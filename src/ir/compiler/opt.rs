//! Simplifying a module before lowering it.

use super::interproc::{self, Effects};
use super::passes::Passes;
use super::{cfg, inline, loops, memory, range, BinOp, Block, Function, Module, Node, Target, Terminator, UnOp, Value};
use crate::asm::fx::{HashMap, HashSet};

/// Optimizes a module. Repeats, until nothing changes:
///
/// - turning tail calls into loops, and inlining small functions and functions
///   called only once,
/// - folding and simplifying nodes, and merging nodes that compute the same
///   thing, within a block or from a block that dominates the other,
/// - hoisting work that doesn't change between iterations out of loops, and
///   cheap work even from blocks that only run on some iterations,
/// - dropping block parameters that always receive the same value,
/// - forwarding stored values to loads, and dropping loads and stores whose
///   results are never seen,
/// - range analysis: replacing values with the constant they're known to be,
///   folding branches that only go one way, and using cheaper ops where the
///   ranges allow,
/// - turning branches on constants into jumps, sending jumps to blocks that
///   only jump on straight to their target, and merging blocks into their
///   only predecessor.
///
/// Blocks this leaves unreachable stay in their function, but are never
/// lowered, and neither are functions nothing calls any more.
pub fn optimize(module: &mut Module) {
    optimize_with(module, &Passes::all());
}

/// `optimize`, with only the passes `passes` has on (by their names in
/// `PASSES`, which are also what `-vv` reports their times under).
pub fn optimize_with(module: &mut Module, passes: &Passes) {
    use crate::asm::log::{self, DEBUG, INFO, PASSES};
    let mut phase = log::phase(INFO, "optimize");
    let size = |m: &Module| m.funcs.iter().map(|f| f.values.len()).sum::<usize>();
    crate::log!(DEBUG, "{} functions, {} values", module.funcs.len(), size(module));
    let time = |name: &'static str, f: &mut dyn FnMut() -> bool| passes.on(name) && PASSES.with(|t| t.borrow_mut().time(name, f));
    let mut done = Simplified::default();
    for round in 1..=8 {
        let mut r = log::phase(DEBUG, format!("round {round}"));
        let mut changed = false;
        let effects = interproc::effects(module);
        changed |= time("tail-calls", &mut || module.funcs.iter_mut().fold(false, |c, f| inline::tail_calls(f) | c));
        changed |= done.simplify(module, &effects, passes);
        changed |= time("inline", &mut || inline::inline(module));
        changed |= time("specialize", &mut || interproc::specialize(module));
        changed |= time("dead-arguments", &mut || interproc::dead_arguments(module));
        let effects = interproc::effects(module);
        changed |= done.simplify(module, &effects, passes);
        changed |= time("ranges", &mut || apply_ranges(module));
        r.done(format!("{} functions, {} values{}", module.funcs.len(), size(module), if changed { "" } else { ", no change: done" }));
        if !changed {
            break;
        }
    }
    let effects = interproc::effects(module);
    done.simplify(module, &effects, passes);
    for f in &mut module.funcs {
        f.rebuild_dedup();
    }
    PASSES.with(|t| {
        t.borrow().report("the optimizer's passes");
        *t.borrow_mut() = log::Tally::default();
    });
    phase.done(format!("{} functions, {} values", module.funcs.len(), size(module)));
}

/// Which functions are already as simple as `simplify` makes them, so that
/// a round of `optimize` can skip them: each one's fingerprint when it was
/// last simplified, which still holds while the function is the same and
/// so are the effects of what it calls.
#[derive(Default)]
struct Simplified {
    effects: HashMap<String, Effects>,
    prints: HashMap<String, u64>,
}

impl Simplified {
    fn simplify(&mut self, module: &mut Module, effects: &HashMap<String, Effects>, passes: &Passes) -> bool {
        if *effects != self.effects {
            self.effects = effects.clone();
            self.prints.clear();
        }
        // (each function on its own: on as many threads as there are cores,
        // each taking the next function there is to do)
        let todo: Vec<std::sync::Mutex<&mut Function>> = module.funcs.iter_mut().filter(|f| self.prints.get(&f.name) != Some(&fingerprint(f))).map(std::sync::Mutex::new).collect();
        let next = std::sync::atomic::AtomicUsize::new(0);
        let threads = std::thread::available_parallelism().map_or(1, |n| n.get()).min(todo.len().max(1));
        let done: Vec<Vec<(String, u64, bool)>> = std::thread::scope(|scope| {
            let workers: Vec<_> = (0..threads)
                .map(|_| {
                    scope.spawn(|| {
                        let mut out = vec![];
                        loop {
                            let i = next.fetch_add(1, std::sync::atomic::Ordering::Relaxed);
                            let Some(slot) = todo.get(i) else { break };
                            let mut f = slot.lock().unwrap();
                            let start = std::time::Instant::now();
                            let before = f.values.len();
                            let changed = simplify_with(&mut f, effects, passes);
                            crate::log!(crate::asm::log::TRACE, "simplify {}: {} values to {}, {}", f.name, before, f.values.len(), crate::asm::log::show(start.elapsed()));
                            out.push((f.name.clone(), fingerprint(&f), changed));
                        }
                        out
                    })
                })
                .collect();
            workers.into_iter().map(|w| w.join().unwrap()).collect()
        });
        let mut changed = false;
        for (name, print, c) in done.into_iter().flatten() {
            changed |= c;
            self.prints.insert(name, print);
        }
        changed
    }
}

/// A hash of everything in a function, to tell whether it's changed.
fn fingerprint(f: &Function) -> u64 {
    use std::hash::{Hash, Hasher};
    let mut h = crate::asm::fx::FxHasher::default();
    (&f.values, &f.blocks).hash(&mut h);
    h.finish()
}

/// The function-level passes, until they stop changing anything.
pub(in crate::ir) fn simplify(f: &mut Function, effects: &HashMap<String, Effects>) -> bool {
    simplify_with(f, effects, &Passes::all())
}

/// `simplify`, with only the passes `passes` has on.
fn simplify_with(f: &mut Function, effects: &HashMap<String, Effects>, passes: &Passes) -> bool {
    let mut any = false;
    // a loop of blocks that only jump to each other would keep threading
    for _ in 0..100 {
        let changed = crate::asm::log::PASSES.with(|t| {
            let mut t = t.borrow_mut();
            let mut time = |name: &'static str, pass: &mut dyn FnMut() -> bool| passes.on(name) && t.time(name, pass);
            time("simplify", &mut || resimplify(f))
                | time("gvn", &mut || gvn(f))
                | time("trivial-params", &mut || trivial_params(f))
                | time("variables", &mut || memory::promote(f))
                | time("memory", &mut || memory::optimize(f, effects))
                | time("pure-calls", &mut || pure_calls(f, effects))
                | time("licm", &mut || licm(f))
                | time("strength-reduce", &mut || loops::strength_reduce(f))
                | time("unroll", &mut || loops::unroll(f))
                | time("fold-branches", &mut || fold_branches(f))
                | time("thread-jumps", &mut || exhaust(f, thread_jumps))
                | time("merge-blocks", &mut || exhaust(f, merge_blocks))
                | time("merge-tails", &mut || exhaust(f, merge_tails))
                | time("dead-params", &mut || dead_params(f))
                | time("devirtualize", &mut || devirtualize(f))
        });
        if !changed {
            break;
        }
        any = true;
    }
    any
}

/// A pass that makes one change at a time, run until it has made them all
/// (so a big function doesn't take a round of every pass for each). At
/// most as many as there are blocks: a loop of blocks that only jump to
/// each other would keep threading.
fn exhaust(f: &mut Function, pass: fn(&mut Function) -> bool) -> bool {
    let mut any = false;
    for _ in 0..f.blocks.len() + 1 {
        if !pass(f) {
            break;
        }
        any = true;
    }
    any
}

pub(in crate::ir) fn resolve(map: &HashMap<Value, Value>, mut v: Value) -> Value {
    for _ in 0..map.len() {
        match map.get(&v) {
            Some(&to) => v = to,
            None => break,
        }
    }
    v
}

/// Whether replacing the keys of `map` changes anything: whether something
/// uses one. (Dead values stay in a function, and one can keep simplifying
/// to another, or matching another, without that changing anything; saying
/// it did kept `simplify` going round to its limit.)
fn changes(f: &Function, map: &HashMap<Value, Value>) -> bool {
    if map.is_empty() {
        return false;
    }
    let uses = |ops: &[Value]| ops.iter().any(|o| map.contains_key(o));
    f.values.iter().any(|d| d.block.is_some() && uses(&d.node.operands()))
        || f.blocks.iter().any(|b| b.term.as_ref().is_some_and(|t| uses(&t.operands())))
}

/// Replaces every use of each key of `map` with its value.
pub(in crate::ir) fn replace_uses(f: &mut Function, map: &HashMap<Value, Value>) {
    if map.is_empty() {
        return;
    }
    for data in &mut f.values {
        data.node.map_operands(|v| resolve(map, v));
    }
    for block in &mut f.blocks {
        if let Some(t) = &mut block.term {
            t.map_operands(|v| resolve(map, v));
        }
    }
}

fn resimplify(f: &mut Function) -> bool {
    let mut map = HashMap::default();
    let mut seen: HashMap<(Option<Block>, Node), Value> = HashMap::default();
    let current = f.current;
    // (whether a node in a block got operands that were replaced as it went)
    let mut rewrote = false;
    for i in 0..f.values.len() {
        let v = Value(i as u32);
        let block = f.values[i].block;
        let mut node = f.values[i].node.clone();
        node.map_operands(|v| resolve(&map, v));
        rewrote |= block.is_some() && node != f.values[i].node;
        let simplified = match (&node, block) {
            (Node::Unary(op, a), Some(b)) => {
                f.current = b;
                f.simplify_unary(*op, *a)
            }
            (Node::Binary(op, a, x), Some(b)) => {
                f.current = b;
                f.simplify_binary(*op, *a, *x)
            }
            _ => Err(node),
        };
        match simplified {
            Ok(to) => {
                if to != v {
                    map.insert(v, to);
                }
            }
            Err(node) => {
                if matches!(node, Node::Unary(..) | Node::Binary(..)) {
                    match seen.get(&(block, node.clone())) {
                        Some(&same) => {
                            map.insert(v, same);
                        }
                        None => {
                            seen.insert((block, node.clone()), v);
                        }
                    }
                }
                f.values[i].node = node;
            }
        }
    }
    f.current = current;
    let changed = rewrote || changes(f, &map);
    replace_uses(f, &map);
    f.rebuild_dedup();
    changed
}

fn low_mask(bits: u32) -> i64 {
    if bits == 64 { -1 } else { (1 << bits) - 1 }
}

fn fold_branches(f: &mut Function) -> bool {
    let mut changed = false;
    for b in 0..f.blocks.len() {
        let new = match &f.blocks[b].term {
            Some(Terminator::Branch(c, t, e)) => match f.const_value(*c) {
                Some(0) => Some(Terminator::Jump(e.clone())),
                // a constant is nonzero on every target width only if its bits
                // that fit in the narrowest one are
                Some(k) if k & low_mask(f.min_width) != 0 => Some(Terminator::Jump(t.clone())),
                _ if t == e => Some(Terminator::Jump(t.clone())),
                _ => None,
            },
            _ => None,
        };
        if let Some(term) = new {
            f.blocks[b].term = Some(term);
            changed = true;
        }
    }
    changed
}

/// For each block, whether anything outside it, among `reachable`, uses its
/// values. (All at once, in one look at every value: asking block by block
/// was quadratic.)
fn escaping(f: &Function, reachable: &[Block]) -> Vec<bool> {
    let mut live = vec![false; f.blocks.len()];
    reachable.iter().for_each(|r| live[r.index()] = true);
    let mut escapes = vec![false; f.blocks.len()];
    let mut uses = |x: Block, o: Value| {
        if let Some(b) = f.values[o.index()].block {
            if b != x {
                escapes[b.index()] = true;
            }
        }
    };
    for data in &f.values {
        if let Some(x) = data.block.filter(|x| live[x.index()]) {
            data.node.operands().into_iter().for_each(|o| uses(x, o));
        }
    }
    for &x in reachable {
        f.blocks[x.index()].term.iter().flat_map(|t| t.operands()).for_each(|o| uses(x, o));
    }
    escapes
}

/// Sends jumps to a block that does nothing but jump on straight to where it
/// jumps, one block at a time; and the ways into a block that does nothing
/// but branch on one of its parameters, where they give it a constant,
/// straight to the side that takes (as `&&` and `||` make: a block that
/// gets 0 from one side and a comparison from the other, and branches).
fn thread_jumps(f: &mut Function) -> bool {
    let rpo = cfg::reverse_postorder(f);
    let preds = cfg::predecessors(f, &rpo);
    let escapes = escaping(f, &rpo);
    for &b in &rpo[1..] {
        let block = &f.blocks[b.index()];
        if !block.effects.is_empty() || escapes[b.index()] {
            continue;
        }
        // where it goes must be given its parameters or values from blocks
        // that dominate it, which also dominate its predecessors
        let params = block.params.clone();
        let own = |v: Value| f.values[v.index()].block == Some(b) && !params.contains(&v);
        // (with an edge into it, where it goes on to from there)
        let on = |t: &Target, next: &Target| {
            let args = next
                .args
                .iter()
                .map(|a| match params.iter().position(|p| p == a) {
                    Some(i) => t.args[i],
                    None => *a,
                })
                .collect();
            Target { block: next.block, args }
        };
        let mut sources = preds[b.index()].clone();
        sources.dedup();
        match block.term.clone() {
            Some(Terminator::Jump(next)) if next.block != b && !next.args.iter().any(|&a| own(a)) => {
                for p in sources {
                    f.blocks[p.index()].term.as_mut().unwrap().map_targets(|t| if t.block == b { on(t, &next) } else { t.clone() });
                }
                return true;
            }
            Some(Terminator::Branch(c, yes, no)) if yes.block != b && no.block != b && !yes.args.iter().chain(&no.args).any(|&a| own(a)) => {
                let Some(k) = params.iter().position(|&p| p == c) else { continue };
                let mut changed = false;
                for p in sources {
                    let consts: Vec<Option<i64>> = f.blocks[p.index()].term.as_ref().unwrap().targets().iter().map(|t| if t.block == b { f.const_value(t.args[k]) } else { None }).collect();
                    let mut i = 0;
                    f.blocks[p.index()].term.as_mut().unwrap().map_targets(|t| {
                        let known = consts[i];
                        i += 1;
                        match known {
                            Some(x) => {
                                changed = true;
                                on(t, if x != 0 { &yes } else { &no })
                            }
                            None => t.clone(),
                        }
                    });
                }
                if changed {
                    return true;
                }
            }
            _ => {}
        }
    }
    false
}

/// Merges a block into its only predecessor, when that ends by jumping to it.
fn merge_blocks(f: &mut Function) -> bool {
    let rpo = cfg::reverse_postorder(f);
    let preds = cfg::predecessors(f, &rpo);
    for &b in &rpo {
        let Some(Terminator::Jump(next)) = f.blocks[b.index()].term.clone() else { continue };
        let c = next.block;
        if c == b || c == f.entry() || preds[c.index()] != [b] {
            continue;
        }
        // c's parameters become the jump's arguments
        let map: HashMap<Value, Value> =
            f.blocks[c.index()].params.iter().copied().zip(next.args.iter().copied()).collect();
        for data in &mut f.values {
            if data.block == Some(c) {
                data.block = Some(b);
            }
        }
        let effects = std::mem::take(&mut f.blocks[c.index()].effects);
        f.blocks[b.index()].effects.extend(effects);
        f.blocks[b.index()].term = f.blocks[c.index()].term.take();
        f.blocks[c.index()].params.clear();
        replace_uses(f, &map);
        return true;
    }
    false
}

fn block_order(f: &Function, rpo: &[Block]) -> Vec<usize> {
    let mut order = vec![usize::MAX; f.blocks.len()];
    for (i, b) in rpo.iter().enumerate() {
        order[b.index()] = i;
    }
    order
}

/// Global value numbering: a pure node that's the same as one in a block that
/// dominates it is replaced by that one.
fn gvn(f: &mut Function) -> bool {
    let rpo = cfg::reverse_postorder(f);
    let idom = cfg::dominators(f, &rpo);
    let order = block_order(f, &rpo);
    let mut groups: HashMap<&Node, Vec<Value>> = HashMap::default();
    for (i, data) in f.values.iter().enumerate() {
        if let (Node::Unary(..) | Node::Binary(..), Some(b)) = (&data.node, data.block) {
            if idom[b.index()].is_some() {
                groups.entry(&data.node).or_default().push(Value(i as u32));
            }
        }
    }
    let block = |v: Value| f.values[v.index()].block.unwrap();
    let mut map = HashMap::default();
    for (_, mut values) in groups {
        if values.len() < 2 {
            continue;
        }
        values.sort_by_key(|&v| order[block(v).index()]);
        for i in 0..values.len() {
            let v = values[i];
            let same = values[..i]
                .iter()
                .find(|&&w| !map.contains_key(&w) && cfg::dominates(&idom, block(w), block(v)));
            if let Some(&w) = same {
                map.insert(v, w);
            }
        }
    }
    let changed = changes(f, &map);
    replace_uses(f, &map);
    changed
}

/// Replaces a block parameter that receives the same value from every jump
/// (other than its own value, around a loop) with that value.
fn trivial_params(f: &mut Function) -> bool {
    let rpo = cfg::reverse_postorder(f);
    let mut incoming: HashMap<Value, HashSet<Value>> = HashMap::default();
    for &b in &rpo {
        for target in f.blocks[b.index()].term.iter().flat_map(|t| t.targets()) {
            for (&p, &a) in f.blocks[target.block.index()].params.iter().zip(&target.args) {
                if a != p {
                    incoming.entry(p).or_default().insert(a);
                }
            }
        }
    }
    let mut map = HashMap::default();
    for &b in &rpo[1..] {
        for &p in &f.blocks[b.index()].params {
            if let Some(values) = incoming.get(&p) {
                if values.len() == 1 {
                    map.insert(p, *values.iter().next().unwrap());
                }
            }
        }
    }
    replace_uses(f, &map);
    !map.is_empty()
}

/// Hoists pure nodes that don't change between iterations out of loops, into
/// a block that runs just before each loop, one loop at a time. Cheap nodes
/// move even from blocks that only run on some iterations: pure nodes can't
/// fail (even dividing by 0 gives a result), so computing one early is safe,
/// and it then runs at most once per entry to the loop instead of once per
/// iteration. Expensive ones (multiplying, dividing, bitwise operations and
/// comparisons, which are routines) only move from blocks every iteration
/// runs, since a block that rarely runs, like the slow path of an
/// allocator, would otherwise make every entry to the loop pay for them.
fn licm(f: &mut Function) -> bool {
    let rpo = cfg::reverse_postorder(f);
    let preds = cfg::predecessors(f, &rpo);
    let idom = cfg::dominators(f, &rpo);
    for l in cfg::loops(f) {
        let outside = |f: &Function, v: Value| f.values[v.index()].block.is_none_or(|b| !l.body.contains(&b));
        // a block that every iteration runs; work from other blocks only
        // moves if it's cheap, since it then runs even when they wouldn't
        let every_time = |b: Block| l.latches.iter().all(|&latch| cfg::dominates(&idom, b, latch));
        let cheap = |f: &Function, node: &Node| match node {
            Node::Unary(UnOp::Neg | UnOp::Not, _) | Node::Binary(BinOp::Add | BinOp::Sub, ..) => true,
            Node::Binary(BinOp::Index, _, i) => f.const_value(*i).is_some(),
            _ => false,
        };
        let mut hoist = vec![];
        let mut hoisted = HashSet::default();
        loop {
            let before = hoist.len();
            for (i, data) in f.values.iter().enumerate() {
                let v = Value(i as u32);
                if let (Node::Unary(..) | Node::Binary(..), Some(b)) = (&data.node, data.block) {
                    if l.body.contains(&b)
                        && !hoisted.contains(&v)
                        && (every_time(b) || cheap(f, &data.node))
                        && data.node.operands().iter().all(|&o| outside(f, o) || hoisted.contains(&o))
                    {
                        hoist.push(v);
                        hoisted.insert(v);
                    }
                }
            }
            if hoist.len() == before {
                break;
            }
        }
        if hoist.is_empty() {
            continue;
        }
        let pre = preheader(f, l.header, &l.body, &preds);
        for v in hoist {
            f.values[v.index()].block = Some(pre);
        }
        return true;
    }
    false
}

/// The block that runs just before entering the loop at `header`: its only
/// predecessor from outside the loop, if that only jumps to it, or else a new
/// block that every edge from outside goes through.
pub(in crate::ir) fn preheader(f: &mut Function, header: Block, body: &HashSet<Block>, preds: &[Vec<Block>]) -> Block {
    let mut outside: Vec<Block> = preds[header.index()].iter().copied().filter(|p| !body.contains(p)).collect();
    outside.dedup();
    if let [p] = outside[..] {
        if matches!(f.blocks[p.index()].term, Some(Terminator::Jump(_))) {
            return p;
        }
    }
    let pre = f.new_block(f.blocks[header.index()].params.len());
    let params = f.blocks[pre.index()].params.clone();
    f.blocks[pre.index()].term = Some(Terminator::Jump(Target { block: header, args: params }));
    for p in outside {
        f.blocks[p.index()].term.as_mut().unwrap().map_targets(|t| {
            if t.block == header { Target { block: pre, args: t.args.clone() } } else { t.clone() }
        });
    }
    pre
}

/// Uses the results of range analysis on every function.
fn apply_ranges(module: &mut Module) -> bool {
    let analysis = range::analyze(module);
    let mut changed = false;
    for (f, ranges) in module.funcs.iter_mut().zip(&analysis) {
        changed |= use_ranges(f, ranges);
    }
    changed
}

fn use_ranges(f: &mut Function, r: &range::Ranges) -> bool {
    let mut changed = false;
    let live = |b: Option<Block>| b.is_some_and(|b| r.reachable[b.index()]);

    // operands known to be one value where they're used become that constant
    let mut constants = vec![];
    for (i, data) in f.values.iter().enumerate() {
        if live(data.block) {
            for o in data.node.operands() {
                if let Some(k) = r.at(o, data.block.unwrap()).singleton() {
                    if f.const_value(o) != Some(k) {
                        constants.push((Some(i), None, o, k));
                    }
                }
            }
        }
    }
    for (b, block) in f.blocks.iter().enumerate() {
        if r.reachable[b] {
            for o in block.term.iter().flat_map(|t| t.operands()) {
                if let Some(k) = r.at(o, Block(b as u32)).singleton() {
                    if f.const_value(o) != Some(k) {
                        constants.push((None, Some(b), o, k));
                    }
                }
            }
        }
    }
    for (value, block, o, k) in constants {
        let c = f.int(k);
        let swap = |v: Value| if v == o { c } else { v };
        match (value, block) {
            (Some(i), _) => f.values[i].node.map_operands(swap),
            (_, Some(b)) => f.blocks[b].term.as_mut().unwrap().map_operands(swap),
            _ => unreachable!(),
        }
        changed = true;
    }

    // cheaper ops for operands in known ranges
    let mut map = HashMap::default();
    for i in 0..f.values.len() {
        let data = &f.values[i];
        let Some(b) = data.block.filter(|&b| r.reachable[b.index()]) else { continue };
        let new = match data.node {
            Node::Binary(op, a, x) => {
                let (ra, rx) = (r.at(a, b), r.at(x, b));
                let nonnegative = ra.at_least(0) && rx.at_least(0);
                use BinOp::*;
                match op {
                    Div | Rem if ra.at_least(0) && rx.at_least(1) => {
                        Some(Node::Binary(if op == Div { DivU } else { RemU }, a, x))
                    }
                    Shr if ra.at_least(0) => Some(Node::Binary(ShrU, a, x)),
                    LtU | LeU | GtU | GeU if nonnegative => {
                        let signed = match op {
                            LtU => Lt,
                            LeU => Le,
                            GtU => Gt,
                            _ => Ge,
                        };
                        Some(Node::Binary(signed, a, x))
                    }
                    Min | Max => {
                        let (low, high) = match (ra.bounds(), rx.bounds()) {
                            (Some((_, ah)), Some((xl, _))) if ah <= xl => (a, x),
                            (Some((al, _)), Some((_, xh))) if xh <= al => (x, a),
                            _ => continue,
                        };
                        map.insert(Value(i as u32), if op == Min { low } else { high });
                        continue;
                    }
                    _ => None,
                }
            }
            Node::Unary(UnOp::Abs, a) => {
                let ra = r.at(a, b);
                if ra.at_least(0) {
                    map.insert(Value(i as u32), a);
                    continue;
                }
                ra.at_most(0).then_some(Node::Unary(UnOp::Neg, a))
            }
            _ => None,
        };
        if let Some(node) = new {
            f.values[i].node = node;
            changed = true;
        }
    }
    replace_uses(f, &map);
    changed |= !map.is_empty();

    // branches that only go one way
    for b in 0..f.blocks.len() {
        if !r.reachable[b] {
            continue;
        }
        if let Some(Terminator::Branch(c, t, e)) = &f.blocks[b].term {
            let rc = r.at(*c, Block(b as u32));
            let taken = if rc == range::Range::Int(0, 0) {
                Some(e.clone())
            } else if rc.at_least(1) || rc.at_most(-1) {
                Some(t.clone())
            } else {
                None
            };
            if let Some(t) = taken {
                f.blocks[b].term = Some(Terminator::Jump(t));
                changed = true;
            }
        }
    }
    changed
}

/// Calls to functions that are just their result: one whose result nothing
/// uses goes, and one the same as a call that dominates it reuses its result.
fn pure_calls(f: &mut Function, effects: &HashMap<String, Effects>) -> bool {
    let rpo = cfg::reverse_postorder(f);
    let idom = cfg::dominators(f, &rpo);
    let mut used = vec![false; f.values.len()];
    for data in &f.values {
        data.node.operands().into_iter().for_each(|o| used[o.index()] = true);
    }
    for block in &f.blocks {
        block.term.iter().flat_map(|t| t.operands()).for_each(|o| used[o.index()] = true);
    }
    let mut earlier: Vec<(Node, Value, Block)> = vec![];
    let mut map = HashMap::default();
    let mut removed = HashSet::default();
    for &b in &rpo {
        for &e in &f.blocks[b.index()].effects {
            let node = &f.values[e.index()].node;
            let Node::Call(name, _) = node else { continue };
            if !effects.get(name).is_some_and(|e| e.pure()) {
                continue;
            }
            if !used[e.index()] {
                removed.insert(e);
            } else if let Some(&(_, same, _)) =
                earlier.iter().find(|(n, _, at)| n == node && cfg::dominates(&idom, *at, b))
            {
                map.insert(e, same);
                removed.insert(e);
            } else {
                earlier.push((node.clone(), e, b));
            }
        }
    }
    if removed.is_empty() {
        return false;
    }
    replace_uses(f, &map);
    for block in &mut f.blocks {
        block.effects.retain(|e| !removed.contains(e));
    }
    true
}

/// Merges blocks that do exactly the same thing and go to the same place,
/// sending everything that went to one to the other.
fn merge_tails(f: &mut Function) -> bool {
    let rpo = cfg::reverse_postorder(f);
    let escapes = escaping(f, &rpo);
    let mut used = vec![false; f.values.len()];
    for data in &f.values {
        data.node.operands().into_iter().for_each(|o| used[o.index()] = true);
    }
    for block in &f.blocks {
        block.term.iter().flat_map(|t| t.operands()).for_each(|o| used[o.index()] = true);
    }
    let candidate = |b: Block| {
        let block = &f.blocks[b.index()];
        b != f.entry()
            && block.params.is_empty()
            && block.effects.iter().all(|e| !used[e.index()])
            && !escapes[b.index()]
    };
    let same = |a: Block, b: Block| {
        let (x, y) = (&f.blocks[a.index()], &f.blocks[b.index()]);
        x.term == y.term
            && x.effects.len() == y.effects.len()
            && x.effects.iter().zip(&y.effects).all(|(p, q)| f.values[p.index()].node == f.values[q.index()].node)
    };
    for (i, &a) in rpo.iter().enumerate() {
        if !candidate(a) {
            continue;
        }
        if let Some(&b) = rpo[i + 1..].iter().find(|&&b| candidate(b) && same(a, b)) {
            for &p in &rpo {
                if let Some(t) = &mut f.blocks[p.index()].term {
                    t.map_targets(|t| if t.block == b { Target { block: a, args: vec![] } } else { t.clone() });
                }
            }
            return true;
        }
    }
    false
}

/// Removes block parameters nothing needs, and the arguments jumps pass them.
fn dead_params(f: &mut Function) -> bool {
    let rpo = cfg::reverse_postorder(f);
    let needed = super::sched::needed(f, &rpo);
    let mut changed = false;
    for &b in &rpo[1..] {
        let dead: Vec<usize> =
            f.blocks[b.index()].params.iter().enumerate().filter(|(_, p)| !needed[p.index()]).map(|(i, _)| i).collect();
        if dead.is_empty() {
            continue;
        }
        let keep = |list: Vec<Value>| list.into_iter().enumerate().filter(|(i, _)| !dead.contains(i)).map(|(_, v)| v).collect();
        let params = std::mem::take(&mut f.blocks[b.index()].params);
        f.blocks[b.index()].params = keep(params);
        for (i, p) in f.blocks[b.index()].params.clone().into_iter().enumerate() {
            f.values[p.index()].node = Node::Param(b, i);
        }
        for block in &mut f.blocks {
            if let Some(t) = &mut block.term {
                t.map_targets(|t| {
                    if t.block == b { Target { block: b, args: keep(t.args.clone()) } } else { t.clone() }
                });
            }
        }
        changed = true;
    }
    changed
}

/// Turns indirect calls of a known function's address into direct calls,
/// which can then be inlined and optimized like any other.
fn devirtualize(f: &mut Function) -> bool {
    let mut changed = false;
    for i in 0..f.values.len() {
        if let Node::CallIndirect(g, args) = &f.values[i].node {
            if let Node::FuncAddr(name) = &f.values[g.index()].node {
                f.values[i].node = Node::Call(name.clone(), args.clone());
                changed = true;
            }
        }
    }
    changed
}
