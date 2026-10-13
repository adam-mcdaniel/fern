//! Simplifying a module before lowering it.

use super::interproc::{self, Effects};
use super::{cfg, inline, loops, memory, range, BinOp, Block, Function, Module, Node, Target, Terminator, UnOp, Value};
use std::collections::{HashMap, HashSet};

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
    for _ in 0..8 {
        let mut changed = false;
        let effects = interproc::effects(module);
        for f in &mut module.funcs {
            changed |= inline::tail_calls(f);
            changed |= simplify(f, &effects);
        }
        changed |= inline::inline(module);
        changed |= interproc::specialize(module);
        changed |= interproc::dead_arguments(module);
        let effects = interproc::effects(module);
        for f in &mut module.funcs {
            changed |= simplify(f, &effects);
        }
        changed |= apply_ranges(module);
        if !changed {
            break;
        }
    }
    let effects = interproc::effects(module);
    for f in &mut module.funcs {
        simplify(f, &effects);
        f.rebuild_dedup();
    }
}

/// The function-level passes, until they stop changing anything.
pub(super) fn simplify(f: &mut Function, effects: &HashMap<String, Effects>) -> bool {
    let mut any = false;
    // a loop of blocks that only jump to each other would keep threading
    for _ in 0..100 {
        let changed = resimplify(f)
            | gvn(f)
            | trivial_params(f)
            | memory::optimize(f, effects)
            | pure_calls(f, effects)
            | licm(f)
            | loops::strength_reduce(f)
            | loops::unroll(f)
            | fold_branches(f)
            | thread_jumps(f)
            | merge_blocks(f)
            | merge_tails(f)
            | dead_params(f)
            | devirtualize(f);
        if !changed {
            break;
        }
        any = true;
    }
    any
}

fn resolve(map: &HashMap<Value, Value>, mut v: Value) -> Value {
    for _ in 0..map.len() {
        match map.get(&v) {
            Some(&to) => v = to,
            None => break,
        }
    }
    v
}

/// Replaces every use of each key of `map` with its value.
pub(super) fn replace_uses(f: &mut Function, map: &HashMap<Value, Value>) {
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
    let mut map = HashMap::new();
    let mut seen: HashMap<(Option<Block>, Node), Value> = HashMap::new();
    let current = f.current;
    for i in 0..f.values.len() {
        let v = Value(i as u32);
        let block = f.values[i].block;
        let mut node = f.values[i].node.clone();
        node.map_operands(|v| resolve(&map, v));
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
    replace_uses(f, &map);
    f.rebuild_dedup();
    !map.is_empty()
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

/// Whether anything outside block `b`, among `reachable`, uses `b`'s values.
fn escapes(f: &Function, reachable: &[Block], b: Block) -> bool {
    let in_b = |v: Value| f.values[v.index()].block == Some(b);
    let live: Vec<bool> = {
        let mut live = vec![false; f.blocks.len()];
        reachable.iter().for_each(|r| live[r.index()] = true);
        live
    };
    f.values.iter().any(|data| {
        data.block.is_some_and(|x| x != b && live[x.index()]) && data.node.operands().into_iter().any(in_b)
    }) || reachable
        .iter()
        .filter(|&&x| x != b)
        .any(|&x| f.blocks[x.index()].term.iter().flat_map(|t| t.operands()).any(in_b))
}

/// Sends jumps to a block that does nothing but jump on straight to where it
/// jumps, one block at a time.
fn thread_jumps(f: &mut Function) -> bool {
    let rpo = cfg::reverse_postorder(f);
    let preds = cfg::predecessors(f, &rpo);
    for &b in &rpo[1..] {
        let block = &f.blocks[b.index()];
        let Some(Terminator::Jump(next)) = &block.term else { continue };
        if !block.effects.is_empty() || next.block == b {
            continue;
        }
        // the jump's arguments must be the block's parameters or values from
        // blocks that dominate it, which also dominate its predecessors
        let params = block.params.clone();
        let next = next.clone();
        let own = |v: Value| f.values[v.index()].block == Some(b) && !params.contains(&v);
        if next.args.iter().any(|&a| own(a)) || escapes(f, &rpo, b) {
            continue;
        }
        let mut sources = preds[b.index()].clone();
        sources.dedup();
        for p in sources {
            let term = f.blocks[p.index()].term.as_mut().unwrap();
            term.map_targets(|t| {
                if t.block != b {
                    return t.clone();
                }
                let args = next
                    .args
                    .iter()
                    .map(|a| match params.iter().position(|p| p == a) {
                        Some(i) => t.args[i],
                        None => *a,
                    })
                    .collect();
                Target { block: next.block, args }
            });
        }
        return true;
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
    let mut groups: HashMap<&Node, Vec<Value>> = HashMap::new();
    for (i, data) in f.values.iter().enumerate() {
        if let (Node::Unary(..) | Node::Binary(..), Some(b)) = (&data.node, data.block) {
            if idom[b.index()].is_some() {
                groups.entry(&data.node).or_default().push(Value(i as u32));
            }
        }
    }
    let block = |v: Value| f.values[v.index()].block.unwrap();
    let mut map = HashMap::new();
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
    replace_uses(f, &map);
    !map.is_empty()
}

/// Replaces a block parameter that receives the same value from every jump
/// (other than its own value, around a loop) with that value.
fn trivial_params(f: &mut Function) -> bool {
    let rpo = cfg::reverse_postorder(f);
    let mut incoming: HashMap<Value, HashSet<Value>> = HashMap::new();
    for &b in &rpo {
        for target in f.blocks[b.index()].term.iter().flat_map(|t| t.targets()) {
            for (&p, &a) in f.blocks[target.block.index()].params.iter().zip(&target.args) {
                if a != p {
                    incoming.entry(p).or_default().insert(a);
                }
            }
        }
    }
    let mut map = HashMap::new();
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
        let mut hoisted = HashSet::new();
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
pub(super) fn preheader(f: &mut Function, header: Block, body: &HashSet<Block>, preds: &[Vec<Block>]) -> Block {
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
    let mut map = HashMap::new();
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
    let mut map = HashMap::new();
    let mut removed = HashSet::new();
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
            && !escapes(f, &rpo, b)
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
