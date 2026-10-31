//! Removing memory accesses: loads whose value is already known, stores that
//! are overwritten before anything could read them, and stores to
//! allocations nothing reads.
//!
//! What each cell is known to hold flows forward through the function: at a
//! block with several ways in (including a loop header), a cell is known if
//! every way in agrees on its value. If they know different values for a cell
//! the block then loads, the block gets a new parameter for it, and every
//! jump to it passes the value it knows.
//!
//! Before that, a variable (an alloca whose address never escapes, only
//! loaded and stored, a whole cell at a time, at offsets known when
//! compiling) becomes a value outright (`promote`): what it holds is a value
//! in each block, a parameter where ways in meet and it may be read before
//! it's set, which the knowing above can't do for a variable a loop inside a
//! loop sets (each loop's header would wait on the other's knowing it).
//!
//! Addresses are compared by where they point: an allocation (or an unknown
//! pointer) plus a constant offset, when the offset is constant. Different
//! allocations never overlap, and an allocation whose address never escapes
//! (it's only ever used to load, store or index) can't be reached through any
//! other pointer, or by a call. An address `index a, x + 1`, past a check
//! that `x <u y`, isn't `a` itself (see `apart`): storing into an array
//! doesn't change its length at the start.
//!
//! A fixed load (`Node::Fixed`, of a cell that never changes once anything
//! can read it) is the same as one before it, whatever comes between, and
//! comes out of loops whenever its address is had before them.

use super::interproc::{self, Effects};
use super::opt::{preheader, replace_uses};
use super::{cfg, BinOp, Block, Function, Node, Terminator, Value};
use crate::asm::fx::{HashMap, HashSet};

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
enum Root {
    /// An alloca or heap allocation.
    Allocation(Value),
    /// The global cells, which nothing else overlaps; the offset is the
    /// global's number.
    Globals,
    /// A pointer from somewhere else.
    Unknown(Value),
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
enum Offset {
    Const(i64),
    /// Not constant, so known only as the address value itself.
    At(Value),
}

/// Where an address points: a root plus an offset. Two places are the same
/// cell if they're equal, and may be if they share a root.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
struct Place {
    root: Root,
    offset: Offset,
}

fn place(f: &Function, addr: Value) -> Place {
    match &f.values[addr.index()].node {
        Node::Alloca(_) | Node::HeapAlloc(_) | Node::GcAlloc(..) => Place { root: Root::Allocation(addr), offset: Offset::Const(0) },
        Node::GlobalAddr(i) => Place { root: Root::Globals, offset: Offset::Const(*i as i64) },
        Node::Binary(BinOp::Index, base, i) => {
            let p = place(f, *base);
            let offset = match (p.offset, f.const_value(*i)) {
                (Offset::Const(o), Some(k)) => Offset::Const(o + k),
                _ => Offset::At(addr),
            };
            Place { root: p.root, offset }
        }
        _ => Place { root: Root::Unknown(addr), offset: Offset::Const(0) },
    }
}

/// The values still used: the effects in blocks `live`, what their
/// terminators use, and what those use, all the way down. (A value nothing
/// uses any more still names its block, so its block being live doesn't make
/// it so.)
fn live_values(f: &Function, live: &[Block]) -> Vec<bool> {
    let mut used = vec![false; f.values.len()];
    let mut work = vec![];
    for &b in live {
        let block = &f.blocks[b.index()];
        work.extend(block.effects.iter().copied());
        work.extend(block.params.iter().copied());
        if let Some(t) = &block.term {
            work.extend(t.operands());
        }
    }
    while let Some(v) = work.pop() {
        if !std::mem::replace(&mut used[v.index()], true) {
            work.extend(f.values[v.index()].node.operands());
        }
    }
    used
}

/// The allocations whose address is used for anything but loading, storing
/// or indexing, since another pointer could then reach them.
pub(in crate::ir) fn escaping(f: &Function, live: &[Block]) -> HashSet<Value> {
    let mut escaped = HashSet::default();
    let mut escape = |f: &Function, v: Value| {
        if let Root::Allocation(a) = place(f, v).root {
            escaped.insert(a);
        }
    };
    let used = live_values(f, live);
    for (i, data) in f.values.iter().enumerate() {
        if !used[i] {
            continue;
        }
        match &data.node {
            Node::Load(_) | Node::Fixed(_) => {}
            Node::Store(_, v) => escape(f, *v),
            Node::Binary(BinOp::Index, _, i) => escape(f, *i),
            node => node.operands().into_iter().for_each(|o| escape(f, o)),
        }
    }
    for &b in live {
        if let Some(t) = &f.blocks[b.index()].term {
            for o in t.operands() {
                escape(f, o);
            }
        }
    }
    escaped
}

/// Whether `addr` points into an allocation only this function can reach.
pub(in crate::ir) fn private_alloca(f: &Function, addr: Value, escaped: &HashSet<Value>) -> bool {
    matches!(place(f, addr).root, Root::Allocation(a) if !escaped.contains(&a))
}

/// The name a call's effects are listed under: the callee's, or the empty
/// name for an indirect call.
fn callee(node: &Node) -> &str {
    match node {
        Node::Call(name, _) => name,
        // nothing's known about an external function, so it can do anything
        Node::CallExtern(..) => "\0extern",
        _ => "",
    }
}

/// What a call to `name` can do.
fn call_effects(effects: &HashMap<String, Effects>, name: &str) -> Effects {
    effects.get(name).copied().unwrap_or(Effects::any())
}

/// What tells two places apart, in a function: which of its allocations
/// others can reach, and the addresses known not to be a certain cell of
/// their root (by its offset).
struct Aliasing {
    escaped: HashSet<Value>,
    apart: HashMap<Value, i64>,
}

impl Aliasing {
    fn new(f: &Function, rpo: &[Block], effects: &HashMap<String, Effects>) -> Aliasing {
        Aliasing { escaped: escaping(f, rpo), apart: apart(f, rpo, effects) }
    }

    fn may_alias(&self, a: Place, b: Place) -> bool {
        match (a.root, b.root) {
            (Root::Allocation(x), Root::Allocation(y)) if x != y => false,
            (Root::Globals, Root::Allocation(_)) | (Root::Allocation(_), Root::Globals) => false,
            (Root::Allocation(x), Root::Unknown(_)) | (Root::Unknown(_), Root::Allocation(x)) => self.escaped.contains(&x),
            _ if a.root == b.root => match (a.offset, b.offset) {
                (Offset::Const(x), Offset::Const(y)) => x == y,
                (Offset::Const(k), Offset::At(v)) | (Offset::At(v), Offset::Const(k)) => self.apart.get(&v) != Some(&k),
                _ => true,
            },
            _ => true,
        }
    }

    /// Whether a call can touch memory at `p`.
    fn reaches(&self, p: Place) -> bool {
        !matches!(p.root, Root::Allocation(a) if !self.escaped.contains(&a))
    }
}

/// The addresses `index base, x + 1` where `x <u y` is known (it's past a
/// branch on that): `x` isn't the biggest number there is, so `x + 1` isn't
/// 0, whatever the width, and the address isn't `base` itself. (So storing
/// into an array, past the check of the index against the length at its
/// start, doesn't change the length.) Each with the offset of `base`.
///
/// A block that never goes on (it aborts, or calls a function that never
/// returns: see `interproc::stops`) doesn't count as a way in to where it
/// jumps, so a check whose failing side stops is known past the join.
fn apart(f: &Function, rpo: &[Block], effects: &HashMap<String, Effects>) -> HashMap<Value, i64> {
    let stopping: HashSet<Block> = rpo.iter().copied().filter(|b| f.blocks[b.index()].effects.iter().any(|&e| interproc::stops(&f.values[e.index()].node, effects))).collect();
    // each block's ways in, but from blocks that stop
    let mut preds = cfg::predecessors(f, rpo);
    for p in &mut preds {
        p.retain(|b| !stopping.contains(b));
        p.dedup();
    }
    // where each `x` is less than something, unsigned: the blocks only an
    // edge that says so leads to
    let mut below: HashMap<Block, Vec<Value>> = HashMap::default();
    for &b in rpo {
        let Some(Terminator::Branch(c, yes, no)) = &f.blocks[b.index()].term else { continue };
        if yes.block == no.block || stopping.contains(&b) {
            continue;
        }
        let (x, edge) = match f.values[c.index()].node {
            Node::Binary(BinOp::LtU, x, _) | Node::Binary(BinOp::GtU, _, x) => (x, yes.block),
            Node::Binary(BinOp::GeU, x, _) | Node::Binary(BinOp::LeU, _, x) => (x, no.block),
            _ => continue,
        };
        if preds[edge.index()] == [b] {
            below.entry(edge).or_default().push(x);
        }
    }
    if below.is_empty() {
        return HashMap::default();
    }
    let idom = cfg::dominators(f, rpo);
    // whether `x <u y` for some `y` wherever `b` runs: up from `b`, to the
    // only block that goes on to it, or else to its dominator, there's an
    // edge that says so
    let known_below = |x: Value, mut b: Block| {
        for _ in 0..f.blocks.len() {
            if below.get(&b).is_some_and(|xs| xs.contains(&x)) {
                return true;
            }
            b = match (&preds[b.index()][..], idom[b.index()]) {
                ([p], _) => *p,
                (_, Some(up)) if up != b => up,
                _ => return false,
            };
        }
        false
    };
    let mut out = HashMap::default();
    for (i, data) in f.values.iter().enumerate() {
        let Node::Binary(BinOp::Index, base, n) = data.node else { continue };
        let Offset::Const(k) = place(f, base).offset else { continue };
        let (Node::Binary(BinOp::Add, a, b), Some(at)) = (&f.values[n.index()].node, f.values[n.index()].block) else { continue };
        let plus_one = |x: Value, one: Value| f.const_value(one) == Some(1) && known_below(x, at);
        if plus_one(*a, *b) || plus_one(*b, *a) {
            out.insert(Value(i as u32), k);
        }
    }
    out
}

type Known = HashMap<Place, Value>;

/// What block `b` knows on entry, from what its predecessors know at their
/// ends. A predecessor not yet analyzed (around a loop) doesn't limit it, so
/// the analysis starts optimistic and only drops facts.
fn known_on_entry(f: &Function, b: Block, preds: &[Vec<Block>], at_end: &[Option<Known>]) -> Known {
    if b == f.entry() {
        return Known::default();
    }
    // each analyzed edge in, with what its source knows and passes
    let mut sources = preds[b.index()].clone();
    sources.dedup();
    let edges: Vec<(&Known, &Vec<Value>)> = sources
        .iter()
        .filter_map(|q| at_end[q.index()].as_ref().map(|known| (q, known)))
        .flat_map(|(q, known)| {
            f.blocks[q.index()].term.iter().flat_map(|t| t.targets()).filter(|t| t.block == b).map(move |t| (known, &t.args))
        })
        .collect();
    let Some(&(first, _)) = edges.first() else { return Known::default() };
    let mut known = first.clone();
    known.retain(|place, v| edges.iter().all(|(theirs, _)| theirs.get(place) == Some(v)));
    // a parameter that every edge passes the cell's contents to holds them
    for (i, &param) in f.blocks[b.index()].params.iter().enumerate() {
        for (&place, _) in first {
            if !known.contains_key(&place)
                && edges.iter().all(|(theirs, args)| theirs.get(&place) == args.get(i))
            {
                known.insert(place, param);
            }
        }
    }
    known
}

/// What happens to memory in block `b`, starting from `known`: the loads
/// whose value is already known (with that value), the stores overwritten
/// before anything reads them, and what's known at the end.
fn scan(
    f: &Function,
    b: Block,
    mut known: Known,
    aliasing: &Aliasing,
    effects: &HashMap<String, Effects>,
) -> (Vec<(Value, Value)>, Vec<Value>, Known) {
    let mut forwarded = vec![];
    let mut overwritten = vec![];
    // stores in this block that nothing has read since
    let mut unread: HashMap<Place, Value> = HashMap::default();
    for &e in &f.blocks[b.index()].effects {
        match f.values[e.index()].node {
            Node::Load(a) | Node::Fixed(a) => {
                let p = place(f, a);
                match known.get(&p) {
                    Some(&v) => forwarded.push((e, v)),
                    None => {
                        known.insert(p, e);
                    }
                }
                unread.retain(|q, _| !aliasing.may_alias(*q, p));
            }
            Node::Store(a, v) => {
                let p = place(f, a);
                if let Some(earlier) = unread.insert(p, e) {
                    overwritten.push(earlier);
                }
                known.retain(|q, _| !aliasing.may_alias(*q, p));
                unread.retain(|q, _| *q == p || !aliasing.may_alias(*q, p));
                known.insert(p, v);
            }
            Node::Call(..) | Node::CallIndirect(..) | Node::CallExtern(..) => {
                let call = call_effects(effects, callee(&f.values[e.index()].node));
                if call.writes {
                    known.retain(|q, _| !aliasing.reaches(*q));
                }
                if call.reads {
                    unread.retain(|q, _| !aliasing.reaches(*q));
                }
            }
            _ => {}
        }
    }
    (forwarded, overwritten, known)
}

/// Whether block `b` loads `p` before anything could change it, or a block
/// that only `b` leads to does, and so would know what `b` knows.
fn loads_first(
    f: &Function,
    b: Block,
    p: Place,
    aliasing: &Aliasing,
    preds: &[Vec<Block>],
    effects: &HashMap<String, Effects>,
) -> bool {
    for &e in &f.blocks[b.index()].effects {
        match &f.values[e.index()].node {
            Node::Load(a) | Node::Fixed(a) if place(f, *a) == p => return true,
            Node::Store(a, _) if aliasing.may_alias(place(f, *a), p) => return false,
            node @ (Node::Call(..) | Node::CallIndirect(..) | Node::CallExtern(..))
                if call_effects(effects, callee(node)).writes && aliasing.reaches(p) =>
            {
                return false;
            }
            _ => {}
        }
    }
    cfg::successors(f, b)
        .into_iter()
        .any(|s| s != b && preds[s.index()] == [b] && loads_first(f, s, p, aliasing, preds, effects))
}

pub(in crate::ir) fn optimize(f: &mut Function, effects: &HashMap<String, Effects>) -> bool {
    known_values(f, effects) | fixed_loads(f)
}

/// Each fixed load that one of the same cell comes before, wherever it
/// runs (in a block that dominates its own), replaced by that one: what's
/// there never changes, whatever's stored or called in between.
fn fixed_loads(f: &mut Function) -> bool {
    let rpo = cfg::reverse_postorder(f);
    let idom = cfg::dominators(f, &rpo);
    let mut seen: HashMap<Place, Vec<Value>> = HashMap::default();
    let mut map = HashMap::default();
    for &b in &rpo {
        for &e in &f.blocks[b.index()].effects {
            let Node::Fixed(a) = f.values[e.index()].node else { continue };
            let p = place(f, a);
            let earlier = seen.entry(p).or_default();
            match earlier.iter().find(|&&x| cfg::dominates(&idom, f.values[x.index()].block.unwrap(), b)) {
                Some(&x) => {
                    map.insert(e, x);
                }
                None => earlier.push(e),
            }
        }
    }
    if map.is_empty() {
        return false;
    }
    replace_uses(f, &map);
    for block in &mut f.blocks {
        block.effects.retain(|e| !map.contains_key(e));
    }
    true
}

/// Variables as values (see the module): each cell of each alloca that only
/// loads and stores at known offsets reach, whose address never escapes.
pub(in crate::ir) fn promote(f: &mut Function) -> bool {
    let rpo = cfg::reverse_postorder(f);
    let escaped = escaping(f, &rpo);
    // the cells: (alloca, offset), of allocas only ever reached that way
    let mut ok: HashMap<Value, bool> = HashMap::default();
    let effects: Vec<Value> = rpo.iter().flat_map(|b| f.blocks[b.index()].effects.clone()).collect();
    for &e in &effects {
        if let Node::Alloca(_) = f.values[e.index()].node {
            ok.entry(e).or_insert(!escaped.contains(&e));
        }
    }
    let cell_of = |f: &Function, addr: Value| match place(f, addr) {
        Place { root: Root::Allocation(a), offset: Offset::Const(k) } if matches!(f.values[a.index()].node, Node::Alloca(_)) => Some((a, k)),
        _ => None,
    };
    for &e in &effects {
        if let Node::Load(a) | Node::Fixed(a) | Node::Store(a, _) = f.values[e.index()].node {
            if let Place { root: Root::Allocation(x), offset: Offset::At(_) } = place(f, a) {
                ok.insert(x, false);
            }
        }
    }
    let cells: Vec<(Value, i64)> = {
        let mut seen = HashSet::default();
        let mut out = vec![];
        for &e in &effects {
            if let Node::Load(a) | Node::Fixed(a) | Node::Store(a, _) = f.values[e.index()].node {
                if let Some(c) = cell_of(f, a).filter(|(x, _)| ok.get(x) == Some(&true)) {
                    if seen.insert(c) {
                        out.push(c);
                    }
                }
            }
        }
        out
    };
    if cells.is_empty() {
        return false;
    }
    let index: HashMap<(Value, i64), usize> = cells.iter().enumerate().map(|(i, &c)| (c, i)).collect();
    let n = cells.len();
    let preds = cfg::predecessors(f, &rpo);
    // (a function whose start is jumped back to has nowhere for what the
    // variables hold to come in: left to the knowing that follows)
    if !preds[f.entry().index()].is_empty() {
        return false;
    }
    let succs = |b: Block| -> Vec<Block> { f.blocks[b.index()].term.as_ref().map_or(vec![], |t| t.targets().iter().map(|t| t.block).collect()) };
    // which cells each block reads before setting, and sets
    let mut reads = vec![vec![false; n]; f.blocks.len()];
    let mut sets = vec![vec![false; n]; f.blocks.len()];
    for &b in &rpo {
        for &e in &f.blocks[b.index()].effects {
            match f.values[e.index()].node {
                Node::Load(a) | Node::Fixed(a) => {
                    if let Some(&i) = cell_of(f, a).and_then(|c| index.get(&c)) {
                        if !sets[b.index()][i] {
                            reads[b.index()][i] = true;
                        }
                    }
                }
                Node::Store(a, _) => {
                    if let Some(&i) = cell_of(f, a).and_then(|c| index.get(&c)) {
                        sets[b.index()][i] = true;
                    }
                }
                _ => {}
            }
        }
    }
    // where each may be read before it's set (backward, to a fixpoint)
    let mut live_in = vec![vec![false; n]; f.blocks.len()];
    loop {
        let mut changed = false;
        for &b in rpo.iter().rev() {
            let mut live: Vec<bool> = vec![false; n];
            for s in succs(b) {
                for i in 0..n {
                    live[i] |= live_in[s.index()][i];
                }
            }
            for i in 0..n {
                let l = reads[b.index()][i] || (live[i] && !sets[b.index()][i]);
                if l != live_in[b.index()][i] {
                    live_in[b.index()][i] = l;
                    changed = true;
                }
            }
        }
        if !changed {
            break;
        }
    }
    // a parameter for each where ways in meet and it's live
    let entry = f.entry();
    let mut params: HashMap<(Block, usize), Value> = HashMap::default();
    for &b in &rpo {
        if b != entry && preds[b.index()].len() > 1 {
            for i in 0..n {
                if live_in[b.index()][i] {
                    params.insert((b, i), f.add_param(b));
                }
            }
        }
    }
    // each block's value of each, at its start and end; loads become values
    // and stores go (an unset variable holds whatever: 0)
    let zero = f.int(0);
    let mut at_end: Vec<Vec<Value>> = vec![vec![zero; n]; f.blocks.len()];
    let mut map = HashMap::default();
    let mut removed = HashSet::default();
    for &b in &rpo {
        let mut now: Vec<Value> = match preds[b.index()].as_slice() {
            [p] if b != entry => at_end[p.index()].clone(),
            _ => (0..n).map(|i| params.get(&(b, i)).copied().unwrap_or(zero)).collect(),
        };
        for &e in &f.blocks[b.index()].effects.clone() {
            match f.values[e.index()].node {
                Node::Load(a) | Node::Fixed(a) => {
                    if let Some(&i) = cell_of(f, a).and_then(|c| index.get(&c)) {
                        map.insert(e, now[i]);
                        removed.insert(e);
                    }
                }
                Node::Store(a, v) => {
                    if let Some(&i) = cell_of(f, a).and_then(|c| index.get(&c)) {
                        now[i] = super::opt::resolve(&map, v);
                        removed.insert(e);
                    }
                }
                _ => {}
            }
        }
        at_end[b.index()] = now;
    }
    // what each jump passes the new parameters (in the order they were added)
    for &b in &rpo {
        let mut added: Vec<(usize, Value)> = (0..n).filter_map(|i| params.get(&(b, i)).map(|&p| (i, p))).collect();
        added.sort_by_key(|&(_, p)| p);
        if added.is_empty() {
            continue;
        }
        let mut sources = preds[b.index()].clone();
        sources.dedup();
        for q in sources {
            let values: Vec<Value> = added.iter().map(|&(i, _)| super::opt::resolve(&map, at_end[q.index()][i])).collect();
            f.blocks[q.index()].term.as_mut().unwrap().map_targets(|t| {
                let mut t = t.clone();
                if t.block == b {
                    t.args.extend(values.iter().copied());
                }
                t
            });
        }
    }
    replace_uses(f, &map);
    for block in &mut f.blocks {
        block.effects.retain(|e| !removed.contains(e));
    }
    true
}

/// Loads whose value is known, and stores nothing reads (see the module).
fn known_values(f: &mut Function, effects: &HashMap<String, Effects>) -> bool {
    let rpo = cfg::reverse_postorder(f);
    let preds = cfg::predecessors(f, &rpo);
    let aliasing = Aliasing::new(f, &rpo, effects);

    // what each block knows at its end, to a fixpoint
    let mut at_end: Vec<Option<Known>> = vec![None; f.blocks.len()];
    loop {
        let mut changed = false;
        for &b in &rpo {
            let known = known_on_entry(f, b, &preds, &at_end);
            let (_, _, end) = scan(f, b, known, &aliasing, effects);
            if at_end[b.index()].as_ref() != Some(&end) {
                at_end[b.index()] = Some(end);
                changed = true;
            }
        }
        if !changed {
            break;
        }
    }

    let mut map = HashMap::default();
    let mut removed = HashSet::default();
    let mut new_params = false;
    for &b in &rpo {
        let mut known = known_on_entry(f, b, &preds, &at_end);
        // cells every predecessor knows, but not the same value for, become
        // parameters if the block loads them
        let ways_in = &preds[b.index()];
        if b != f.entry() && ways_in.len() > 1 {
            let first = at_end[ways_in[0].index()].as_ref().unwrap();
            let mut places: Vec<Place> = first
                .keys()
                .filter(|p| !known.contains_key(p))
                .filter(|p| ways_in.iter().all(|q| at_end[q.index()].as_ref().unwrap().contains_key(p)))
                .copied()
                .collect();
            places.sort_by_key(|p| format!("{p:?}"));
            for p in places {
                if !loads_first(f, b, p, &aliasing, &preds, effects) {
                    continue;
                }
                let param = f.add_param(b);
                let mut sources = ways_in.clone();
                sources.dedup();
                for q in sources {
                    let v = at_end[q.index()].as_ref().unwrap()[&p];
                    f.blocks[q.index()].term.as_mut().unwrap().map_targets(|t| {
                        let mut t = t.clone();
                        if t.block == b {
                            t.args.push(v);
                        }
                        t
                    });
                }
                known.insert(p, param);
                new_params = true;
            }
        }
        let (forwarded, overwritten, end) = scan(f, b, known, &aliasing, effects);
        // what the new parameters hold is known from here on, to the
        // blocks only this one leads to, whose loads `loads_first` counted
        at_end[b.index()] = Some(end);
        for (load, v) in forwarded {
            map.insert(load, v);
            removed.insert(load);
        }
        removed.extend(overwritten);
    }

    let changed = !removed.is_empty() || new_params;
    replace_uses(f, &map);
    for block in &mut f.blocks {
        block.effects.retain(|e| !removed.contains(e));
    }
    changed | remove_dead(f, &rpo, &aliasing.escaped) | dead_stores(f, effects) | hoist_loads(f, effects)
}

/// Removes loads nothing uses, and stores to allocations nothing loads from.
fn remove_dead(f: &mut Function, rpo: &[Block], escaped: &HashSet<Value>) -> bool {
    let live = live_values(f, rpo);
    let mut used = HashSet::default();
    for (i, data) in f.values.iter().enumerate() {
        if live[i] {
            used.extend(data.node.operands());
        }
    }
    for &b in rpo {
        if let Some(t) = &f.blocks[b.index()].term {
            used.extend(t.operands());
        }
    }
    let effects: Vec<Value> = rpo.iter().flat_map(|b| f.blocks[b.index()].effects.clone()).collect();
    let loaded: HashSet<Root> = effects
        .iter()
        .filter_map(|&e| match f.values[e.index()].node {
            Node::Load(a) | Node::Fixed(a) => Some(place(f, a).root),
            _ => None,
        })
        .collect();
    let mut removed = HashSet::default();
    for &e in &effects {
        match f.values[e.index()].node {
            // nothing can tell which address an allocation got, unless it's used
            Node::Load(_) | Node::Fixed(_) | Node::Alloca(_) | Node::HeapAlloc(_) | Node::GcAlloc(..) if !used.contains(&e) => {
                removed.insert(e);
            }
            Node::Store(a, _) => {
                let root = place(f, a).root;
                if matches!(root, Root::Allocation(x) if !escaped.contains(&x)) && !loaded.contains(&root) {
                    removed.insert(e);
                }
            }
            _ => {}
        }
    }
    // (and allocations used only by loads and stores that are gone: a
    // variable, once the memory pass has made its value a register)
    // (all at once, in one look at every value)
    let live: HashSet<Value> = f.blocks.iter().flat_map(|b| b.effects.iter().copied()).filter(|e| !removed.contains(e)).collect();
    let allocas: HashSet<Value> = effects.iter().copied().filter(|&e| matches!(f.values[e.index()].node, Node::Alloca(_)) && !removed.contains(&e)).collect();
    let mut kept = HashSet::default();
    for (i, d) in f.values.iter().enumerate() {
        if d.block.is_none() {
            continue;
        }
        let gone = matches!(d.node, Node::Load(_) | Node::Fixed(_) | Node::Store(..)) && !live.contains(&Value(i as u32));
        for o in d.node.operands() {
            // (a use that keeps it: anything but a load or store that's gone,
            // and storing its address somewhere)
            if allocas.contains(&o) && (!gone || matches!(d.node, Node::Store(_, x) if x == o)) {
                kept.insert(o);
            }
        }
    }
    removed.extend(allocas.into_iter().filter(|a| !kept.contains(a)));
    if removed.is_empty() {
        return false;
    }
    for block in &mut f.blocks {
        block.effects.retain(|e| !removed.contains(e));
    }
    true
}

/// The places a function's loads and stores reach, numbered, so that sets
/// of them can be bits.
struct Places {
    list: Vec<Place>,
    ids: HashMap<Place, usize>,
    /// For each place a store reaches, the places it may alias, as bits.
    aliases: HashMap<usize, Vec<u64>>,
}

impl Places {
    fn new(f: &Function, rpo: &[Block], aliasing: &Aliasing) -> Places {
        let mut places = Places { list: vec![], ids: HashMap::default(), aliases: HashMap::default() };
        let mut stored = vec![];
        for &b in rpo {
            for &e in &f.blocks[b.index()].effects {
                if let Node::Load(a) | Node::Fixed(a) | Node::Store(a, _) = f.values[e.index()].node {
                    let p = place(f, a);
                    let next = places.list.len();
                    let id = *places.ids.entry(p).or_insert(next);
                    if id == next {
                        places.list.push(p);
                    }
                    if matches!(f.values[e.index()].node, Node::Store(..)) {
                        stored.push(id);
                    }
                }
            }
        }
        for id in stored {
            if !places.aliases.contains_key(&id) {
                let mut row = vec![0u64; places.words()];
                for (j, &q) in places.list.iter().enumerate() {
                    if aliasing.may_alias(q, places.list[id]) {
                        row[j / 64] |= 1 << (j % 64);
                    }
                }
                places.aliases.insert(id, row);
            }
        }
        places
    }

    fn words(&self) -> usize {
        self.list.len().div_ceil(64)
    }
}

/// What may be read later: these places (bits, by number), and if
/// `escaped`, anything a caller or callee can reach.
#[derive(Clone, PartialEq)]
struct Reads {
    places: Vec<u64>,
    escaped: bool,
}

/// Runs block `b` backward from what's read after it, and says which of its
/// stores nothing reads before they're overwritten.
fn reads_before(
    f: &Function,
    b: Block,
    mut reads: Reads,
    aliasing: &Aliasing,
    effects: &HashMap<String, Effects>,
    places: &Places,
) -> (Reads, Vec<Value>) {
    let mut dead = vec![];
    for &e in f.blocks[b.index()].effects.iter().rev() {
        match &f.values[e.index()].node {
            Node::Load(a) | Node::Fixed(a) => {
                let i = places.ids[&place(f, *a)];
                reads.places[i / 64] |= 1 << (i % 64);
            }
            Node::Store(a, _) => {
                let p = place(f, *a);
                let i = places.ids[&p];
                let aliased = reads.places.iter().zip(&places.aliases[&i]).any(|(x, y)| x & y != 0);
                if !(aliased || reads.escaped && aliasing.reaches(p)) {
                    dead.push(e);
                }
                // reads after here see this store, not earlier ones
                reads.places[i / 64] &= !(1 << (i % 64));
            }
            node @ (Node::Call(..) | Node::CallIndirect(..) | Node::CallExtern(..)) if call_effects(effects, callee(node)).reads => {
                reads.escaped = true
            }
            _ => {}
        }
    }
    (reads, dead)
}

/// Removes stores that every path overwrites before anything reads them, or
/// that nothing reads at all. At a return, a caller may read anything it can
/// reach, but not the function's own allocations.
fn dead_stores(f: &mut Function, effects: &HashMap<String, Effects>) -> bool {
    let rpo = cfg::reverse_postorder(f);
    let aliasing = Aliasing::new(f, &rpo, effects);
    let places = Places::new(f, &rpo, &aliasing);
    let none = Reads { places: vec![0; places.words()], escaped: false };
    let after = |f: &Function, b: Block, before: &HashMap<Block, Reads>| {
        if matches!(f.blocks[b.index()].term, Some(Terminator::Return(_))) {
            return Reads { places: none.places.clone(), escaped: true };
        }
        let mut reads = none.clone();
        for s in cfg::successors(f, b) {
            if let Some(theirs) = before.get(&s) {
                reads.places.iter_mut().zip(&theirs.places).for_each(|(x, y)| *x |= y);
                reads.escaped |= theirs.escaped;
            }
        }
        reads
    };
    // (a worklist: a block again only when what's after it changed)
    let preds = cfg::predecessors(f, &rpo);
    let mut before: HashMap<Block, Reads> = HashMap::default();
    let mut work: Vec<Block> = rpo.clone();
    let mut queued = vec![false; f.blocks.len()];
    rpo.iter().for_each(|b| queued[b.index()] = true);
    while let Some(b) = work.pop() {
        queued[b.index()] = false;
        let (reads, _) = reads_before(f, b, after(f, b, &before), &aliasing, effects, &places);
        if before.get(&b) != Some(&reads) {
            before.insert(b, reads);
            for &p in &preds[b.index()] {
                if !queued[p.index()] {
                    queued[p.index()] = true;
                    work.push(p);
                }
            }
        }
    }
    let mut dead = HashSet::default();
    for &b in &rpo {
        dead.extend(reads_before(f, b, after(f, b, &before), &aliasing, effects, &places).1);
    }
    if dead.is_empty() {
        return false;
    }
    for block in &mut f.blocks {
        block.effects.retain(|e| !dead.contains(e));
    }
    true
}

/// Whether loading `p` can't touch a bad address: it's inside an allocation
/// of known size.
fn in_bounds(f: &Function, p: Place) -> bool {
    let (Root::Allocation(a), Offset::Const(k)) = (p.root, p.offset) else { return false };
    let size = match &f.values[a.index()].node {
        Node::Alloca(cells) => Some(*cells as i64),
        Node::HeapAlloc(n) | Node::GcAlloc(n, _) => f.const_value(*n),
        _ => None,
    };
    size.is_some_and(|size| (0..size).contains(&k))
}

/// Hoists loads out of loops, into the block before the loop, when nothing in
/// the loop can change what they read. A load moves only if running it early
/// can't touch a bad address: it's in the loop's header, which runs whenever
/// the loop is entered, or it's inside an allocation of known size. (A
/// fixed load moves whenever its address is had before the loop.)
fn hoist_loads(f: &mut Function, effects: &HashMap<String, Effects>) -> bool {
    let rpo = cfg::reverse_postorder(f);
    let preds = cfg::predecessors(f, &rpo);
    let aliasing = Aliasing::new(f, &rpo, effects);
    for l in cfg::loops(f) {
        let mut stores = vec![];
        let mut writing_call = false;
        for b in &l.body {
            for &e in &f.blocks[b.index()].effects {
                match &f.values[e.index()].node {
                    Node::Store(a, _) => stores.push(place(f, *a)),
                    node @ (Node::Call(..) | Node::CallIndirect(..) | Node::CallExtern(..)) => {
                        writing_call |= call_effects(effects, callee(node)).writes
                    }
                    _ => {}
                }
            }
        }
        let outside = |v: Value| f.values[v.index()].block.is_none_or(|b| !l.body.contains(&b));
        let mut hoist = vec![];
        for &b in rpo.iter().filter(|b| l.body.contains(b)) {
            for &e in &f.blocks[b.index()].effects {
                match f.values[e.index()].node {
                    Node::Load(a) => {
                        let p = place(f, a);
                        if outside(a)
                            && !stores.iter().any(|&q| aliasing.may_alias(q, p))
                            && !(writing_call && aliasing.reaches(p))
                            && (b == l.header || in_bounds(f, p))
                        {
                            hoist.push((b, e));
                        }
                    }
                    // (what's there never changes, and can always be read)
                    Node::Fixed(a) if outside(a) => hoist.push((b, e)),
                    _ => {}
                }
            }
        }
        if hoist.is_empty() {
            continue;
        }
        let pre = preheader(f, l.header, &l.body, &preds);
        for (b, e) in hoist {
            f.blocks[b.index()].effects.retain(|&x| x != e);
            f.blocks[pre.index()].effects.push(e);
            f.values[e.index()].block = Some(pre);
        }
        return true;
    }
    false
}
