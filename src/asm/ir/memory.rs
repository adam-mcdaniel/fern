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
//! Addresses are compared by where they point: an allocation (or an unknown
//! pointer) plus a constant offset, when the offset is constant. Different
//! allocations never overlap, and an allocation whose address never escapes
//! (it's only ever used to load, store or index) can't be reached through any
//! other pointer, or by a call.

use super::interproc::Effects;
use super::opt::{preheader, replace_uses};
use super::{cfg, BinOp, Block, Function, Node, Value};
use std::collections::{HashMap, HashSet};

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
        Node::Alloca(_) | Node::HeapAlloc(_) | Node::GcAlloc(_) => Place { root: Root::Allocation(addr), offset: Offset::Const(0) },
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

/// The allocations whose address is used for anything but loading, storing
/// or indexing, since another pointer could then reach them.
pub(super) fn escaping(f: &Function, live: &[Block]) -> HashSet<Value> {
    let mut escaped = HashSet::new();
    let mut escape = |f: &Function, v: Value| {
        if let Root::Allocation(a) = place(f, v).root {
            escaped.insert(a);
        }
    };
    for data in &f.values {
        if !data.block.is_some_and(|b| live.contains(&b)) {
            continue;
        }
        match &data.node {
            Node::Load(_) => {}
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
pub(super) fn private_alloca(f: &Function, addr: Value, escaped: &HashSet<Value>) -> bool {
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

fn may_alias(a: Place, b: Place, escaped: &HashSet<Value>) -> bool {
    match (a.root, b.root) {
        (Root::Allocation(x), Root::Allocation(y)) if x != y => false,
        (Root::Globals, Root::Allocation(_)) | (Root::Allocation(_), Root::Globals) => false,
        (Root::Allocation(x), Root::Unknown(_)) | (Root::Unknown(_), Root::Allocation(x)) => escaped.contains(&x),
        _ if a.root == b.root => match (a.offset, b.offset) {
            (Offset::Const(x), Offset::Const(y)) => x == y,
            _ => true,
        },
        _ => true,
    }
}

/// Whether a call can touch memory at `p`.
fn call_reaches(p: Place, escaped: &HashSet<Value>) -> bool {
    !matches!(p.root, Root::Allocation(a) if !escaped.contains(&a))
}

type Known = HashMap<Place, Value>;

/// What block `b` knows on entry, from what its predecessors know at their
/// ends. A predecessor not yet analyzed (around a loop) doesn't limit it, so
/// the analysis starts optimistic and only drops facts.
fn known_on_entry(f: &Function, b: Block, preds: &[Vec<Block>], at_end: &[Option<Known>]) -> Known {
    if b == f.entry() {
        return Known::new();
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
    let Some(&(first, _)) = edges.first() else { return Known::new() };
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
    escaped: &HashSet<Value>,
    effects: &HashMap<String, Effects>,
) -> (Vec<(Value, Value)>, Vec<Value>, Known) {
    let mut forwarded = vec![];
    let mut overwritten = vec![];
    // stores in this block that nothing has read since
    let mut unread: HashMap<Place, Value> = HashMap::new();
    for &e in &f.blocks[b.index()].effects {
        match f.values[e.index()].node {
            Node::Load(a) => {
                let p = place(f, a);
                match known.get(&p) {
                    Some(&v) => forwarded.push((e, v)),
                    None => {
                        known.insert(p, e);
                    }
                }
                unread.retain(|q, _| !may_alias(*q, p, escaped));
            }
            Node::Store(a, v) => {
                let p = place(f, a);
                if let Some(earlier) = unread.insert(p, e) {
                    overwritten.push(earlier);
                }
                known.retain(|q, _| !may_alias(*q, p, escaped));
                unread.retain(|q, _| *q == p || !may_alias(*q, p, escaped));
                known.insert(p, v);
            }
            Node::Call(..) | Node::CallIndirect(..) | Node::CallExtern(..) => {
                let call = call_effects(effects, callee(&f.values[e.index()].node));
                if call.writes {
                    known.retain(|q, _| !call_reaches(*q, escaped));
                }
                if call.reads {
                    unread.retain(|q, _| !call_reaches(*q, escaped));
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
    escaped: &HashSet<Value>,
    preds: &[Vec<Block>],
    effects: &HashMap<String, Effects>,
) -> bool {
    for &e in &f.blocks[b.index()].effects {
        match &f.values[e.index()].node {
            Node::Load(a) if place(f, *a) == p => return true,
            Node::Store(a, _) if may_alias(place(f, *a), p, escaped) => return false,
            node @ (Node::Call(..) | Node::CallIndirect(..) | Node::CallExtern(..))
                if call_effects(effects, callee(node)).writes && call_reaches(p, escaped) =>
            {
                return false;
            }
            _ => {}
        }
    }
    cfg::successors(f, b)
        .into_iter()
        .any(|s| s != b && preds[s.index()] == [b] && loads_first(f, s, p, escaped, preds, effects))
}

pub(super) fn optimize(f: &mut Function, effects: &HashMap<String, Effects>) -> bool {
    let rpo = cfg::reverse_postorder(f);
    let preds = cfg::predecessors(f, &rpo);
    let escaped = escaping(f, &rpo);

    // what each block knows at its end, to a fixpoint
    let mut at_end: Vec<Option<Known>> = vec![None; f.blocks.len()];
    loop {
        let mut changed = false;
        for &b in &rpo {
            let known = known_on_entry(f, b, &preds, &at_end);
            let (_, _, end) = scan(f, b, known, &escaped, effects);
            if at_end[b.index()].as_ref() != Some(&end) {
                at_end[b.index()] = Some(end);
                changed = true;
            }
        }
        if !changed {
            break;
        }
    }

    let mut map = HashMap::new();
    let mut removed = HashSet::new();
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
                if !loads_first(f, b, p, &escaped, &preds, effects) {
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
        let (forwarded, overwritten, end) = scan(f, b, known, &escaped, effects);
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
    changed | remove_dead(f, &rpo, &escaped) | dead_stores(f, effects) | hoist_loads(f, effects)
}

/// Removes loads nothing uses, and stores to allocations nothing loads from.
fn remove_dead(f: &mut Function, rpo: &[Block], escaped: &HashSet<Value>) -> bool {
    let mut used = HashSet::new();
    for data in &f.values {
        if data.block.is_some() {
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
            Node::Load(a) => Some(place(f, a).root),
            _ => None,
        })
        .collect();
    let mut removed = HashSet::new();
    for &e in &effects {
        match f.values[e.index()].node {
            // nothing can tell which address an allocation got, unless it's used
            Node::Load(_) | Node::Alloca(_) | Node::HeapAlloc(_) | Node::GcAlloc(_) if !used.contains(&e) => {
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
    if removed.is_empty() {
        return false;
    }
    for block in &mut f.blocks {
        block.effects.retain(|e| !removed.contains(e));
    }
    true
}

/// What may be read later: these places, and if `escaped`, anything a
/// caller or callee can reach.
#[derive(Clone, Default, PartialEq)]
struct Reads {
    places: HashSet<Place>,
    escaped: bool,
}

impl Reads {
    fn may_read(&self, p: Place, escaped: &HashSet<Value>) -> bool {
        (self.escaped && call_reaches(p, escaped)) || self.places.iter().any(|&q| may_alias(q, p, escaped))
    }
}

/// Runs block `b` backward from what's read after it, and says which of its
/// stores nothing reads before they're overwritten.
fn reads_before(
    f: &Function,
    b: Block,
    mut reads: Reads,
    escaped: &HashSet<Value>,
    effects: &HashMap<String, Effects>,
) -> (Reads, Vec<Value>) {
    let mut dead = vec![];
    for &e in f.blocks[b.index()].effects.iter().rev() {
        match &f.values[e.index()].node {
            Node::Load(a) => {
                reads.places.insert(place(f, *a));
            }
            Node::Store(a, _) => {
                let p = place(f, *a);
                if !reads.may_read(p, escaped) {
                    dead.push(e);
                }
                // reads after here see this store, not earlier ones
                reads.places.remove(&p);
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
    let escaped = escaping(f, &rpo);
    let after = |f: &Function, b: Block, before: &HashMap<Block, Reads>| {
        if matches!(f.blocks[b.index()].term, Some(super::Terminator::Return(_))) {
            return Reads { places: HashSet::new(), escaped: true };
        }
        let mut reads = Reads::default();
        for s in cfg::successors(f, b) {
            if let Some(theirs) = before.get(&s) {
                reads.places.extend(&theirs.places);
                reads.escaped |= theirs.escaped;
            }
        }
        reads
    };
    let mut before: HashMap<Block, Reads> = HashMap::new();
    loop {
        let mut changed = false;
        for &b in rpo.iter().rev() {
            let (reads, _) = reads_before(f, b, after(f, b, &before), &escaped, effects);
            if before.get(&b) != Some(&reads) {
                before.insert(b, reads);
                changed = true;
            }
        }
        if !changed {
            break;
        }
    }
    let mut dead = HashSet::new();
    for &b in &rpo {
        dead.extend(reads_before(f, b, after(f, b, &before), &escaped, effects).1);
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
        Node::HeapAlloc(n) | Node::GcAlloc(n) => f.const_value(*n),
        _ => None,
    };
    size.is_some_and(|size| (0..size).contains(&k))
}

/// Hoists loads out of loops, into the block before the loop, when nothing in
/// the loop can change what they read. A load moves only if running it early
/// can't touch a bad address: it's in the loop's header, which runs whenever
/// the loop is entered, or it's inside an allocation of known size.
fn hoist_loads(f: &mut Function, effects: &HashMap<String, Effects>) -> bool {
    let rpo = cfg::reverse_postorder(f);
    let preds = cfg::predecessors(f, &rpo);
    let escaped = escaping(f, &rpo);
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
                if let Node::Load(a) = f.values[e.index()].node {
                    let p = place(f, a);
                    if outside(a)
                        && !stores.iter().any(|&q| may_alias(q, p, &escaped))
                        && !(writing_call && call_reaches(p, &escaped))
                        && (b == l.header || in_bounds(f, p))
                    {
                        hoist.push((b, e));
                    }
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
