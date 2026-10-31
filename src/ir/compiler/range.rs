//! Range analysis: the interval each value lies in, on every cell width the
//! module targets.
//!
//! An interval only describes a value if its bounds fit in the narrowest
//! width the module targets (`Module::min_width`, 16 bits unless it says
//! otherwise), since then nothing in computing it can overflow on any width
//! the program can run on, and the value is the same on all of them.
//! Anything else is `Top`: possibly any value, and possibly a different one
//! on each width.
//!
//! The analysis is optimistic, like sparse conditional constant propagation:
//! blocks start unreachable and values start empty, and only edges that can
//! be taken add anything. Branches refine what's known along each edge, so
//! inside `if i < 10`, `i` is at most 9. Calls carry ranges into parameters
//! and out of returns. Loops are made to converge by widening, then narrowed
//! again.

use super::{cfg, BinOp, Block, Function, Module, Node, Terminator, UnOp, Value};
use crate::asm::fx::HashMap;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(in crate::ir) enum Range {
    /// No value: unreachable, or never computed.
    Empty,
    /// Within these bounds, which fit in the narrowest width.
    Int(i64, i64),
    /// Anything.
    Top,
}

use Range::{Empty, Int, Top};

impl Range {
    pub(in crate::ir) fn join(self, other: Range) -> Range {
        match (self, other) {
            (Empty, r) | (r, Empty) => r,
            (Int(a, b), Int(c, d)) => Int(a.min(c), b.max(d)),
            _ => Top,
        }
    }

    pub(in crate::ir) fn meet(self, other: Range) -> Range {
        match (self, other) {
            (Top, r) | (r, Top) => r,
            (Int(a, b), Int(c, d)) if a.max(c) <= b.min(d) => Int(a.max(c), b.min(d)),
            _ => Empty,
        }
    }

    pub(in crate::ir) fn singleton(self) -> Option<i64> {
        match self {
            Int(a, b) if a == b => Some(a),
            _ => None,
        }
    }

    pub(in crate::ir) fn bounds(self) -> Option<(i64, i64)> {
        match self {
            Int(a, b) => Some((a, b)),
            _ => None,
        }
    }

    fn wide_bounds(self) -> Option<(i128, i128)> {
        self.bounds().map(|(a, b)| (a as i128, b as i128))
    }

    /// Whether the value is known to be at least `k`.
    pub(in crate::ir) fn at_least(self, k: i64) -> bool {
        matches!(self, Int(a, _) if a >= k)
    }

    /// Whether the value is known to be at most `k`.
    pub(in crate::ir) fn at_most(self, k: i64) -> bool {
        matches!(self, Int(_, b) if b <= k)
    }

    fn excludes_zero(self) -> bool {
        matches!(self, Int(a, b) if a > 0 || b < 0)
    }
}

/// The narrowest cell width a module targets, as the bounds that a value has
/// to stay within to mean the same thing on every width.
#[derive(Clone, Copy, Debug)]
pub(in crate::ir) struct Width {
    lo: i128,
    hi: i128,
}

impl Width {
    pub(in crate::ir) fn new(bits: u32) -> Width {
        Width { lo: -(1 << (bits - 1)), hi: (1 << (bits - 1)) - 1 }
    }

    /// From `lo` to `hi`, if that's within the width.
    fn range(self, lo: i128, hi: i128) -> Range {
        if lo > hi {
            Empty
        } else if lo < self.lo || hi > self.hi {
            Top
        } else {
            Int(lo as i64, hi as i64)
        }
    }

    fn constant(self, k: i64) -> Range {
        self.range(k as i128, k as i128)
    }

    /// Widens a range that keeps growing to the width's limits, so loops
    /// converge.
    fn widen(self, old: Range, new: Range) -> Range {
        match (old, new) {
            (Int(a, b), Int(c, d)) => Int(
                if c < a { self.lo as i64 } else { a },
                if d > b { self.hi as i64 } else { b },
            ),
            _ => new,
        }
    }

    /// Whether `a - b` fits within the width for every value the two can take.
    pub(in crate::ir) fn difference_fits(self, a: Range, b: Range) -> bool {
        match (a.wide_bounds(), b.wide_bounds()) {
            (Some((al, ah)), Some((bl, bh))) => al - bh >= -self.hi && ah - bl <= self.hi,
            _ => false,
        }
    }
}

pub(in crate::ir) fn binary(op: BinOp, a: Range, b: Range, w: Width) -> Range {
    use BinOp::*;
    if a == Empty || b == Empty {
        return Empty;
    }
    let comparison = |known: Option<bool>| match known {
        Some(true) => w.constant(1),
        Some(false) => w.constant(0),
        None => Int(0, 1),
    };
    match op {
        Eq | Ne | Lt | Le | Gt | Ge | LtU | LeU | GtU | GeU => {
            let (Some((al, ah)), Some((bl, bh))) = (a.bounds(), b.bounds()) else {
                return comparison(None);
            };
            // unsigned comparisons agree with signed ones for values >= 0
            if matches!(op, LtU | LeU | GtU | GeU) && (al < 0 || bl < 0) {
                return comparison(None);
            }
            let known = match op {
                Lt | LtU => decide(ah < bl, al >= bh),
                Le | LeU => decide(ah <= bl, al > bh),
                Gt | GtU => decide(al > bh, ah <= bl),
                Ge | GeU => decide(al >= bh, ah < bl),
                Eq => decide(al == ah && bl == bh && al == bl, ah < bl || bh < al),
                _ => decide(ah < bl || bh < al, al == ah && bl == bh && al == bl),
            };
            comparison(known)
        }
        // a remainder is smaller than the divisor whatever the dividend is
        Rem | RemU if b.excludes_zero() && (op == Rem || b.at_least(0)) => {
            let (bl, bh) = b.wide_bounds().unwrap();
            let m = bl.abs().max(bh.abs()) - 1;
            match a.wide_bounds() {
                Some((al, ah)) if al >= 0 => w.range(0, ah.min(m)),
                Some((al, ah)) if ah <= 0 && op == Rem => w.range(al.max(-m), 0),
                _ if op == Rem => w.range(-m, m),
                _ => w.range(0, m),
            }
        }
        And if a.at_least(0) || b.at_least(0) => {
            let hi = match (a, b) {
                (Int(0.., ah), Int(0.., bh)) => ah.min(bh),
                (Int(0.., ah), _) => ah,
                (_, Int(_, bh)) => bh,
                _ => unreachable!(),
            };
            w.range(0, hi as i128)
        }
        _ => {
            let (Some((al, ah)), Some((bl, bh))) = (a.wide_bounds(), b.wide_bounds()) else { return Top };
            match op {
                Add => w.range(al + bl, ah + bh),
                Sub => w.range(al - bh, ah - bl),
                Mul => corners(al, ah, bl, bh, w, |x, y| x * y),
                Div | DivU if bl > 0 || bh < 0 => {
                    if op == DivU && (al < 0 || bl < 0) {
                        return Top;
                    }
                    corners(al, ah, bl, bh, w, |x, y| x / y)
                }
                Or | Xor if al >= 0 && bl >= 0 => {
                    let top = (ah.max(bh) as u128 + 1).next_power_of_two() as i128 - 1;
                    w.range(0, top)
                }
                Shl if al >= 0 && bl >= 0 && bh < 63 => w.range(al << bl, ah << bh),
                Shr | ShrU if (op == Shr || al >= 0) && bl >= 0 => {
                    let shift = |x: i128, s: i128| x >> s.min(127);
                    w.range(shift(al, bl).min(shift(al, bh)), shift(ah, bl).max(shift(ah, bh)))
                }
                Min => w.range(al.min(bl), ah.min(bh)),
                Max => w.range(al.max(bl), ah.max(bh)),
                _ => Top,
            }
        }
    }
}

/// `Some(true)` if `yes`, `Some(false)` if `no`, else unknown.
fn decide(yes: bool, no: bool) -> Option<bool> {
    if yes {
        Some(true)
    } else if no {
        Some(false)
    } else {
        None
    }
}

/// The range of `f` over the corners of two intervals, for an `f` that's
/// monotonic in each argument on them.
fn corners(al: i128, ah: i128, bl: i128, bh: i128, w: Width, f: impl Fn(i128, i128) -> i128) -> Range {
    let values = [f(al, bl), f(al, bh), f(ah, bl), f(ah, bh)];
    w.range(*values.iter().min().unwrap(), *values.iter().max().unwrap())
}

pub(in crate::ir) fn unary(op: UnOp, a: Range, w: Width) -> Range {
    match (op, a.wide_bounds()) {
        (_, _) if a == Empty => Empty,
        (UnOp::LNot, Some((lo, hi))) if lo > 0 || hi < 0 => w.constant(0),
        (UnOp::LNot, Some((0, 0))) => w.constant(1),
        (UnOp::LNot, _) => Int(0, 1),
        (_, None) => Top,
        (UnOp::Neg, Some((lo, hi))) => w.range(-hi, -lo),
        (UnOp::Not, Some((lo, hi))) => w.range(-hi - 1, -lo - 1),
        (UnOp::Abs, Some((lo, _))) if lo >= 0 => a,
        (UnOp::Abs, Some((lo, hi))) if hi <= 0 => w.range(-hi, -lo),
        (UnOp::Abs, Some((lo, hi))) => w.range(0, (-lo).max(hi)),
    }
}

/// The ranges of one function's values.
pub(in crate::ir) struct Ranges {
    /// The module's narrowest width.
    pub(in crate::ir) width: Width,
    range: Vec<Range>,
    /// What's known about values inside each block, from the branches that
    /// lead to it.
    facts: Vec<HashMap<Value, Range>>,
    /// Whether each block can run.
    pub(in crate::ir) reachable: Vec<bool>,
}

impl Ranges {
    /// The range of `v` where block `b` uses it: anything, for values made
    /// since the analysis.
    pub(in crate::ir) fn at(&self, v: Value, b: Block) -> Range {
        let Some(&r) = self.range.get(v.index()) else { return Range::Top };
        match self.facts.get(b.index()).and_then(|facts| facts.get(&v)) {
            Some(&fact) => r.meet(fact),
            None => r,
        }
    }
}

/// Analyzes every function in `module`: each with what flows into its
/// parameters and out of what it calls, over and over until that settles.
/// A function's analysis depends on nothing else, so after the first round
/// only the functions whose parameters, or whose callees' returns, have
/// changed are analyzed again; and each round's are analyzed on as many
/// threads as there are cores.
pub(in crate::ir) fn analyze(module: &Module) -> Vec<Ranges> {
    let w = Width::new(module.min_width);
    let n = module.funcs.len();
    // what flows into each function's parameters, and out of its returns
    let mut params: Vec<Vec<Range>> = module.funcs.iter().map(|f| vec![Empty; f.param_count()]).collect();
    let callers = called_from(module);
    let callees = module.callees();
    let taken = module.address_taken();
    for (i, f) in module.funcs.iter().enumerate() {
        // a function nothing calls, or that can be called indirectly, is
        // analyzed as if called with anything
        if i > 0 && (!callers[i] || taken[i]) {
            params[i] = vec![Top; f.param_count()];
        }
    }
    let mut returns = vec![Empty; n];
    let mut changes = vec![0; n];
    // each function's latest analysis: its ranges, the calls it can make
    // (with their arguments' ranges), and what it can return
    let mut results: Vec<Option<Ranges>> = (0..n).map(|_| None).collect();
    let mut calls: Vec<Vec<(usize, Vec<Range>)>> = vec![vec![]; n];
    let mut rets = vec![Empty; n];
    let mut dirty = vec![true; n];
    let mut rounds = 0;
    loop {
        rounds += 1;
        let todo: Vec<usize> = (0..n).filter(|&i| dirty[i]).collect();
        for (i, (ranges, made, ret)) in analyze_all(module, &todo, &params, &returns, w) {
            results[i] = Some(ranges);
            calls[i] = made;
            rets[i] = ret;
        }
        let mut new_params = params.clone();
        for made in &calls {
            for (callee, args) in made {
                if callers[*callee] {
                    for (p, a) in new_params[*callee].iter_mut().zip(args) {
                        *p = p.join(*a);
                    }
                }
            }
        }
        // calls widen like loops, so recursion converges
        let mut changed = false;
        let (mut params_changed, mut returns_changed) = (vec![false; n], vec![false; n]);
        for i in 0..n {
            if new_params[i] != params[i] || rets[i] != returns[i] {
                changed = true;
                changes[i] += 1;
                let (old_params, old_return) = (params[i].clone(), returns[i]);
                if changes[i] > 3 {
                    for (p, new) in params[i].iter_mut().zip(&new_params[i]) {
                        *p = w.widen(*p, p.join(*new));
                    }
                    returns[i] = w.widen(returns[i], returns[i].join(rets[i]));
                } else {
                    params[i] = new_params[i].clone();
                    returns[i] = rets[i];
                }
                params_changed[i] = params[i] != old_params;
                returns_changed[i] = returns[i] != old_return;
            }
        }
        if !changed || rounds > 50 {
            if changed {
                // give up on precision rather than risk an unsound result
                for i in 1..n {
                    params[i] = vec![Top; params[i].len()];
                    returns[i] = Top;
                }
                let everything: Vec<usize> = (0..n).collect();
                for (i, (ranges, _, _)) in analyze_all(module, &everything, &params, &returns, w) {
                    results[i] = Some(ranges);
                }
            }
            return results.into_iter().map(|r| r.expect("every function analyzed")).collect();
        }
        for i in 0..n {
            dirty[i] = params_changed[i] || callees[i].iter().any(|&c| returns_changed[c]);
        }
    }
}

/// The functions numbered in `todo`, analyzed (see `analyze_function`) on
/// as many threads as there are cores, each taking the next there is to do.
#[allow(clippy::type_complexity)]
fn analyze_all(module: &Module, todo: &[usize], params: &[Vec<Range>], returns: &[Range], w: Width) -> Vec<(usize, (Ranges, Vec<(usize, Vec<Range>)>, Range))> {
    let next = std::sync::atomic::AtomicUsize::new(0);
    let threads = std::thread::available_parallelism().map_or(1, |n| n.get()).min(todo.len().max(1));
    std::thread::scope(|scope| {
        let workers: Vec<_> = (0..threads)
            .map(|_| {
                scope.spawn(|| {
                    let mut out = vec![];
                    loop {
                        let k = next.fetch_add(1, std::sync::atomic::Ordering::Relaxed);
                        let Some(&i) = todo.get(k) else { break };
                        out.push((i, analyze_function(module, &module.funcs[i], &params[i], returns, w)));
                    }
                    out
                })
            })
            .collect();
        workers.into_iter().flat_map(|w| w.join().unwrap()).collect()
    })
}

/// Whether each function is called from somewhere.
fn called_from(module: &Module) -> Vec<bool> {
    let mut called = vec![false; module.funcs.len()];
    for callees in module.callees() {
        for i in callees {
            called[i] = true;
        }
    }
    called
}

/// Analyzes one function, given its parameters' ranges and every function's
/// return range. Returns its ranges, the arguments of each call it can make,
/// and what it can return.
fn analyze_function(
    module: &Module,
    f: &Function,
    params: &[Range],
    returns: &[Range],
    w: Width,
) -> (Ranges, Vec<(usize, Vec<Range>)>, Range) {
    let rpo = cfg::reverse_postorder(f);
    let idom = cfg::dominators(f, &rpo);
    let preds = cfg::predecessors(f, &rpo);
    let pinned = f.pinned();
    let mut range = vec![Empty; f.values.len()];
    for (i, data) in f.values.iter().enumerate() {
        if let Node::Const(k) = data.node {
            range[i] = w.constant(k);
        }
    }
    let mut ranges = Ranges {
        width: w,
        range,
        facts: vec![HashMap::default(); f.blocks.len()],
        reachable: vec![false; f.blocks.len()],
    };
    for (&p, &r) in f.blocks[0].params.iter().zip(params) {
        ranges.range[p.index()] = r;
    }

    let mut changes = vec![0u32; f.values.len()];
    let mut narrowing = 0;
    // what each block's parameters receive, from the previous pass, since back
    // edges are only seen after the block in a pass
    let empty: Vec<Vec<Range>> = f.blocks.iter().map(|b| vec![Empty; b.params.len()]).collect();
    let mut previous = empty.clone();
    for _ in 0..1000 {
        let mut changed = false;
        let mut incoming = empty.clone();
        let mut live_edge = vec![false; f.blocks.len()];
        live_edge[0] = true;
        for &b in &rpo {
            ranges.reachable[b.index()] = live_edge[b.index()];
            if !live_edge[b.index()] {
                continue;
            }
            ranges.facts[b.index()] = facts_for(f, b, &idom, &preds, &ranges, w);
            // parameters: what every taken edge into the block passes
            if b != f.entry() {
                for (i, &p) in f.blocks[b.index()].params.iter().enumerate() {
                    let new = previous[b.index()][i];
                    let old = ranges.range[p.index()];
                    let new = if narrowing > 0 {
                        new
                    } else {
                        let joined = old.join(new);
                        if joined != old {
                            changes[p.index()] += 1;
                        }
                        if changes[p.index()] > 3 { w.widen(old, joined) } else { joined }
                    };
                    if new != old {
                        ranges.range[p.index()] = new;
                        changed = true;
                    }
                }
            }
            for &v in &pinned[b.index()] {
                let data = &f.values[v.index()];
                let new = match &data.node {
                    Node::Const(_) | Node::Param(..) => continue,
                    Node::Unary(op, a) => unary(*op, ranges.at(*a, b), w),
                    Node::Binary(op, a, x) => binary(*op, ranges.at(*a, b), ranges.at(*x, b), w),
                    Node::GetChar => Int(-1, 255),
                    Node::Call(name, _) => module.index_of(name).map_or(Top, |i| returns[i]),
                    _ if data.node.has_result() => Top,
                    _ => continue,
                };
                if new != ranges.range[v.index()] {
                    ranges.range[v.index()] = new;
                    changed = true;
                }
            }
            // edges out
            let term = f.blocks[b.index()].term.as_ref().expect("verified");
            let mut take = |target: &super::Target, edge: &HashMap<Value, Range>| {
                live_edge[target.block.index()] = true;
                for (slot, &a) in incoming[target.block.index()].iter_mut().zip(&target.args) {
                    let r = ranges.at(a, b);
                    let r = edge.get(&a).map_or(r, |&fact| r.meet(fact));
                    *slot = slot.join(r);
                }
            };
            match term {
                Terminator::Jump(t) => take(t, &HashMap::default()),
                Terminator::Branch(c, t, e) => {
                    let cond = ranges.at(*c, b);
                    if cond != Empty && cond != w.constant(0) {
                        take(t, &edge_facts(f, *c, true, &ranges, b, w));
                    }
                    if cond != Empty && !cond.excludes_zero() {
                        take(e, &edge_facts(f, *c, false, &ranges, b, w));
                    }
                }
                Terminator::Return(_) => {}
            }
        }
        if incoming != previous {
            changed = true;
        }
        previous = incoming;
        if !changed {
            // a couple of passes without widening recover precision it lost
            narrowing += 1;
            if narrowing > 2 {
                break;
            }
        }
    }

    // calls and returns, from the blocks that can run
    let mut calls = vec![];
    let mut ret = Empty;
    for &b in &rpo {
        if !ranges.reachable[b.index()] {
            continue;
        }
        for &e in &f.blocks[b.index()].effects {
            if let Node::Call(name, args) = &f.values[e.index()].node {
                if let Some(callee) = module.index_of(name) {
                    calls.push((callee, args.iter().map(|&a| ranges.at(a, b)).collect()));
                }
            }
        }
        if let Some(Terminator::Return(v)) = &f.blocks[b.index()].term {
            ret = ret.join(v.map_or(w.constant(0), |v| ranges.at(v, b)));
        }
    }
    (ranges, calls, ret)
}

/// What's known inside `b` from the branches on the way to it: each block on
/// its dominator chain with a single predecessor that branches to it.
fn facts_for(
    f: &Function,
    b: Block,
    idom: &[Option<Block>],
    preds: &[Vec<Block>],
    ranges: &Ranges,
    w: Width,
) -> HashMap<Value, Range> {
    let mut facts: HashMap<Value, Range> = HashMap::default();
    let mut x = b;
    loop {
        if let [p] = preds[x.index()][..] {
            if let Some(Terminator::Branch(c, t, e)) = &f.blocks[p.index()].term {
                if t.block != e.block {
                    for (v, r) in edge_facts(f, *c, t.block == x, ranges, p, w) {
                        let known = facts.get(&v).copied().unwrap_or(Top);
                        facts.insert(v, known.meet(r));
                    }
                }
            }
        }
        match idom[x.index()] {
            Some(up) if up != x => x = up,
            _ => return facts,
        }
    }
}

/// What's known about the operands of `cond`, in block `at`, once a branch on
/// it goes one way.
fn edge_facts(f: &Function, cond: Value, taken: bool, ranges: &Ranges, at: Block, w: Width) -> HashMap<Value, Range> {
    use BinOp::*;
    let mut facts = HashMap::default();
    facts.insert(cond, if taken { ranges.at(cond, at).meet(nonzero(ranges.at(cond, at), w)) } else { w.constant(0) });
    match &f.values[cond.index()].node {
        Node::Binary(op @ (Lt | Le | Gt | Ge | Eq | Ne), x, y) => {
            let op = if taken { *op } else { negate(*op) };
            let (rx, ry) = (ranges.at(*x, at), ranges.at(*y, at));
            facts.insert(*x, constrain(op, rx, ry, w));
            facts.insert(*y, constrain(op.swapped().unwrap(), ry, rx, w));
        }
        Node::Unary(UnOp::LNot, x) => {
            let rx = ranges.at(*x, at);
            facts.insert(*x, if taken { w.constant(0) } else { nonzero(rx, w) });
        }
        _ => {}
    }
    facts
}

fn negate(op: BinOp) -> BinOp {
    use BinOp::*;
    match op {
        Lt => Ge,
        Ge => Lt,
        Le => Gt,
        Gt => Le,
        Eq => Ne,
        Ne => Eq,
        _ => unreachable!(),
    }
}

/// `r` without 0, as far as an interval can say so.
fn nonzero(r: Range, w: Width) -> Range {
    match r.wide_bounds() {
        Some((0, hi)) => w.range(1, hi),
        Some((lo, 0)) => w.range(lo, -1),
        _ => r,
    }
}

/// The range of `x`, in `rx`, given `x op y` for a `y` in `ry`. A bound only
/// carries over from `y` if `x` already has the other one, or `x` could still
/// be anything on some width.
fn constrain(op: BinOp, rx: Range, ry: Range, w: Width) -> Range {
    use BinOp::*;
    let (Some((yl, yh)), Some((xl, xh))) = (ry.wide_bounds(), rx.wide_bounds()) else {
        return match (op, ry) {
            (Eq, Int(..)) => rx.meet(ry),
            _ => rx,
        };
    };
    match op {
        Lt => w.range(xl, xh.min(yh - 1)),
        Le => w.range(xl, xh.min(yh)),
        Gt => w.range(xl.max(yl + 1), xh),
        Ge => w.range(xl.max(yl), xh),
        Eq => rx.meet(ry),
        _ => match ry.singleton().map(|k| k as i128) {
            Some(k) if k == xl => w.range(xl + 1, xh),
            Some(k) if k == xh => w.range(xl, xh - 1),
            _ => rx,
        },
    }
}
