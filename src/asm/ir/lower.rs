//! Lowering a module to ops.
//!
//! Each function is planned first: its blocks' DAGs are scheduled, and its
//! values are given numbered slots by coloring their interference graph, so
//! values that are never live at the same time share a slot. Slots are fixed
//! cells at the bottom of the stack, which are the cheapest to reach (and
//! functions that can't be running at the same time share them), except
//! in a recursive function for values that are live across a call that can
//! come back into it: those go in its stack frame, which only such functions
//! have. Callers write arguments straight into the callee's parameter cells,
//! and results come back in R0.
//!
//! The VM only has structured loops, so control flow is rebuilt from the
//! graph, with Ramsey's algorithm ("Beyond Relooper", 2022): the dominator
//! tree gives the nesting. A loop header becomes a loop, a block with several
//! predecessors comes after a region that ends where it begins, and a jump to
//! either is a break or continue. Most of those are just falling off the end
//! of something; the rest set a flag that skips code on the way out. The rare
//! graph this can't rebuild (an irreducible one, with a loop entered in more
//! than one place) falls back to a loop that keeps the current block's number
//! in a slot and checks each block against it.
//!
//! Range analysis picks cheaper helpers where it can: comparisons of values
//! that are close together, and multiplication by small numbers.
//!
//! Before any of that, [`prepare`](super::prepare) adds the garbage collector
//! if the module needs it, adds the checks that stop the program if the
//! stack and heap run into each other, and turns aborts into returns.

use super::range::{self, Range, Ranges};
use super::{cfg, prepare, sched, verify, BinOp, Block, Function, Intrinsic, Module, Node, Target, Terminator, UnOp, Value};
use crate::asm::{self, Location, Program, R0, R1, R2, R3};
use crate::Op;
use std::cell::Cell;
use std::collections::{HashMap, HashSet};

/// Settings for [`lower_with`].
#[derive(Clone, Debug)]
pub struct Options {
    /// The tape size to set the heap up for, as for `asm::init_with`.
    pub cells: u64,
    /// Whether to stop the program, with "stack overflow" or "out of
    /// memory", when the stack would run into the heap. Without the checks,
    /// such a program overwrites its own memory.
    pub checks: bool,
    /// Whether to optimize the ops (with `asm::opt`).
    pub optimize: bool,
}

impl Default for Options {
    fn default() -> Self {
        Options { cells: asm::DEFAULT_CELLS, checks: true, optimize: true }
    }
}

/// Lowers a module to ops for a tape of `asm::DEFAULT_CELLS` cells. The
/// result runs on any cell width from the module's minimum up.
pub fn lower(module: &Module) -> Result<Vec<Op>, String> {
    lower_with(module, &Options::default())
}

pub fn lower_with(module: &Module, options: &Options) -> Result<Vec<Op>, String> {
    verify(module)?;
    let prepared = prepare::prepare(module, options.checks, |m| plans(m).iter().map(|p| p.frame).max().unwrap_or(0))?;
    verify(&prepared).map_err(|e| format!("after preparing the module to lower: {e}"))?;
    let module = &prepared;
    let live = live_functions(module);
    let ranges = range::analyze(module);
    let taken = module.address_taken();
    let plans = plans(module);
    // the global cells come first, then a shared area of cells where
    // functions that can be called indirectly take their arguments
    let globals = module.globals as u64;
    let area = (0..module.funcs.len()).filter(|&i| taken[i]).map(|i| module.funcs[i].param_count()).max().unwrap_or(0);
    // functions that can't be running at the same time (neither can lead
    // to a call of the other) share fixed cells: each goes in the first
    // place that's clear of the ones that can, biggest first
    let reach = reachable_functions(module);
    let start = globals + area as u64;
    let mut statics = start;
    let mut bases = vec![0; plans.len()];
    let mut order: Vec<usize> = (0..plans.len()).filter(|&i| live[i]).collect();
    order.sort_by_key(|&i| std::cmp::Reverse(plans[i].statics));
    let mut placed: Vec<(usize, u64, u64)> = vec![];
    for i in order {
        let size = plans[i].statics as u64;
        let busy: Vec<(u64, u64)> =
            placed.iter().filter(|&&(j, ..)| reach[i][j] || reach[j][i]).map(|&(_, from, to)| (from, to)).collect();
        let mut base = start;
        while let Some(&(_, to)) = busy.iter().find(|&&(from, to)| base < to && from < base + size) {
            base = to;
        }
        bases[i] = base;
        placed.push((i, base, base + size));
        statics = statics.max(base + size);
    }
    if asm::STACK_BASE + statics >= options.cells {
        return Err(format!("{statics} cells of fixed storage don't fit on a tape of {} cells", options.cells));
    }

    let layout = Layout { module, plans: &plans, bases: &bases, taken: &taken, globals, area };
    let mut out = vec![];
    asm::init_with(&mut out, options.cells);
    if statics > 0 {
        asm::alloc(&mut out, statics as i64);
    }
    for (i, f) in module.funcs.iter().enumerate() {
        if live[i] {
            Emitter {
                f,
                plan: &plans[i],
                base: bases[i],
                main: i == 0,
                ranges: &ranges[i],
                acc: Cell::new(None),
                layout: &layout,
            }
            .function(&mut out);
        }
    }
    // what lowering promises: no pointer leads to the registers (and the
    // other fixed cells below the stack), and calls only go to functions
    let facts = asm::opt::Facts { private: 0..asm::STACK_BASE as i64, labels_only: true };
    Ok(if options.optimize { asm::opt::opt_with(out, &facts) } else { out })
}

/// Each function's plan.
fn plans(module: &Module) -> Vec<Plan> {
    let reach = reachable_functions(module);
    let taken = module.address_taken();
    module
        .funcs
        .iter()
        .enumerate()
        .map(|(i, f)| {
            // a call can come back into f if its callee can reach f, and an
            // indirect call can call any function whose address is taken
            let reenters = |node: &Node| match node {
                Node::Call(name, _) => {
                    let callee = module.index_of(name).unwrap();
                    callee == i || reach[callee][i]
                }
                Node::CallIndirect(..) => (0..taken.len()).any(|g| taken[g] && (g == i || reach[g][i])),
                _ => false,
            };
            Plan::new(f, &reenters)
        })
        .collect()
}

/// Which functions each function can reach through calls.
fn reachable_functions(module: &Module) -> Vec<Vec<bool>> {
    let callees = module.callees();
    (0..callees.len())
        .map(|start| {
            let mut seen = vec![false; callees.len()];
            let mut stack = callees[start].clone();
            while let Some(g) = stack.pop() {
                if !seen[g] {
                    seen[g] = true;
                    stack.extend(&callees[g]);
                }
            }
            seen
        })
        .collect()
}

/// Where every function's storage is, for callers to find their callees'
/// parameter cells.
struct Layout<'a> {
    module: &'a Module,
    plans: &'a [Plan],
    bases: &'a [u64],
    /// Which functions can be called indirectly.
    taken: &'a [bool],
    /// How many global cells there are, before the shared argument area.
    globals: u64,
    /// How many cells the shared argument area has.
    area: usize,
}

impl Layout<'_> {
    /// The shared area's cells, where indirect calls put their arguments.
    fn area_cells(&self) -> Vec<Location> {
        (0..self.area).map(|j| asm::reg(asm::STACK_BASE + self.globals + j as u64)).collect()
    }

    /// Where a caller puts each argument for `name`, if it uses it.
    fn param_cells(&self, name: &str) -> Vec<Option<Location>> {
        let i = self.module.index_of(name).unwrap();
        if self.taken[i] {
            return self.area_cells().into_iter().take(self.module.funcs[i].param_count()).map(Some).collect();
        }
        let (plan, base) = (&self.plans[i], self.bases[i]);
        let cell = |slot: usize| asm::reg(asm::STACK_BASE + base + slot as u64);
        self.module.funcs[i].blocks[0]
            .params
            .iter()
            .enumerate()
            .map(|(j, p)| match plan.home.get(p) {
                Some(Home::Static(s)) => Some(cell(*s)),
                Some(Home::Frame(_)) => Some(cell(plan.incoming[&j])),
                None => None,
            })
            .collect()
    }
}

/// The functions `main` can call, directly or not, from blocks that can run.
fn live_functions(module: &Module) -> Vec<bool> {
    let mut live = vec![false; module.funcs.len()];
    let mut stack = vec![0];
    while let Some(i) = stack.pop() {
        if live[i] {
            continue;
        }
        live[i] = true;
        let f = &module.funcs[i];
        for b in cfg::reverse_postorder(f) {
            for &e in &f.blocks[b.index()].effects {
                if let Node::Call(name, _) = &f.values[e.index()].node {
                    stack.push(module.index_of(name).unwrap());
                }
            }
        }
        stack.extend(f.addresses_taken().iter().map(|name| module.index_of(name).unwrap()));
    }
    live
}

fn is_var(f: &Function, v: Value) -> bool {
    f.values[v.index()].block.is_some()
}

/// Where a value lives: a fixed cell, or a cell of the stack frame.
#[derive(Clone, Copy, Debug, PartialEq)]
enum Home {
    Static(usize),
    Frame(usize),
}

/// How a function's values map to slots, and the order it computes them in.
struct Plan {
    /// The reachable blocks, in reverse postorder.
    blocks: Vec<Block>,
    /// Whether the blocks form a loop.
    cyclic: bool,
    schedule: Vec<Vec<Value>>,
    home: HashMap<Value, Home>,
    /// Where each alloca's cells start.
    region: HashMap<Value, Home>,
    /// Where the current block's number is kept, when dispatching.
    pc: Home,
    /// The fixed cell callers put each parameter kept in the frame in.
    incoming: HashMap<usize, usize>,
    /// How many fixed cells, and how many frame cells, the function needs.
    statics: usize,
    frame: usize,
    /// Each block's position in `blocks`.
    order: Vec<usize>,
    idom: Vec<Option<Block>>,
    /// Whether each block has more than one edge in, besides back edges.
    merge: Vec<bool>,
    /// The slot of each loop header's flag that runs it again.
    go: HashMap<Block, usize>,
    /// The slot holding which label a flagged break is going to.
    jump: usize,
    /// Whether every loop has a single entry, so control flow can be rebuilt.
    reducible: bool,
}

impl Plan {
    /// `reenters` says which calls can come back into `f`.
    fn new(f: &Function, reenters: &dyn Fn(&Node) -> bool) -> Plan {
        let blocks = cfg::reverse_postorder(f);
        let mut position = vec![usize::MAX; f.blocks.len()];
        for (i, b) in blocks.iter().enumerate() {
            position[b.index()] = i;
        }
        let cyclic = blocks
            .iter()
            .any(|&b| cfg::successors(f, b).iter().any(|s| position[s.index()] <= position[b.index()]));
        let mut needed = sched::needed(f, &blocks);
        // a global's address that's only loaded from and stored to needn't
        // be computed: those use the global's cell directly
        let direct = direct_globals(f, &needed);
        for (v, &d) in direct.iter().enumerate() {
            if d {
                needed[v] = false;
            }
        }
        let outside = sched::used_outside(f, &blocks, &needed);
        let pinned = f.pinned();
        let mut schedule = vec![vec![]; f.blocks.len()];
        for &b in &blocks {
            let mut order = sched::schedule(f, b, &needed, &outside, &pinned[b.index()]);
            order.retain(|v| !direct[v.index()]);
            schedule[b.index()] = order;
        }
        let live_in = liveness(f, &blocks, &schedule, &direct);
        let (statics, framed) = assign_slots(f, &blocks, &schedule, &live_in, reenters);
        let statics = by_use(f, &blocks, &schedule, statics);
        let framed = by_use(f, &blocks, &schedule, framed);

        let idom = cfg::dominators(f, &blocks);
        let mut merge = vec![false; f.blocks.len()];
        let mut forward = vec![0; f.blocks.len()];
        let mut headers = vec![];
        let mut reducible = true;
        for &b in &blocks {
            for s in cfg::successors(f, b) {
                if position[s.index()] > position[b.index()] {
                    forward[s.index()] += 1;
                    merge[s.index()] = forward[s.index()] > 1;
                } else {
                    reducible &= cfg::dominates(&idom, s, b);
                    if !headers.contains(&s) {
                        headers.push(s);
                    }
                }
            }
        }

        let mut home: HashMap<Value, Home> = statics.iter().map(|(&v, &s)| (v, Home::Static(s))).collect();
        home.extend(framed.iter().map(|(&v, &s)| (v, Home::Frame(s))));
        let mut fixed = statics.values().max().map_or(0, |&s| s + 1);
        let mut frame = framed.values().max().map_or(0, |&s| s + 1);
        let recursive = !framed.is_empty()
            || f.values.iter().any(|d| reenters(&d.node));

        // the block number is only needed to dispatch, and it has to survive
        // calls back into the function; the break flag is only needed when
        // there's more than one block
        let pc = if reducible {
            Home::Static(fixed)
        } else if recursive {
            frame += 1;
            Home::Frame(frame - 1)
        } else {
            fixed += 1;
            Home::Static(fixed - 1)
        };
        let jump = fixed;
        if blocks.len() > 1 || cyclic {
            fixed += 1;
        }
        let go: HashMap<Block, usize> = headers.iter().enumerate().map(|(i, &h)| (h, fixed + i)).collect();
        fixed += go.len();
        let mut incoming = HashMap::new();
        for (i, p) in f.blocks[0].params.iter().enumerate() {
            if matches!(home.get(p), Some(Home::Frame(_))) {
                incoming.insert(i, fixed);
                fixed += 1;
            }
        }
        // allocas belong to each call, so a recursive function's go in its frame
        let mut region = HashMap::new();
        for &b in &blocks {
            for &v in &schedule[b.index()] {
                if let Node::Alloca(cells) = f.values[v.index()].node {
                    if recursive {
                        region.insert(v, Home::Frame(frame));
                        frame += cells as usize;
                    } else {
                        region.insert(v, Home::Static(fixed));
                        fixed += cells as usize;
                    }
                }
            }
        }
        Plan {
            blocks,
            cyclic,
            schedule,
            home,
            region,
            pc,
            incoming,
            statics: fixed,
            frame,
            order: position,
            idom,
            merge,
            go,
            jump,
            reducible,
        }
    }
}

/// Which values are global addresses that only loads and stores (as the
/// address) use.
fn direct_globals(f: &Function, needed: &[bool]) -> Vec<bool> {
    let mut direct: Vec<bool> = f.values.iter().map(|d| matches!(d.node, Node::GlobalAddr(_))).collect();
    for (i, data) in f.values.iter().enumerate() {
        if !needed[i] {
            continue;
        }
        let ops = match &data.node {
            Node::Load(_) => vec![],
            Node::Store(_, x) => vec![*x],
            node => node.operands(),
        };
        for o in ops {
            direct[o.index()] = false;
        }
    }
    for block in &f.blocks {
        for o in block.term.iter().flat_map(|t| t.operands()) {
            direct[o.index()] = false;
        }
    }
    direct
}

/// The values live at the end of `b`: what its successors need besides their
/// own parameters, and what its terminator uses.
fn live_out(f: &Function, b: Block, live_in: &[HashSet<Value>]) -> HashSet<Value> {
    let mut live = HashSet::new();
    if let Some(t) = &f.blocks[b.index()].term {
        for target in t.targets() {
            let params = &f.blocks[target.block.index()].params;
            live.extend(live_in[target.block.index()].iter().filter(|v| !params.contains(v)));
        }
        live.extend(t.operands().into_iter().filter(|&v| is_var(f, v)));
    }
    live
}

/// The values live at the start of each block, including its parameters.
fn liveness(f: &Function, blocks: &[Block], schedule: &[Vec<Value>], direct: &[bool]) -> Vec<HashSet<Value>> {
    let mut live_in = vec![HashSet::new(); f.blocks.len()];
    loop {
        let mut changed = false;
        for &b in blocks.iter().rev() {
            let mut live = live_out(f, b, &live_in);
            for &v in schedule[b.index()].iter().rev() {
                live.remove(&v);
                live.extend(f.values[v.index()].node.operands().into_iter().filter(|&o| is_var(f, o) && !direct[o.index()]));
            }
            if live != live_in[b.index()] {
                live_in[b.index()] = live;
                changed = true;
            }
        }
        if !changed {
            return live_in;
        }
    }
}

/// Gives every value that's computed or received a slot, so that values live
/// at the same time get different slots. A node's result also never shares a
/// slot with its operands, since the helpers write their result before
/// they're done reading their operands. Parameters nothing reads get no slot,
/// and jumps don't pass them anything.
///
/// Values live across a call that can come back into the function go in its
/// frame, and the rest in fixed cells; each kind is numbered separately.
fn assign_slots(
    f: &Function,
    blocks: &[Block],
    schedule: &[Vec<Value>],
    live_in: &[HashSet<Value>],
    reenters: &dyn Fn(&Node) -> bool,
) -> (HashMap<Value, usize>, HashMap<Value, usize>) {
    let mut across: HashSet<Value> = HashSet::new();
    let mut graph: HashMap<Value, HashSet<Value>> = HashMap::new();
    let edge = |graph: &mut HashMap<Value, HashSet<Value>>, a: Value, b: Value| {
        graph.entry(a).or_default();
        graph.entry(b).or_default();
        if a != b {
            graph.get_mut(&a).unwrap().insert(b);
            graph.get_mut(&b).unwrap().insert(a);
        }
    };
    let mut order = vec![];
    for &b in blocks {
        // parameters are all written at the jump, so they interfere with
        // everything live into the block
        for &p in &f.blocks[b.index()].params {
            if live_in[b.index()].contains(&p) {
                order.push(p);
                for &x in &live_in[b.index()] {
                    edge(&mut graph, p, x);
                }
            }
        }
        let mut live = live_out(f, b, live_in);
        let mut defs = vec![];
        for &v in schedule[b.index()].iter().rev() {
            let node = &f.values[v.index()].node;
            let operands: Vec<Value> = node.operands().into_iter().filter(|&o| is_var(f, o)).collect();
            if reenters(node) {
                across.extend(live.iter().filter(|&&x| x != v));
            }
            if node.has_result() {
                defs.push(v);
                edge(&mut graph, v, v);
                for &x in live.iter().chain(&operands) {
                    edge(&mut graph, v, x);
                }
            }
            live.remove(&v);
            live.extend(operands);
        }
        order.extend(defs.into_iter().rev());
    }

    // values passed to a parameter prefer its slot, and the other way round,
    // which saves copying them at the jump
    let mut hints: HashMap<Value, Vec<Value>> = HashMap::new();
    for &b in blocks {
        for target in f.blocks[b.index()].term.iter().flat_map(|t| t.targets()) {
            for (&p, &a) in f.blocks[target.block.index()].params.iter().zip(&target.args) {
                if is_var(f, a) {
                    hints.entry(p).or_default().push(a);
                    hints.entry(a).or_default().push(p);
                }
            }
        }
    }

    let (mut statics, mut framed) = (HashMap::new(), HashMap::new());
    for v in order {
        let slot = if across.contains(&v) { &mut framed } else { &mut statics };
        let taken: HashSet<usize> = graph[&v].iter().filter_map(|n| slot.get(n).copied()).collect();
        let hinted = hints.get(&v).into_iter().flatten().filter_map(|h| slot.get(h).copied()).find(|s| !taken.contains(s));
        let s = hinted.unwrap_or_else(|| (0..).find(|s| !taken.contains(s)).unwrap());
        slot.insert(v, s);
    }
    (statics, framed)
}

/// Renumbers slots so the most used come first. They're then closest to the
/// scratch registers, and to each other, which makes moving between them
/// shorter.
fn by_use(f: &Function, blocks: &[Block], schedule: &[Vec<Value>], slot: HashMap<Value, usize>) -> HashMap<Value, usize> {
    let mut uses: HashMap<usize, usize> = HashMap::new();
    let mut count = |v: Value| {
        if let Some(&s) = slot.get(&v) {
            *uses.entry(s).or_default() += 1;
        }
    };
    for &b in blocks {
        for &v in &schedule[b.index()] {
            count(v);
            f.values[v.index()].node.operands().into_iter().for_each(&mut count);
        }
        f.blocks[b.index()].term.iter().flat_map(|t| t.operands()).for_each(&mut count);
    }
    let mut order: Vec<usize> = uses.keys().copied().collect();
    order.sort_by_key(|s| (std::cmp::Reverse(uses[s]), *s));
    let mut renumber: HashMap<usize, usize> = order.into_iter().enumerate().map(|(new, old)| (old, new)).collect();
    // slots nothing reads or writes in the code, like unused parameters', go last
    let mut next = renumber.len();
    let mut values: Vec<&Value> = slot.keys().collect();
    values.sort();
    for v in values {
        let s = slot[v];
        renumber.entry(s).or_insert_with(|| {
            next += 1;
            next - 1
        });
    }
    slot.into_iter().map(|(v, s)| (v, renumber[&s])).collect()
}

#[cfg(test)]
pub(super) fn frame_size(f: &Function) -> usize {
    let plan = Plan::new(f, &|_| false);
    plan.statics + plan.frame
}

enum Operand {
    Const(i64),
    Loc(Location),
}

struct Emitter<'a> {
    f: &'a Function,
    plan: &'a Plan,
    /// Where the function's fixed cells start, in the stack.
    base: u64,
    main: bool,
    ranges: &'a Ranges,
    /// The value acc holds, if the last thing emitted left one there.
    acc: Cell<Option<Value>>,
    layout: &'a Layout<'a>,
}

/// An open construct, while rebuilding structured control flow.
enum Frame {
    If,
    /// A loop that `header` heads; continuing it runs `header` again.
    Loop { header: Block, targeted: bool },
    /// A region that `follower` comes right after; breaking out of it goes
    /// there. `crossed` is set when a flagged break passes it on the way to
    /// somewhere further out, so the follower has to be skipped.
    Region { follower: Block, targeted: bool, crossed: bool },
}

impl Emitter<'_> {
    /// One of the function's fixed cells.
    fn cell(&self, slot: usize) -> Location {
        asm::reg(asm::STACK_BASE + self.base + slot as u64)
    }

    fn at(&self, home: Home) -> Location {
        match home {
            Home::Static(slot) => self.cell(slot),
            Home::Frame(slot) => asm::local(slot as i64),
        }
    }

    fn loc(&self, v: Value) -> Location {
        self.at(self.plan.home[&v])
    }

    fn operand(&self, v: Value) -> Operand {
        match self.f.values[v.index()].node {
            Node::Const(k) => Operand::Const(k),
            _ => Operand::Loc(self.loc(v)),
        }
    }

    /// Where `v` is, putting it in `scratch` first if it's a constant.
    fn materialize(&self, out: &mut dyn Program, v: Value, scratch: &Location) -> Location {
        match self.operand(v) {
            Operand::Const(k) => {
                asm::set_int(out, scratch, k);
                scratch.clone()
            }
            Operand::Loc(l) => l,
        }
    }

    /// The cell at the address `a` holds: a global's own cell, or else where
    /// the address points.
    fn address(&self, out: &mut dyn Program, a: Value) -> Location {
        match self.f.values[a.index()].node {
            Node::GlobalAddr(i) if !self.plan.home.contains_key(&a) => asm::reg(asm::STACK_BASE + i as u64),
            _ => self.materialize(out, a, R1).deref(),
        }
    }

    fn write(&self, out: &mut dyn Program, dst: &Location, v: Value) {
        match self.operand(v) {
            Operand::Const(k) => asm::set_int(out, dst, k),
            Operand::Loc(l) => asm::mov(out, dst, &l),
        }
    }

    fn dispatches(&self) -> bool {
        self.plan.blocks.len() > 1 || self.plan.cyclic
    }

    fn number(&self, b: Block) -> i64 {
        self.plan.blocks.iter().position(|&x| x == b).unwrap() as i64 + 1
    }

    fn function(&self, out: &mut dyn Program) {
        let framed = self.plan.frame > 0;
        if !self.main {
            out.op(asm::label(self.f.name()));
            out.op(Op::Func);
            if framed {
                asm::push(out, asm::FP);
                asm::mov(out, asm::FP, asm::SP);
                asm::alloc(out, self.plan.frame as i64);
            }
            // callers leave arguments in the parameters' cells, or for ones
            // kept in the frame, in a cell to copy them from; a function that
            // can be called indirectly gets them in the shared area
            let index = self.layout.module.index_of(self.f.name()).unwrap();
            let area = self.layout.area_cells();
            for (i, p) in self.f.blocks[0].params.iter().enumerate() {
                match self.plan.home.get(p) {
                    Some(_) if self.layout.taken[index] => asm::mov(out, &self.loc(*p), &area[i]),
                    Some(Home::Frame(_)) => asm::mov(out, &self.loc(*p), &self.cell(self.plan.incoming[&i])),
                    _ => {}
                }
            }
        }
        if self.plan.reducible {
            let entry = self.f.entry();
            if self.plan.blocks.len() > 1 {
                asm::set(out, &self.cell(self.plan.jump), 0);
            }
            self.tree(out, entry, &mut vec![]);
        } else {
            let pc = self.at(self.plan.pc);
            asm::set(out, &pc, 1);
            let sweep = |out: &mut dyn Program| {
                for (i, &b) in self.plan.blocks.iter().enumerate() {
                    // without loops, the entry always runs first, and only once
                    if i == 0 && !self.plan.cyclic {
                        self.block(out, b);
                        continue;
                    }
                    asm::mov(out, R2, &pc);
                    asm::eq_const(out, R2, i as i64 + 1);
                    asm::begin_if(out, R2);
                    self.block(out, b);
                    asm::end_if(out);
                }
            };
            if self.plan.cyclic {
                asm::while_loop(out, R3, |out| asm::mov(out, R3, &pc), sweep);
            } else {
                sweep(out);
            }
        }
        if self.plan.reducible && (self.plan.blocks.len() > 1 || self.plan.cyclic) {
            // a return can leave the break flag set, and a recursive caller
            // shares it
            asm::set(out, &self.cell(self.plan.jump), 0);
        }
        if !self.main {
            if framed {
                asm::mov(out, asm::SP, asm::FP);
                asm::pop(out, asm::FP);
            }
            out.op(Op::EndFunc);
        }
    }

    fn label(&self, b: Block) -> i64 {
        self.plan.order[b.index()] as i64 + 1
    }

    /// The label a return breaks to, past every other.
    fn return_label(&self) -> i64 {
        self.plan.blocks.len() as i64 + 1
    }

    /// Emits `x` and the part of the dominator tree under it.
    fn tree(&self, out: &mut dyn Program, x: Block, stack: &mut Vec<Frame>) {
        // the blocks x dominates that have several ways in come after it, the
        // latest in reverse postorder outermost
        let mut merges: Vec<Block> = self
            .plan
            .blocks
            .iter()
            .copied()
            .filter(|&b| b != x && self.plan.idom[b.index()] == Some(x) && self.plan.merge[b.index()])
            .collect();
        merges.sort_by_key(|b| std::cmp::Reverse(self.plan.order[b.index()]));
        match self.plan.go.get(&x) {
            Some(&go) => {
                let go = self.cell(go);
                asm::set(out, &go, 1);
                asm::load(out, &go);
                out.op(Op::While);
                asm::set(out, &go, 0);
                stack.push(Frame::Loop { header: x, targeted: false });
                self.within(out, x, &merges, stack);
                let Some(Frame::Loop { targeted, .. }) = stack.pop() else { unreachable!() };
                if targeted {
                    self.on_label(out, self.label(x), |out| asm::set(out, &go, 1));
                }
                asm::load(out, &go);
                out.op(Op::EndWhile);
            }
            None => self.within(out, x, &merges, stack),
        }
    }

    /// Runs `then` if a flagged break is going to `label`, clearing the flag.
    fn on_label(&self, out: &mut dyn Program, label: i64, then: impl FnOnce(&mut dyn Program)) {
        let jump = self.cell(self.plan.jump);
        asm::mov(out, R2, &jump);
        asm::eq_const(out, R2, label);
        asm::begin_if(out, R2);
        asm::set(out, &jump, 0);
        then(out);
        asm::end_if(out);
    }

    /// Emits `x` inside regions that end where each of `merges` begins.
    fn within(&self, out: &mut dyn Program, x: Block, merges: &[Block], stack: &mut Vec<Frame>) {
        if let Some((&follower, inner)) = merges.split_first() {
            stack.push(Frame::Region { follower, targeted: false, crossed: false });
            self.within(out, x, inner, stack);
            let Some(Frame::Region { targeted, crossed, .. }) = stack.pop() else { unreachable!() };
            if targeted {
                self.on_label(out, self.label(follower), |_| {});
            }
            if crossed {
                // skip the follower if a break is still on its way out
                asm::mov(out, R2, &self.cell(self.plan.jump));
                asm::lnot_assign(out, R2);
                asm::begin_if(out, R2);
            }
            self.tree(out, follower, stack);
            if crossed {
                asm::end_if(out);
            }
            return;
        }
        self.acc.set(None);
        for &v in &self.plan.schedule[x.index()] {
            self.inst(out, v);
        }
        match self.f.blocks[x.index()].term.as_ref().expect("verified") {
            Terminator::Return(v) => {
                if !self.main {
                    match v {
                        Some(v) => self.write(out, R0, *v),
                        None => asm::set(out, R0, 0),
                    }
                }
                if stack.iter().any(|frame| !matches!(frame, Frame::If)) {
                    asm::set_int(out, &self.cell(self.plan.jump), self.return_label());
                    for frame in stack.iter_mut() {
                        if let Frame::Region { crossed, .. } = frame {
                            *crossed = true;
                        }
                    }
                }
            }
            Terminator::Jump(t) => self.edge(out, x, t, stack),
            Terminator::Branch(c, t, e) => {
                let c = self.materialize(out, *c, R1);
                asm::begin_if(out, &c);
                stack.push(Frame::If);
                self.edge(out, x, t, stack);
                asm::begin_else(out);
                self.edge(out, x, e, stack);
                stack.pop();
                asm::end_if(out);
            }
        }
    }

    /// Follows the edge from `from` along `t`.
    fn edge(&self, out: &mut dyn Program, from: Block, t: &Target, stack: &mut Vec<Frame>) {
        self.copy_args(out, t);
        let to = t.block;
        if self.plan.order[to.index()] <= self.plan.order[from.index()] {
            let k = stack.iter().rposition(|f| matches!(f, Frame::Loop { header, .. } if *header == to));
            self.leave(out, k.expect("reducible"), stack);
        } else if self.plan.merge[to.index()] {
            let k = stack.iter().rposition(|f| matches!(f, Frame::Region { follower, .. } if *follower == to));
            self.leave(out, k.expect("a region ends at every merge"), stack);
        } else {
            self.tree(out, to, stack);
        }
    }

    /// Continues the loop, or breaks out of the region, that's `stack[k]`.
    fn leave(&self, out: &mut dyn Program, k: usize, stack: &mut [Frame]) {
        let crosses = stack[k + 1..].iter().any(|frame| !matches!(frame, Frame::If));
        if !crosses {
            // nothing runs between here and the end of stack[k]
            if let Frame::Loop { header, .. } = stack[k] {
                asm::set(out, &self.cell(self.plan.go[&header]), 1);
            }
            return;
        }
        let label = match &mut stack[k] {
            Frame::Loop { header, targeted } | Frame::Region { follower: header, targeted, .. } => {
                *targeted = true;
                self.label(*header)
            }
            Frame::If => unreachable!(),
        };
        asm::set_int(out, &self.cell(self.plan.jump), label);
        for frame in &mut stack[k + 1..] {
            if let Frame::Region { crossed, .. } = frame {
                *crossed = true;
            }
        }
    }

    fn copy_args(&self, out: &mut dyn Program, t: &Target) {
        let moves = self.f.blocks[t.block.index()]
            .params
            .iter()
            .zip(&t.args)
            .filter(|(p, _)| self.plan.home.contains_key(p))
            .map(|(p, &a)| (self.loc(*p), self.operand(a)))
            .collect();
        parallel_copy(out, moves);
    }

    fn block(&self, out: &mut dyn Program, b: Block) {
        self.acc.set(None);
        for &v in &self.plan.schedule[b.index()] {
            self.inst(out, v);
        }
        match self.f.blocks[b.index()].term.as_ref().expect("verified") {
            Terminator::Return(v) => {
                if !self.main {
                    match v {
                        Some(v) => self.write(out, R0, *v),
                        None => asm::set(out, R0, 0),
                    }
                }
                if self.dispatches() {
                    asm::set(out, &self.at(self.plan.pc), 0);
                }
            }
            Terminator::Jump(t) => self.goto(out, t),
            Terminator::Branch(c, t, e) => {
                let c = self.materialize(out, *c, R1);
                asm::begin_if(out, &c);
                self.goto(out, t);
                asm::begin_else(out);
                self.goto(out, e);
                asm::end_if(out);
            }
        }
    }

    fn goto(&self, out: &mut dyn Program, t: &Target) {
        self.copy_args(out, t);
        asm::set(out, &self.at(self.plan.pc), self.number(t.block) as u64);
    }

    /// Emits a pure node that only needs acc and its operands' cells as raw
    /// ops, starting from what acc already holds, and leaves its result in acc
    /// as well as its slot. Returns false for anything else.
    fn in_acc(&self, out: &mut dyn Program, v: Value, held: Option<Value>) -> bool {
        use BinOp::*;
        let data = &self.f.values[v.index()];
        let Some(block) = data.block else { return false };
        let is_const = |x: Value| self.f.const_value(x).is_some();
        // acc = x
        let load = |out: &mut dyn Program, x: Value| {
            if held != Some(x) {
                match self.operand(x) {
                    Operand::Const(k) => asm::set_acc(out, k),
                    Operand::Loc(l) => asm::load(out, &l),
                }
            }
        };
        // acc += x, for x in a cell
        let add = |out: &mut dyn Program, x: Value| {
            let l = self.loc(x);
            l.to(out);
            out.op(Op::Add);
            l.from(out);
        };
        // acc = x + k, for x in a cell
        let add_const = |out: &mut dyn Program, x: Value, k: i64| {
            let l = self.loc(x);
            l.to(out);
            asm::set_acc(out, k);
            out.op(Op::Add);
            l.from(out);
        };
        // acc = x - y
        let difference = |out: &mut dyn Program, x: Value, y: Value| match (self.f.const_value(x), self.f.const_value(y)) {
            (_, Some(k)) => add_const(out, x, k.wrapping_neg()),
            (Some(k), _) => {
                add_const(out, y, k.wrapping_neg());
                out.op(Op::Neg);
            }
            _ if held == Some(x) => {
                out.op(Op::Neg);
                add(out, y);
                out.op(Op::Neg);
            }
            _ => {
                load(out, y);
                out.op(Op::Neg);
                add(out, x);
            }
        };
        match data.node {
            Node::Binary(Add | Sub, a, b) if is_const(a) && is_const(b) => return false,
            Node::Binary(Add, a, b) if is_const(b) => add_const(out, a, self.f.const_value(b).unwrap()),
            Node::Binary(Add, a, b) if is_const(a) => add_const(out, b, self.f.const_value(a).unwrap()),
            Node::Binary(Add, a, b) => {
                if held == Some(b) {
                    add(out, a);
                } else {
                    load(out, a);
                    add(out, b);
                }
            }
            Node::Binary(Sub, a, b) => difference(out, a, b),
            Node::Unary(UnOp::Neg, a) if !is_const(a) => {
                load(out, a);
                out.op(Op::Neg);
            }
            Node::Unary(UnOp::Not, a) if !is_const(a) => {
                add_const(out, a, 1);
                out.op(Op::Neg);
            }
            Node::Binary(Mul, a, b) if !is_const(a) && self.f.const_value(b).is_some_and(|k| (2..=8).contains(&k.abs())) => {
                let k = self.f.const_value(b).unwrap();
                let l = self.loc(a);
                l.to(out);
                out.op(Op::Load);
                for _ in 1..k.abs() {
                    out.op(Op::Add);
                }
                l.from(out);
                if k < 0 {
                    out.op(Op::Neg);
                }
            }
            Node::Binary(op @ (Lt | Le | Gt | Ge), a, b)
                if self.ranges.width.difference_fits(self.ranges.at(a, block), self.ranges.at(b, block)) =>
            {
                // a < b is b - a > 0, and a <= b is not a - b > 0
                let (x, y) = if matches!(op, Lt | Ge) { (b, a) } else { (a, b) };
                difference(out, x, y);
                out.op(Op::Positive);
                if matches!(op, Le | Ge) {
                    let dst = self.loc(v);
                    dst.to(out);
                    out.op(Op::Neg);
                    out.op(Op::Store);
                    out.op(Op::Set(1));
                    out.op(Op::Add);
                    dst.from(out);
                }
            }
            _ => return false,
        }
        asm::store(out, &self.loc(v));
        self.acc.set(Some(v));
        true
    }

    fn inst(&self, out: &mut dyn Program, v: Value) {
        let held = self.acc.take();
        if self.in_acc(out, v, held) {
            return;
        }
        let dst = || self.loc(v);
        match &self.f.values[v.index()].node {
            Node::Const(_) | Node::Param(..) => unreachable!("never scheduled"),
            Node::Unary(op, a) => {
                let dst = dst();
                self.write(out, &dst, *a);
                match op {
                    UnOp::Neg => asm::neg_assign(out, &dst),
                    UnOp::Not => asm::not_assign(out, &dst),
                    UnOp::LNot => asm::lnot_assign(out, &dst),
                    UnOp::Abs => asm::abs_assign(out, &dst),
                }
            }
            Node::Binary(op, a, b) => {
                let block = self.f.values[v.index()].block.unwrap();
                let (ra, rb) = (self.ranges.at(*a, block), self.ranges.at(*b, block));
                self.binary(out, &dst(), *op, (*a, ra), (*b, rb))
            }
            Node::Load(a) => {
                let p = self.address(out, *a);
                asm::mov(out, &dst(), &p);
                self.acc.set(Some(v));
            }
            Node::Store(a, x) => {
                let p = self.address(out, *a);
                self.write(out, &p, *x);
            }
            Node::Call(name, args) => {
                let moves = self
                    .layout
                    .param_cells(name)
                    .into_iter()
                    .zip(args)
                    .filter_map(|(cell, &a)| cell.map(|cell| (cell, self.operand(a))))
                    .collect();
                parallel_copy(out, moves);
                out.op(asm::label(name));
                out.op(Op::Call);
                if self.plan.home.contains_key(&v) {
                    asm::mov(out, &dst(), R0);
                    self.acc.set(Some(v));
                }
            }
            Node::FuncAddr(name) => {
                out.op(asm::label(name));
                asm::store(out, &dst());
                self.acc.set(Some(v));
            }
            // an external function is called the way the VM calls one: with
            // its arguments in the cells from R1 up, and the pointer at R1;
            // it leaves its result in acc
            Node::CallExtern(name, args) => {
                const R1_CELL: u64 = 20;
                let moves = args.iter().enumerate().map(|(i, &a)| (asm::reg(R1_CELL + i as u64), self.operand(a))).collect();
                parallel_copy(out, moves);
                R1.to(out);
                out.op(asm::external_label(name));
                out.op(Op::Call);
                R1.from(out);
                if self.plan.home.contains_key(&v) {
                    asm::store(out, &dst());
                    self.acc.set(Some(v));
                }
            }
            Node::CallIndirect(g, args) => {
                let moves = self.layout.area_cells().into_iter().zip(args).map(|(cell, &a)| (cell, self.operand(a))).collect();
                parallel_copy(out, moves);
                let g = self.materialize(out, *g, R1);
                asm::load(out, &g);
                out.op(Op::Call);
                if self.plan.home.contains_key(&v) {
                    asm::mov(out, &dst(), R0);
                    self.acc.set(Some(v));
                }
            }
            Node::GetChar => asm::getchar(out, &dst()),
            Node::GetInt => asm::getint(out, &dst()),
            Node::PutChar(x) => {
                let x = self.materialize(out, *x, R1);
                asm::putchar(out, &x);
            }
            Node::PutInt(x) => {
                let x = self.materialize(out, *x, R1);
                asm::putint(out, &x);
            }
            Node::PutUInt(x) => {
                let x = self.materialize(out, *x, R1);
                asm::putuint(out, &x);
            }
            Node::Puts(s) => asm::puts(out, s),
            Node::HeapAlloc(n) => match self.operand(*n) {
                Operand::Const(k) => asm::heap_alloc_const(out, &dst(), k),
                Operand::Loc(l) => asm::heap_alloc(out, &dst(), &l),
            },
            Node::Alloca(_) => asm::addr_of(out, &dst(), &self.at(self.plan.region[&v])),
            Node::GlobalAddr(i) => asm::addr_of(out, &dst(), &asm::reg(asm::STACK_BASE + *i as u64)),
            Node::Intrinsic(which, args) => match which {
                Intrinsic::StackPointer => asm::mov(out, &dst(), asm::SP),
                Intrinsic::HeapPointer => asm::mov(out, &dst(), asm::GP),
                Intrinsic::SetHeapPointer => self.write(out, asm::GP, args[0]),
                Intrinsic::RootsStart => asm::addr_of(out, &dst(), &asm::reg(asm::STACK_BASE + self.layout.globals)),
            },
            Node::GcAlloc(_) | Node::Abort => unreachable!("replaced before lowering"),
        }
    }

    fn binary(&self, out: &mut dyn Program, dst: &Location, op: BinOp, (a, ra): (Value, Range), (b, rb): (Value, Range)) {
        use BinOp::*;
        // comparisons of values whose difference fits in 16 bits
        if matches!(op, Lt | Le | Gt | Ge) && self.ranges.width.difference_fits(ra, rb) {
            self.write(out, dst, a);
            match (self.operand(b), op) {
                (Operand::Const(k), Lt) => asm::lt_const_small(out, dst, k),
                (Operand::Const(k), Le) => asm::le_const_small(out, dst, k),
                (Operand::Const(k), Gt) => asm::gt_const_small(out, dst, k),
                (Operand::Const(k), _) => asm::ge_const_small(out, dst, k),
                (Operand::Loc(l), Lt) => asm::lt_small(out, dst, &l),
                (Operand::Loc(l), Le) => asm::le_small(out, dst, &l),
                (Operand::Loc(l), Gt) => asm::gt_small(out, dst, &l),
                (Operand::Loc(l), _) => asm::ge_small(out, dst, &l),
            }
            return;
        }
        // dividing by a value known to be small and positive
        let small_divisor = rb.at_least(1) && rb.at_most((1 << 14) - 1);
        if matches!(op, Div | Rem | DivU | RemU) && self.f.const_value(b).is_none() && small_divisor {
            self.write(out, dst, a);
            let d = self.materialize(out, b, R1);
            match op {
                Div => asm::div_small_assign(out, dst, &d),
                Rem => asm::rem_small_assign(out, dst, &d),
                DivU => asm::divu_small_assign(out, dst, &d),
                _ => asm::remu_small_assign(out, dst, &d),
            }
            return;
        }
        // multiplying by a small number, by adding repeatedly
        let small = |r: Range| r.at_least(0) && r.at_most(32);
        if op == Mul && self.f.const_value(b).is_none() && (small(rb) || small(ra)) {
            let (x, count) = if small(rb) { (a, b) } else { (b, a) };
            self.write(out, dst, x);
            let count = self.materialize(out, count, R1);
            asm::mul_small_assign(out, dst, &count);
            return;
        }
        if op == BinOp::Index {
            let base = self.materialize(out, a, R1);
            match self.operand(b) {
                Operand::Const(k) => asm::addr_of(out, dst, &base.deref().offset(k)),
                Operand::Loc(i) => asm::index(out, dst, &base, &i),
            }
            return;
        }
        self.write(out, dst, a);
        if let (Operand::Const(k), Some(with_const)) = (self.operand(b), const_form(op)) {
            with_const(out, dst, k);
            return;
        }
        let b = self.materialize(out, b, R1);
        assign_form(op)(out, dst, &b);
    }
}

type AssignFn = fn(&mut dyn Program, &Location, &Location);
type ConstFn = fn(&mut dyn Program, &Location, i64);

fn assign_form(op: BinOp) -> AssignFn {
    use BinOp::*;
    match op {
        Add => asm::add_assign,
        Sub => asm::sub_assign,
        Mul => asm::mul_assign,
        Div => asm::div_assign,
        Rem => asm::rem_assign,
        DivU => asm::divu_assign,
        RemU => asm::remu_assign,
        And => asm::and_assign,
        Or => asm::or_assign,
        Xor => asm::xor_assign,
        Shl => asm::lsh_assign,
        Shr => asm::rsh_assign,
        ShrU => asm::rshu_assign,
        Eq => asm::eq_assign,
        Ne => asm::ne_assign,
        Lt => asm::lt_assign,
        Le => asm::le_assign,
        Gt => asm::gt_assign,
        Ge => asm::ge_assign,
        LtU => asm::ltu_assign,
        LeU => asm::leu_assign,
        GtU => asm::gtu_assign,
        GeU => asm::geu_assign,
        Min => asm::min_assign,
        Max => asm::max_assign,
        Index => unreachable!("lowered separately"),
    }
}

/// The helper that takes the right operand as a constant, if there is one.
fn const_form(op: BinOp) -> Option<ConstFn> {
    use BinOp::*;
    Some(match op {
        Add => asm::add_const,
        Sub => asm::sub_const,
        Mul => asm::mul_const,
        Div => asm::div_const,
        Rem => asm::rem_const,
        DivU => asm::divu_const,
        RemU => asm::remu_const,
        And => asm::and_const,
        Or => asm::or_const,
        Xor => asm::xor_const,
        Shl => asm::lsh_const,
        Shr => asm::rsh_const,
        ShrU => asm::rshu_const,
        Eq => asm::eq_const,
        Ne => asm::ne_const,
        Lt => asm::lt_const,
        Le => asm::le_const,
        Gt => asm::gt_const,
        Ge => asm::ge_const,
        _ => return None,
    })
}

/// Makes all the moves as if at once, though some read cells that others
/// write: each move goes once nothing still needs its destination, and a cycle
/// of moves is broken by saving one destination in a scratch cell.
fn parallel_copy(out: &mut dyn Program, mut moves: Vec<(Location, Operand)>) {
    let reads = |moves: &[(Location, Operand)], d: &Location| {
        moves.iter().any(|(_, s)| matches!(s, Operand::Loc(l) if l == d))
    };
    moves.retain(|(d, s)| !matches!(s, Operand::Loc(l) if l == d));
    while !moves.is_empty() {
        if let Some(i) = (0..moves.len()).find(|&i| !reads(&moves, &moves[i].0)) {
            let (d, s) = moves.remove(i);
            match s {
                Operand::Const(k) => asm::set_int(out, &d, k),
                Operand::Loc(l) => asm::mov(out, &d, &l),
            }
        } else {
            // only cycles are left; R1 is free again by now, since a broken
            // cycle unwinds completely before another is broken
            let d = moves[0].0.clone();
            asm::mov(out, R1, &d);
            for (_, s) in &mut moves {
                if matches!(s, Operand::Loc(l) if *l == d) {
                    *s = Operand::Loc(R1.clone());
                }
            }
        }
    }
}
