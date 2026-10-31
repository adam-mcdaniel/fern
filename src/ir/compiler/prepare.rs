//! Getting a module ready to lower, on a copy of it:
//!
//! - if it allocates with `gc_alloc`, adding the garbage collector, and
//!   calling it instead,
//! - with checks on, stopping with a message when the stack and the heap
//!   would run into each other: at the start of each recursive function
//!   (only those have stack frames) and after each `heap_alloc`,
//! - turning `abort` into returns. The VM can't stop in the middle of a call,
//!   so an abort sets a global flag and returns, and every call to a
//!   function that can abort is followed by a check of the flag that returns
//!   too, until `main` does, which ends the program. Or, with `exits`, into
//!   a call to the external function `bf_exit` (`EXIT`), which stops the
//!   program then and there, with a status of 1 (the C backends define it,
//!   and the interpreter has it).

use super::{gc, interproc, opt, Block, Contents, Function, Intrinsic, Module, Node, Value};
use crate::asm::fx::HashSet;

/// The external function an abort calls, with `exits`: it stops the
/// program, with the status it's given.
pub const EXIT: &str = "bf_exit";

pub(in crate::ir) fn prepare(module: &Module, checks: bool, exits: bool, max_frame: impl Fn(&Module) -> usize) -> Result<Module, String> {
    let mut m = module.clone();
    add_gc(&mut m)?;
    if checks {
        // room for the biggest stack frame, past the stack pointer
        let margin = max_frame(&m) as i64 + 8;
        let recursive = m.recursive();
        for (i, f) in m.funcs.iter_mut().enumerate() {
            let main = i == 0;
            if recursive[i] {
                let entry = f.entry();
                let rest = split(f, entry, 0);
                f.switch_to(entry);
                let sp = f.intrinsic(Intrinsic::StackPointer, &[]);
                let hp = f.intrinsic(Intrinsic::HeapPointer, &[]);
                let k = f.int(margin);
                // addresses are small and positive, so the sign of their
                // difference compares them, far more cheaply than `<` can,
                // and `> 0` is the cheapest test of sign
                let limit = f.index(sp, k);
                let short = f.sub(limit, hp);
                let zero = f.int(0);
                let bad = f.gt(short, zero);
                let fail = failure(f, "stack overflow\n", main);
                f.switch_to(entry);
                f.branch(bad, fail, &[], rest, &[]);
            }
            for b in f.reachable_blocks() {
                let mut b = b;
                let mut i = 0;
                while i < f.blocks[b.index()].effects.len() {
                    let e = f.blocks[b.index()].effects[i];
                    if !matches!(f.values[e.index()].node, Node::HeapAlloc(_)) {
                        i += 1;
                        continue;
                    }
                    let rest = split(f, b, i + 1);
                    f.switch_to(b);
                    let sp = f.intrinsic(Intrinsic::StackPointer, &[]);
                    let hp = f.intrinsic(Intrinsic::HeapPointer, &[]);
                    let k = f.int(margin);
                    let limit = f.index(sp, k);
                    let short = f.sub(limit, hp);
                    let zero = f.int(0);
                    let bad = f.gt(short, zero);
                    let fail = failure(f, "out of memory\n", main);
                    f.switch_to(b);
                    f.branch(bad, fail, &[], rest, &[]);
                    b = rest;
                    i = 0;
                }
            }
        }
    }
    if exits {
        call_exit(&mut m);
    } else {
        lower_aborts(&mut m);
    }
    for f in &mut m.funcs {
        f.rebuild_dedup();
    }
    Ok(m)
}

/// If `m` allocates with `gc_alloc`, the garbage collector added to it, and
/// called instead (before `main` does anything else, it's set up).
fn add_gc(m: &mut Module) -> Result<(), String> {
    let uses_gc = m.funcs.iter().any(|f| f.values.iter().any(|d| matches!(d.node, Node::GcAlloc(..))));
    if uses_gc {
        if let Some(f) = m.funcs.iter().find(|f| f.name.starts_with("_gc")) {
            return Err(format!("{} is a name the garbage collector uses", f.name));
        }
        // each small constant size gets its own allocator (small objects of
        // numbers are scanned like any others: it costs little), and any
        // other size the general one, or the one for numbers
        let mut sizes: Vec<i64> = vec![];
        let (mut any, mut any_data) = (false, false);
        for f in &m.funcs {
            for data in &f.values {
                if let Node::GcAlloc(n, contents) = data.node {
                    match f.const_value(n).map(|k| k.max(1)).filter(|&k| gc::alloc_of(k).is_some()) {
                        Some(k) if !sizes.contains(&k) => sizes.push(k),
                        Some(_) => {}
                        None if contents == Contents::Data => any_data = true,
                        None => any = true,
                    }
                }
            }
        }
        sizes.sort();
        gc::add(m, &sizes, any, any_data);
        let effects = interproc::effects(m);
        for f in m.funcs.iter_mut().filter(|f| f.name.starts_with("_gc")) {
            opt::simplify(f, &effects);
            f.rebuild_dedup();
        }
        for f in &mut m.funcs {
            for i in 0..f.values.len() {
                if let Node::GcAlloc(n, contents) = f.values[i].node {
                    f.values[i].node = match f.const_value(n).and_then(|k| gc::alloc_of(k.max(1))) {
                        Some(name) => Node::Call(name, vec![]),
                        None if contents == Contents::Data => Node::Call(gc::ALLOC_DATA.to_string(), vec![n]),
                        None => Node::Call(gc::ALLOC.to_string(), vec![n]),
                    };
                }
            }
        }
        let init = m.funcs[0].push(Node::Call(gc::INIT.to_string(), vec![]), Some(Block(0)));
        m.funcs[0].blocks[0].effects.insert(0, init);
    }
    Ok(())
}

/// A block that prints `message` and aborts.
fn failure(f: &mut Function, message: &str, main: bool) -> Block {
    let fail = f.new_block(0);
    f.switch_to(fail);
    f.puts(message);
    f.abort();
    give_up(f, main);
    fail
}

/// Returns, with 0 unless from `main`.
fn give_up(f: &mut Function, main: bool) {
    if main {
        f.ret_void();
    } else {
        let zero = f.int(0);
        f.ret(zero);
    }
}

/// Moves `b`'s effects from the `i`th on, and its terminator, to a new
/// block, leaving `b` without a terminator. Pure nodes of `b` that only what
/// moves uses move with it: so they aren't computed on a path that stops,
/// where they may not make sense (the address of a field of a null pointer,
/// say, which the lowered code can't compute).
fn split(f: &mut Function, b: Block, i: usize) -> Block {
    let c = f.new_block(0);
    let moved = f.blocks[b.index()].effects.split_off(i);
    let term = f.blocks[b.index()].term.take();
    for &e in &moved {
        f.values[e.index()].block = Some(c);
    }
    // the pure nodes the effects staying in b need, directly or not, stay
    let mut stay: HashSet<Value> = HashSet::default();
    let mut work: Vec<Value> = f.blocks[b.index()].effects.iter().flat_map(|&e| f.values[e.index()].node.operands()).collect();
    while let Some(v) = work.pop() {
        let data = &f.values[v.index()];
        if data.block == Some(b) && data.node.is_pure() && stay.insert(v) {
            work.extend(data.node.operands());
        }
    }
    for v in 0..f.values.len() {
        let data = &f.values[v];
        if data.block == Some(b) && data.node.is_pure() && !matches!(data.node, Node::Param(..)) && !stay.contains(&Value(v as u32)) {
            f.values[v].block = Some(c);
        }
    }
    f.blocks[c.index()].effects = moved;
    f.blocks[c.index()].term = term;
    c
}

/// Which functions can abort, themselves or through what they call.
fn may_abort(m: &Module) -> Vec<bool> {
    let mut may: Vec<bool> = m
        .funcs
        .iter()
        .map(|f| {
            f.reachable_blocks()
                .iter()
                .flat_map(|b| &f.blocks[b.index()].effects)
                .any(|e| matches!(f.values[e.index()].node, Node::Abort))
        })
        .collect();
    let callees = m.callees();
    loop {
        let mut changed = false;
        for (i, calls) in callees.iter().enumerate() {
            if !may[i] && calls.iter().any(|&c| may[c]) {
                may[i] = true;
                changed = true;
            }
        }
        if !changed {
            return may;
        }
    }
}

/// Each abort a call to `EXIT`, with 1: it never returns, so what follows it
/// never runs, and nothing else has to change.
fn call_exit(m: &mut Module) {
    if !m.funcs.iter().any(|f| f.values.iter().any(|d| matches!(d.node, Node::Abort))) {
        return;
    }
    m.external(EXIT);
    for f in &mut m.funcs {
        let aborts: Vec<usize> = (0..f.values.len()).filter(|&i| matches!(f.values[i].node, Node::Abort)).collect();
        if aborts.is_empty() {
            continue;
        }
        let one = f.int(1);
        for i in aborts {
            f.values[i].node = Node::CallExtern(EXIT.to_string(), vec![one]);
        }
    }
}

fn lower_aborts(m: &mut Module) {
    let may = may_abort(m);
    if !may.iter().any(|&x| x) {
        return;
    }
    let flag = m.add_globals(1);
    let taken = m.address_taken();
    let indirect = (0..m.funcs.len()).any(|i| taken[i] && may[i]);
    let index: std::collections::HashMap<String, usize> =
        m.funcs.iter().enumerate().map(|(i, f)| (f.name.clone(), i)).collect();
    for (fi, f) in m.funcs.iter_mut().enumerate() {
        if !may[fi] {
            continue;
        }
        let main = fi == 0;
        for b in f.reachable_blocks() {
            let mut b = b;
            let mut i = 0;
            while i < f.blocks[b.index()].effects.len() {
                let e = f.blocks[b.index()].effects[i];
                match &f.values[e.index()].node {
                    Node::Abort => {
                        // nothing after the abort runs: what it defined
                        // becomes 0 for any pure node that still uses it
                        let dropped = f.blocks[b.index()].effects.split_off(i);
                        for d in dropped {
                            f.values[d.index()].node = Node::Const(0);
                            f.values[d.index()].block = None;
                        }
                        f.blocks[b.index()].term = None;
                        f.switch_to(b);
                        let at = f.global_addr(flag);
                        let one = f.int(1);
                        f.store(at, one);
                        give_up(f, main);
                        break;
                    }
                    Node::Call(name, _) if may[index[name]] => {}
                    Node::CallIndirect(..) if indirect => {}
                    _ => {
                        i += 1;
                        continue;
                    }
                }
                let rest = split(f, b, i + 1);
                f.switch_to(b);
                let at = f.global_addr(flag);
                let stopping = f.load(at);
                let stop = f.new_block(0);
                f.branch(stopping, stop, &[], rest, &[]);
                f.switch_to(stop);
                give_up(f, main);
                b = rest;
                i = 0;
            }
        }
    }
}
