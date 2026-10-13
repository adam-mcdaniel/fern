//! Optimizations across functions: what each function can do to memory,
//! dropping parameters and results nothing uses, and copies of functions
//! specialized for constant arguments.

use super::opt::replace_uses;
use super::{cfg, sched, BinOp, Function, Module, Node, Terminator, Value};
use std::collections::HashMap;

/// What calling a function can do, besides computing its result.
#[derive(Clone, Copy, Debug, Default, PartialEq)]
pub(super) struct Effects {
    /// It can read memory its caller can reach.
    pub(super) reads: bool,
    /// It can write memory its caller can reach.
    pub(super) writes: bool,
    /// It reads input, writes output, or allocates on the heap, so calling
    /// it twice isn't the same as calling it once.
    pub(super) other: bool,
}

impl Effects {
    /// Whether a call is just its result: it can be dropped if that's unused,
    /// and two calls with the same arguments give the same result.
    pub(super) fn pure(self) -> bool {
        self == Effects::default()
    }

    /// What an unknown function could do.
    pub(super) fn any() -> Effects {
        Effects { reads: true, writes: true, other: true }
    }
}

/// The effects of each function, including through the functions it calls.
pub(super) fn effects(module: &Module) -> HashMap<String, Effects> {
    let callees = module.callees();
    let mut effects: Vec<Effects> = module.funcs.iter().map(local_effects).collect();
    loop {
        let mut changed = false;
        for (i, calls) in callees.iter().enumerate() {
            for &c in calls {
                let theirs = effects[c];
                let mine = &mut effects[i];
                let joined = Effects {
                    reads: mine.reads | theirs.reads,
                    writes: mine.writes | theirs.writes,
                    other: mine.other | theirs.other,
                };
                if joined != *mine {
                    *mine = joined;
                    changed = true;
                }
            }
        }
        if !changed {
            break;
        }
    }
    // an indirect call can do whatever any function it could call does,
    // listed under the empty name
    let taken = module.address_taken();
    let mut indirect = Effects::default();
    for (i, e) in effects.iter().enumerate() {
        if taken[i] {
            indirect = Effects { reads: indirect.reads | e.reads, writes: indirect.writes | e.writes, other: indirect.other | e.other };
        }
    }
    let mut map: HashMap<String, Effects> = module.funcs.iter().zip(effects).map(|(f, e)| (f.name.clone(), e)).collect();
    map.insert(String::new(), indirect);
    map
}

/// A function's own effects, not counting its calls. Memory only it can
/// reach, its own allocas whose address never escapes, doesn't count.
fn local_effects(f: &Function) -> Effects {
    let live = cfg::reverse_postorder(f);
    let escaped = super::memory::escaping(f, &live);
    let private = |addr: Value| super::memory::private_alloca(f, addr, &escaped);
    let mut effects = Effects::default();
    for &b in &live {
        for &e in &f.blocks[b.index()].effects {
            match &f.values[e.index()].node {
                Node::Load(a) if !private(*a) => effects.reads = true,
                Node::Store(a, _) if !private(*a) => effects.writes = true,
                Node::Load(_) | Node::Store(..) | Node::Call(..) | Node::CallIndirect(..) | Node::Alloca(_) => {}
                Node::CallExtern(..) => effects = Effects::any(),
                _ => effects.other = true,
            }
        }
    }
    effects
}

/// Drops parameters a function never uses, and the matching argument from
/// every call; and the results of functions whose callers all ignore them.
pub(super) fn dead_arguments(module: &mut Module) -> bool {
    let mut changed = false;
    // indirect calls pass every argument, and may use any result
    let taken = module.address_taken();
    for i in 1..module.funcs.len() {
        if taken[i] {
            continue;
        }
        let f = &module.funcs[i];
        let blocks = cfg::reverse_postorder(f);
        let needed = sched::needed(f, &blocks);
        let unused: Vec<usize> =
            f.blocks[0].params.iter().enumerate().filter(|(_, p)| !needed[p.index()]).map(|(j, _)| j).collect();
        if unused.is_empty() {
            continue;
        }
        let name = f.name.clone();
        let f = &mut module.funcs[i];
        let params = std::mem::take(&mut f.blocks[0].params);
        f.blocks[0].params = params.into_iter().enumerate().filter(|(j, _)| !unused.contains(j)).map(|(_, p)| p).collect();
        for (j, p) in f.blocks[0].params.clone().into_iter().enumerate() {
            f.values[p.index()].node = Node::Param(f.entry(), j);
        }
        for g in &mut module.funcs {
            for data in &mut g.values {
                if let Node::Call(callee, args) = &mut data.node {
                    if *callee == name {
                        *args = std::mem::take(args).into_iter().enumerate().filter(|(j, _)| !unused.contains(j)).map(|(_, a)| a).collect();
                    }
                }
            }
        }
        changed = true;
    }

    // results nobody uses
    let mut used: HashMap<String, bool> = HashMap::new();
    for g in &module.funcs {
        let mut uses = vec![false; g.values.len()];
        for data in &g.values {
            data.node.operands().into_iter().for_each(|o| uses[o.index()] = true);
        }
        for block in &g.blocks {
            block.term.iter().flat_map(|t| t.operands()).for_each(|o| uses[o.index()] = true);
        }
        for (v, data) in g.values.iter().enumerate() {
            if let Node::Call(callee, _) = &data.node {
                *used.entry(callee.clone()).or_default() |= uses[v];
            }
        }
    }
    for (i, f) in module.funcs.iter_mut().enumerate().skip(1) {
        if !taken[i] && used.get(&f.name) == Some(&false) {
            for block in &mut f.blocks {
                if let Some(Terminator::Return(v @ Some(_))) = &mut block.term {
                    *v = None;
                    changed = true;
                }
            }
        }
    }
    changed
}

/// The most copies made of any one function.
const MAX_COPIES: usize = 4;
/// Functions bigger than this (in values) aren't copied.
const MAX_SIZE: usize = 150;

/// Makes copies of functions for calls that pass them constants, with the
/// constants in place of the parameters, where the constant feeds an
/// operation it makes cheaper. The copies' unused parameters go once
/// `dead_arguments` runs.
pub(super) fn specialize(module: &mut Module) -> bool {
    let recursive = module.recursive();
    let mut copies: HashMap<(usize, Vec<Option<i64>>), String> = HashMap::new();
    let mut made = vec![0; module.funcs.len()];
    let mut changed = false;
    for caller in 0..module.funcs.len() {
        let sites: Vec<(Value, usize, Vec<Option<i64>>)> = {
            let f = &module.funcs[caller];
            cfg::reverse_postorder(f)
                .into_iter()
                .flat_map(|b| f.blocks[b.index()].effects.clone())
                .filter_map(|e| match &f.values[e.index()].node {
                    Node::Call(name, args) => {
                        let callee = module.index_of(name).unwrap();
                        let constants: Vec<Option<i64>> = args.iter().map(|&a| f.const_value(a)).collect();
                        Some((e, callee, constants))
                    }
                    _ => None,
                })
                .collect()
        };
        for (site, callee, constants) in sites {
            if callee == 0 || recursive[callee] || !worth_specializing(&module.funcs[callee], &constants) {
                continue;
            }
            let key = (callee, constants.clone());
            let name = match copies.get(&key) {
                Some(name) => name.clone(),
                None => {
                    if made[callee] >= MAX_COPIES {
                        continue;
                    }
                    made[callee] += 1;
                    let base = &module.funcs[callee].name;
                    let name = (1..)
                        .map(|n| format!("{}_{n}", &base[..base.len().min(10)]))
                        .find(|name| module.index_of(name).is_none())
                        .unwrap();
                    let mut copy = module.funcs[callee].clone();
                    copy.name = name.clone();
                    let mut map = HashMap::new();
                    for (j, k) in constants.iter().enumerate() {
                        if let Some(k) = k {
                            let p = copy.blocks[0].params[j];
                            let c = copy.int(*k);
                            map.insert(p, c);
                        }
                    }
                    replace_uses(&mut copy, &map);
                    copy.rebuild_dedup();
                    module.funcs.push(copy);
                    made.push(MAX_COPIES);
                    copies.insert(key, name.clone());
                    name
                }
            };
            if let Node::Call(callee_name, _) = &mut module.funcs[caller].values[site.index()].node {
                *callee_name = name;
            }
            changed = true;
        }
    }
    changed
}

/// Whether a constant argument feeds something it would make cheaper.
fn worth_specializing(f: &Function, constants: &[Option<i64>]) -> bool {
    if f.values.len() > MAX_SIZE {
        return false;
    }
    let params = &f.blocks[0].params;
    let constant = |v: Value| params.iter().position(|&p| p == v).is_some_and(|j| constants[j].is_some());
    let cheaper = f.values.iter().any(|data| match &data.node {
        Node::Binary(op, a, b) => {
            use BinOp::*;
            matches!(op, Mul | Div | Rem | DivU | RemU | And | Or | Xor | Shl | Shr | ShrU | Lt | Le | Gt | Ge | LtU | LeU | GtU | GeU)
                && (constant(*a) || constant(*b))
        }
        _ => false,
    });
    let branches = f.blocks.iter().any(|b| matches!(&b.term, Some(Terminator::Branch(c, ..)) if constant(*c)));
    cheaper || branches
}
