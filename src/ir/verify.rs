//! Checking that a module is well formed.

use super::{cfg, Block, Function, Intrinsic, Module, Node, Value};
use crate::asm::fx::HashSet;

/// Checks that:
///
/// - function names are unique and fit asm's labels,
/// - every reachable block ends in a terminator,
/// - jumps pass as many arguments as their target takes,
/// - calls name a function other than `main` and pass as many arguments as it
///   takes, at most 9 of them constants,
/// - global cells exist, and intrinsics have the right number of operands,
/// - a module doesn't use both `HeapAlloc` and `GcAlloc`,
/// - every value is defined before it's used: in a block that dominates the
///   use, or earlier in the same block.
pub fn verify(module: &Module) -> Result<(), String> {
    let mut names = HashSet::default();
    for (i, f) in module.funcs.iter().enumerate() {
        if !names.insert(&f.name) {
            return Err(format!("there's more than one function called {}", f.name));
        }
        let ok = (1..=13).contains(&f.name.len()) && f.name.chars().all(|c| c.is_ascii_alphanumeric() || c == '_');
        if i > 0 && !ok {
            return Err(format!("function names must be 1 to 13 letters, digits or '_': {:?}", f.name));
        }
        verify_function(module, f).map_err(|e| format!("{}: {e}", f.name))?;
    }
    for name in &module.externs {
        if let Err(e) = external_name(name) {
            return Err(format!("the external function {name:?}: {e}"));
        }
    }
    let uses = |gc: bool| {
        module.funcs.iter().any(|f| {
            cfg::reverse_postorder(f).iter().flat_map(|b| &f.blocks[b.index()].effects).any(|e| {
                matches!((&f.values[e.index()].node, gc), (Node::GcAlloc(..), true) | (Node::HeapAlloc(_), false))
            })
        })
    };
    if uses(true) && uses(false) {
        return Err("the module uses both heap_alloc and gc_alloc".to_string());
    }
    Ok(())
}

fn verify_function(module: &Module, f: &Function) -> Result<(), String> {
    for block in &f.blocks {
        for target in block.term.iter().flat_map(|t| t.targets()) {
            if target.block.index() >= f.blocks.len() {
                return Err(format!("jumps to {}, which isn't in this function", target.block));
            }
        }
    }
    let rpo = cfg::reverse_postorder(f);
    let idom = cfg::dominators(f, &rpo);
    let mut position = vec![usize::MAX; f.values.len()];
    for &b in &rpo {
        for (i, &e) in f.blocks[b.index()].effects.iter().enumerate() {
            position[e.index()] = i;
        }
    }

    // whether `used` can be used in block `b` by its effect number `at`, or by
    // a pure node or the terminator if `at` is usize::MAX
    let check = |used: Value, b: Block, at: usize| -> Result<(), String> {
        let Some(data) = f.values.get(used.index()) else {
            return Err(format!("{used} isn't in this function"));
        };
        if !data.node.has_result() {
            return Err(format!("{used} has no value"));
        }
        let Some(def) = data.block else { return Ok(()) };
        if idom[def.index()].is_none() || !cfg::dominates(&idom, def, b) {
            return Err(format!("{used} is used in {b}, but defined in {def}, which doesn't dominate it"));
        }
        if def == b && position[used.index()] != usize::MAX && position[used.index()] >= at {
            return Err(format!("{used} is used in {b} before it's defined"));
        }
        if !data.node.is_pure() && position[used.index()] == usize::MAX {
            return Err(format!("{used} is used, but isn't one of {def}'s effects"));
        }
        Ok(())
    };

    for &b in &rpo {
        let block = &f.blocks[b.index()];
        let term = block.term.as_ref().ok_or(format!("{b} has no terminator"))?;
        for (i, &e) in block.effects.iter().enumerate() {
            let node = &f.values[e.index()].node;
            for op in node.operands() {
                check(op, b, i)?;
            }
            if let Node::Call(name, args) = node {
                let callee = module.index_of(name).ok_or(format!("calls {name}, which doesn't exist"))?;
                if callee == 0 {
                    return Err("calls main".to_string());
                }
                let want = module.funcs[callee].param_count();
                if args.len() != want {
                    return Err(format!("calls {name} with {} arguments, but it takes {want}", args.len()));
                }
            }
            if let Node::CallExtern(name, args) = node {
                if !module.externs.contains(name) {
                    return Err(format!("calls the external function {name}, which isn't declared"));
                }
                if args.len() > 9 {
                    return Err(format!("calls {name} with {} arguments, but an external function takes at most 9", args.len()));
                }
            }
            if let Node::Intrinsic(which, args) = node {
                let want = usize::from(*which == Intrinsic::SetHeapPointer);
                if args.len() != want {
                    return Err(format!("{} takes {want} operands, not {}", which.name(), args.len()));
                }
            }
        }
        for target in term.targets() {
            let want = f.blocks[target.block.index()].params.len();
            if target.args.len() != want {
                return Err(format!(
                    "{b} jumps to {} with {} arguments, but it takes {want}",
                    target.block,
                    target.args.len()
                ));
            }
        }
        for op in term.operands() {
            check(op, b, usize::MAX)?;
        }
    }

    // (pure nodes nothing needs are never computed, so only the ones that
    // are have to be well formed: passes like merging blocks can leave dead
    // ones behind that refer to values that no longer dominate them)
    let needed = crate::ir::compiler::sched::needed(f, &rpo);
    for (i, data) in f.values.iter().enumerate() {
        if !needed[i] && matches!(data.node, Node::Unary(..) | Node::Binary(..)) {
            continue;
        }
        if let (Node::GlobalAddr(i), Some(b)) = (&data.node, data.block) {
            if idom[b.index()].is_some() && *i >= module.globals {
                return Err(format!("uses global {i}, but there are only {}", module.globals));
            }
        }
        if let (Node::FuncAddr(name), Some(b)) = (&data.node, data.block) {
            if idom[b.index()].is_some() && !matches!(module.index_of(name), Some(i) if i > 0) {
                return Err(format!("takes the address of {name}, which isn't a function other than main"));
            }
        }
        if let (Node::Unary(..) | Node::Binary(..), Some(b)) = (&data.node, data.block) {
            if idom[b.index()].is_some() {
                for op in data.node.operands() {
                    check(op, b, usize::MAX)?;
                }
            }
        }
    }
    Ok(())
}

/// Whether `name` can be an external function's: it's the function's label
/// in the VM, so it's a C name of at most 15 characters, which isn't one
/// of the program's own labels (`f_...` and `rt_...`), nor one the C or
/// LLVM backends use.
pub(super) fn external_name(name: &str) -> Result<(), String> {
    const TAKEN: [&str; 12] = ["main", "tape", "ptr", "acc", "stack", "putchar", "getchar", "printf", "calloc", "malloc", "exit", "free"];
    let c_name = (1..=15).contains(&name.len())
        && name.chars().all(|c| c.is_ascii_alphanumeric() || c == '_')
        && !name.starts_with(|c: char| c.is_ascii_digit());
    if !c_name {
        Err("an external function's name is 1 to 15 letters, digits or '_', not starting with a digit".into())
    } else if name.starts_with("f_") || name.starts_with("rt_") || TAKEN.contains(&name) {
        Err("that name is taken by the program or a backend".into())
    } else {
        Ok(())
    }
}
