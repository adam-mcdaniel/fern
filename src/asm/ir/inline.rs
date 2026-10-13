//! Inlining calls, and turning tail calls into loops.

use super::opt::replace_uses;
use super::{cfg, Block, Function, Module, Node, Target, Terminator, Value};
use std::collections::HashMap;

/// Functions at most this big (in nodes that run) are inlined everywhere.
/// Bigger ones are only inlined if they're called once.
const SMALL: usize = 30;

/// Turns calls a function makes to itself right before returning their
/// result into jumps back to its start, with the call's arguments as the new
/// parameters. The result can be returned straight away, or passed to a
/// block that only returns it, as the branches of a conditional do.
pub(super) fn tail_calls(f: &mut Function) -> bool {
    let rpo = cfg::reverse_postorder(f);
    let returned = |e: Value, term: &Terminator| match term {
        Terminator::Return(Some(v)) => *v == e,
        Terminator::Jump(t) => {
            let target = &f.blocks[t.block.index()];
            match &target.term {
                Some(Terminator::Return(Some(v))) if target.effects.is_empty() => {
                    target.params.iter().zip(&t.args).any(|(p, a)| p == v && *a == e)
                }
                _ => false,
            }
        }
        _ => false,
    };
    let is_tail = |b: Block| {
        let block = &f.blocks[b.index()];
        match (block.effects.last(), &block.term) {
            (Some(&e), Some(term)) => {
                returned(e, term) && matches!(&f.values[e.index()].node, Node::Call(name, _) if *name == f.name)
            }
            _ => false,
        }
    };
    let tails: Vec<Block> = rpo.iter().copied().filter(|&b| is_tail(b)).collect();
    if tails.is_empty() {
        return false;
    }

    // the entry block's contents move to a new loop header, so the tail calls
    // can jump back to it
    let entry = f.entry();
    let head = f.new_block(f.param_count());
    let params = f.blocks[0].params.clone();
    let head_params = f.blocks[head.index()].params.clone();
    for data in &mut f.values {
        if data.block == Some(entry) && !matches!(data.node, Node::Param(b, _) if b == entry) {
            data.block = Some(head);
        }
    }
    f.blocks[head.index()].effects = std::mem::take(&mut f.blocks[0].effects);
    f.blocks[head.index()].term = f.blocks[0].term.take();
    replace_uses(f, &params.iter().copied().zip(head_params).collect());
    f.blocks[0].term = Some(Terminator::Jump(Target { block: head, args: params }));

    for b in tails {
        let b = if b == entry { head } else { b };
        let call = f.blocks[b.index()].effects.pop().unwrap();
        let Node::Call(_, args) = f.values[call.index()].node.clone() else { unreachable!() };
        f.blocks[b.index()].term = Some(Terminator::Jump(Target { block: head, args }));
    }
    true
}

/// How many nodes of `f` run: its effects and the pure nodes they need.
fn size(f: &Function) -> usize {
    let blocks = cfg::reverse_postorder(f);
    let needed = super::sched::needed(f, &blocks);
    let pure = f.values.iter().enumerate().filter(|(i, d)| needed[*i] && d.block.is_some()).count();
    pure + blocks.len()
}

/// Inlines calls to small functions, and to functions that are only called
/// once, unless they're recursive.
pub(super) fn inline(module: &mut Module) -> bool {
    let recursive = module.recursive();
    let mut calls = vec![0; module.funcs.len()];
    for f in &module.funcs {
        for &b in &cfg::reverse_postorder(f) {
            for &e in &f.blocks[b.index()].effects {
                if let Node::Call(name, _) = &f.values[e.index()].node {
                    calls[module.index_of(name).unwrap()] += 1;
                }
            }
        }
    }
    let sizes: Vec<usize> = module.funcs.iter().map(size).collect();
    let worth = |callee: usize| !recursive[callee] && (calls[callee] == 1 || sizes[callee] <= SMALL);

    let mut changed = false;
    for caller in 0..module.funcs.len() {
        // a cap, since inlining can expose more calls to inline
        for _ in 0..50 {
            let f = &module.funcs[caller];
            let site = cfg::reverse_postorder(f).into_iter().find_map(|b| {
                f.blocks[b.index()].effects.iter().position(|&e| match &f.values[e.index()].node {
                    Node::Call(name, _) => {
                        let callee = module.index_of(name).unwrap();
                        callee != caller && worth(callee)
                    }
                    _ => false,
                })
                .map(|i| (b, i))
            });
            let Some((b, i)) = site else { break };
            let e = module.funcs[caller].blocks[b.index()].effects[i];
            let Node::Call(name, _) = &module.funcs[caller].values[e.index()].node else { unreachable!() };
            let callee = module.funcs[module.index_of(name).unwrap()].clone();
            inline_call(&mut module.funcs[caller], b, i, &callee);
            changed = true;
        }
    }
    changed
}

/// Replaces the call that's effect number `k` of block `b` with a copy of
/// `g`'s body.
fn inline_call(f: &mut Function, b: Block, k: usize, g: &Function) {
    let call = f.blocks[b.index()].effects[k];
    let Node::Call(_, args) = f.values[call.index()].node.clone() else { unreachable!() };

    // split b after the call: what follows moves to a block that receives the
    // call's result
    let rest = f.new_block(1);
    let result = f.blocks[rest.index()].params[0];
    let after = f.blocks[b.index()].effects.split_off(k + 1);
    f.blocks[b.index()].effects.pop();
    for &e in &after {
        f.values[e.index()].block = Some(rest);
    }
    f.blocks[rest.index()].effects = after;
    f.blocks[rest.index()].term = f.blocks[b.index()].term.take();
    replace_uses(f, &HashMap::from([(call, result)]));
    // pure nodes of b that depend on anything that moved, move too
    loop {
        let mut moved = false;
        for i in 0..f.values.len() {
            let data = &f.values[i];
            if data.block == Some(b)
                && matches!(data.node, Node::Unary(..) | Node::Binary(..))
                && data.node.operands().iter().any(|o| f.values[o.index()].block == Some(rest))
            {
                f.values[i].block = Some(rest);
                moved = true;
            }
        }
        if !moved {
            break;
        }
    }

    // copy g's blocks and values
    let blocks: Vec<Block> = g.blocks.iter().map(|gb| f.new_block(gb.params.len())).collect();
    let mut map: Vec<Option<Value>> = vec![None; g.values.len()];
    for (gb, &nb) in g.blocks.iter().zip(&blocks) {
        for (j, &p) in gb.params.iter().enumerate() {
            map[p.index()] = Some(f.blocks[nb.index()].params[j]);
        }
    }
    for (i, data) in g.values.iter().enumerate() {
        if map[i].is_none() {
            map[i] = Some(match data.node {
                Node::Const(k) => f.int(k),
                _ => f.push(data.node.clone(), data.block.map(|x| blocks[x.index()])),
            });
        }
    }
    let map: Vec<Value> = map.into_iter().map(Option::unwrap).collect();
    for (i, data) in g.values.iter().enumerate() {
        if !matches!(data.node, Node::Const(_)) {
            f.values[map[i].index()].node.map_operands(|o| map[o.index()]);
        }
    }
    let zero = f.int(0);
    for (gb, &nb) in g.blocks.iter().zip(&blocks) {
        f.blocks[nb.index()].effects = gb.effects.iter().map(|e| map[e.index()]).collect();
        f.blocks[nb.index()].term = gb.term.as_ref().map(|t| match t {
            Terminator::Return(v) => Terminator::Jump(Target { block: rest, args: vec![v.map_or(zero, |v| map[v.index()])] }),
            t => {
                let mut t = t.clone();
                t.map_operands(|o| map[o.index()]);
                t.map_targets(|t| Target { block: blocks[t.block.index()], args: t.args.clone() });
                t
            }
        });
    }
    f.blocks[b.index()].term = Some(Terminator::Jump(Target { block: blocks[0], args }));
}
