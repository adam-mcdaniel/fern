//! Which values a function needs, and the order each block computes them in.

use super::{Block, Function, Node, Terminator, Value};
use crate::asm::fx::HashMap;

/// Whether each value is needed: depended on, directly or not, by an effect,
/// a branch or a return in one of `reachable`. A jump's argument is only
/// needed if the parameter it's passed to is, so a value that only goes
/// round a loop to compute itself isn't. Everything else is dead, and is
/// never computed.
pub(in crate::ir) fn needed(f: &Function, reachable: &[Block]) -> Vec<bool> {
    let mut needed = vec![false; f.values.len()];
    let mut incoming: HashMap<Value, Vec<Value>> = HashMap::default();
    let mut stack = vec![];
    for &b in reachable {
        let block = &f.blocks[b.index()];
        stack.extend(&block.effects);
        match &block.term {
            Some(Terminator::Branch(c, ..)) | Some(Terminator::Return(Some(c))) => stack.push(*c),
            _ => {}
        }
        for t in block.term.iter().flat_map(|t| t.targets()) {
            for (&p, &a) in f.blocks[t.block.index()].params.iter().zip(&t.args) {
                incoming.entry(p).or_default().push(a);
            }
        }
    }
    while let Some(v) = stack.pop() {
        if !needed[v.index()] {
            needed[v.index()] = true;
            stack.extend(f.values[v.index()].node.operands());
            if let Some(args) = incoming.get(&v) {
                stack.extend(args);
            }
        }
    }
    needed
}

/// Whether each needed value is used outside the block it belongs to.
pub(in crate::ir) fn used_outside(f: &Function, reachable: &[Block], needed: &[bool]) -> Vec<bool> {
    let mut outside = vec![false; f.values.len()];
    let mut mark = |user: Option<Block>, v: Value| {
        let block = f.values[v.index()].block;
        if block.is_some() && block != user {
            outside[v.index()] = true;
        }
    };
    for (i, data) in f.values.iter().enumerate() {
        if needed[i] {
            for op in data.node.operands() {
                mark(data.block, op);
            }
        }
    }
    for &b in reachable {
        if let Some(t) = &f.blocks[b.index()].term {
            for op in t.operands() {
                mark(Some(b), op);
            }
        }
    }
    outside
}

/// The order block `b` computes its values in. Each effect comes right after
/// the pure nodes it needs that haven't been computed yet, so pure nodes are
/// computed as late as possible. Then come the nodes the terminator needs, and
/// last the ones only other blocks use. `pinned` is the values in `b`.
pub(in crate::ir) fn schedule(f: &Function, b: Block, needed: &[bool], outside: &[bool], pinned: &[Value]) -> Vec<Value> {
    let mut order = vec![];
    let mut done = vec![false; f.values.len()];
    for &e in &f.blocks[b.index()].effects {
        for op in f.values[e.index()].node.operands() {
            visit(f, b, op, &mut order, &mut done);
        }
        order.push(e);
        done[e.index()] = true;
    }
    if let Some(t) = &f.blocks[b.index()].term {
        for op in t.operands() {
            visit(f, b, op, &mut order, &mut done);
        }
    }
    for &v in pinned {
        if needed[v.index()] && outside[v.index()] {
            visit(f, b, v, &mut order, &mut done);
        }
    }
    order
}

/// Adds `v` to `order` after the not-yet-computed pure nodes of `b` it depends
/// on, if it's a pure node of `b` itself.
fn visit(f: &Function, b: Block, v: Value, order: &mut Vec<Value>, done: &mut [bool]) {
    let mut stack = vec![(v, false)];
    while let Some((v, expanded)) = stack.pop() {
        let data = &f.values[v.index()];
        if done[v.index()] || data.block != Some(b) || !matches!(data.node, Node::Unary(..) | Node::Binary(..) | Node::FuncAddr(_) | Node::GlobalAddr(_)) {
            continue;
        }
        if expanded {
            done[v.index()] = true;
            order.push(v);
        } else {
            stack.push((v, true));
            for op in data.node.operands().into_iter().rev() {
                stack.push((op, false));
            }
        }
    }
}
