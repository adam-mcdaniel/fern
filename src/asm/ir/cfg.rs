//! The control-flow graph: successors, block order and dominators.

use super::{Block, Function, Terminator};

pub(super) fn successors(f: &Function, b: Block) -> Vec<Block> {
    match &f.blocks[b.index()].term {
        Some(Terminator::Jump(t)) => vec![t.block],
        Some(Terminator::Branch(_, t, e)) => vec![t.block, e.block],
        _ => vec![],
    }
}

/// The blocks reachable from the entry, in reverse postorder: each block comes
/// before its successors, except along loops' back edges. A branch's first
/// target comes before its second.
pub(super) fn reverse_postorder(f: &Function) -> Vec<Block> {
    let mut seen = vec![false; f.blocks.len()];
    let mut post = vec![];
    let mut stack = vec![(f.entry(), 0)];
    seen[0] = true;
    while let Some(&(b, i)) = stack.last() {
        let succ = successors(f, b);
        if let Some(&s) = succ.iter().rev().nth(i) {
            stack.last_mut().unwrap().1 += 1;
            if !seen[s.index()] {
                seen[s.index()] = true;
                stack.push((s, 0));
            }
        } else {
            post.push(b);
            stack.pop();
        }
    }
    post.reverse();
    post
}

/// Each block's predecessors among `blocks`, once per edge.
pub(super) fn predecessors(f: &Function, blocks: &[Block]) -> Vec<Vec<Block>> {
    let mut preds = vec![vec![]; f.blocks.len()];
    for &b in blocks {
        for s in successors(f, b) {
            preds[s.index()].push(b);
        }
    }
    preds
}

/// Each block's immediate dominator, given the blocks in reverse postorder
/// (Cooper, Harvey and Kennedy's algorithm). The entry is its own, and
/// unreachable blocks have none.
pub(super) fn dominators(f: &Function, rpo: &[Block]) -> Vec<Option<Block>> {
    let mut order = vec![usize::MAX; f.blocks.len()];
    for (i, b) in rpo.iter().enumerate() {
        order[b.index()] = i;
    }
    let preds = predecessors(f, rpo);
    let mut idom: Vec<Option<Block>> = vec![None; f.blocks.len()];
    idom[0] = Some(f.entry());
    let intersect = |idom: &[Option<Block>], mut a: Block, mut b: Block| {
        while a != b {
            while order[a.index()] > order[b.index()] {
                a = idom[a.index()].unwrap();
            }
            while order[b.index()] > order[a.index()] {
                b = idom[b.index()].unwrap();
            }
        }
        a
    };
    loop {
        let mut changed = false;
        for &b in &rpo[1..] {
            let mut new = None;
            for &p in &preds[b.index()] {
                if idom[p.index()].is_some() {
                    new = Some(match new {
                        None => p,
                        Some(n) => intersect(&idom, p, n),
                    });
                }
            }
            if new != idom[b.index()] {
                idom[b.index()] = new;
                changed = true;
            }
        }
        if !changed {
            return idom;
        }
    }
}

/// Whether `a` dominates `b`: every path from the entry to `b` passes `a`.
pub(super) fn dominates(idom: &[Option<Block>], a: Block, mut b: Block) -> bool {
    loop {
        if a == b {
            return true;
        }
        match idom[b.index()] {
            Some(up) if up != b => b = up,
            _ => return false,
        }
    }
}

/// A natural loop: the blocks that can reach one of its latches without
/// passing its header, which dominates them all.
pub(super) struct Loop {
    pub(super) header: Block,
    /// The blocks that jump back to the header.
    pub(super) latches: Vec<Block>,
    pub(super) body: std::collections::HashSet<Block>,
}

/// The function's natural loops, innermost (latest header) first.
pub(super) fn loops(f: &Function) -> Vec<Loop> {
    let rpo = reverse_postorder(f);
    let idom = dominators(f, &rpo);
    let preds = predecessors(f, &rpo);
    let mut loops = vec![];
    for &header in rpo.iter().rev() {
        let mut latches: Vec<Block> = preds[header.index()].iter().copied().filter(|&p| dominates(&idom, header, p)).collect();
        latches.dedup();
        if latches.is_empty() {
            continue;
        }
        let mut body = std::collections::HashSet::from([header]);
        let mut stack = latches.clone();
        while let Some(b) = stack.pop() {
            if body.insert(b) {
                stack.extend(&preds[b.index()]);
            }
        }
        loops.push(Loop { header, latches, body });
    }
    loops
}
