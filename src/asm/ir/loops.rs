//! Loop optimizations: strength reduction of induction variables, and fully
//! unrolling loops that run a small, constant number of times.

use super::opt::replace_uses;
use super::{cfg, fold, sched, BinOp, Block, Function, Node, Target, Terminator, Value};
use std::collections::HashMap;

/// For each parameter of `header` that every back edge passes as itself plus
/// a constant, that constant.
fn induction_steps(f: &Function, l: &cfg::Loop) -> HashMap<usize, i64> {
    let mut steps = HashMap::new();
    for (i, &p) in f.blocks[l.header.index()].params.iter().enumerate() {
        let mut step = None;
        let all = l.latches.iter().all(|&latch| {
            f.blocks[latch.index()].term.iter().flat_map(|t| t.targets()).filter(|t| t.block == l.header).all(|t| {
                match f.values[t.args[i].index()].node {
                    Node::Binary(BinOp::Add, a, c) if a == p => match (f.const_value(c), step) {
                        (Some(c), None) => {
                            step = Some(c);
                            true
                        }
                        (Some(c), Some(s)) => c == s,
                        _ => false,
                    },
                    _ => false,
                }
            })
        });
        if let (true, Some(c)) = (all, step) {
            steps.insert(i, c);
        }
    }
    steps
}

/// Strength reduction: inside a loop whose parameter `i` steps by a
/// constant, `i * k` becomes a new parameter that steps by `k` times as
/// much, and `index(base, i)` a pointer that moves along by the step. One
/// loop and one node at a time.
pub(super) fn strength_reduce(f: &mut Function) -> bool {
    let rpo = cfg::reverse_postorder(f);
    let preds = cfg::predecessors(f, &rpo);
    let needed = sched::needed(f, &rpo);
    for l in cfg::loops(f) {
        let steps = induction_steps(f, &l);
        let params = f.blocks[l.header.index()].params.clone();
        let outside = |v: Value| f.values[v.index()].block.is_none_or(|b| !l.body.contains(&b));
        let induction = |v: Value| params.iter().position(|&p| p == v).filter(|i| steps.contains_key(i));
        // (the node, its induction variable's index, and what it is)
        let found = f.values.iter().enumerate().find_map(|(u, data)| {
            if !needed[u] || !data.block.is_some_and(|b| l.body.contains(&b)) {
                return None;
            }
            let (i, kind) = match data.node {
                Node::Binary(BinOp::Mul, a, k) => induction(a).zip(f.const_value(k)).map(|(i, k)| (i, Kind::Scale(k)))?,
                Node::Binary(BinOp::Index, base, a) if outside(base) => induction(a).map(|i| (i, Kind::Index(base)))?,
                _ => return None,
            };
            Some((Value(u as u32), i, kind))
        });
        let Some((u, i, kind)) = found else { continue };
        let step = steps[&i];
        f.rebuild_dedup();
        let q = f.add_param(l.header);
        let mut sources = preds[l.header.index()].clone();
        sources.dedup();
        for p in sources {
            let back = l.latches.contains(&p);
            let targets: Vec<Target> =
                f.blocks[p.index()].term.iter().flat_map(|t| t.targets()).filter(|t| t.block == l.header).cloned().collect();
            let saved = f.current;
            f.current = p;
            let args: Vec<Value> = targets
                .iter()
                .map(|t| match (kind, back) {
                    (Kind::Scale(k), false) => {
                        let k = f.int(k);
                        f.mul(t.args[i], k)
                    }
                    (Kind::Index(base), false) => f.index(base, t.args[i]),
                    (Kind::Scale(k), true) => {
                        let d = f.int(step.wrapping_mul(k));
                        f.add(q, d)
                    }
                    (Kind::Index(_), true) => {
                        let d = f.int(step);
                        f.index(q, d)
                    }
                })
                .collect();
            f.current = saved;
            let mut args = args.into_iter();
            f.blocks[p.index()].term.as_mut().unwrap().map_targets(|t| {
                let mut t = t.clone();
                if t.block == l.header {
                    t.args.push(args.next().unwrap());
                }
                t
            });
        }
        replace_uses(f, &HashMap::from([(u, q)]));
        return true;
    }
    false
}

#[derive(Clone, Copy)]
enum Kind {
    /// The induction variable times a constant.
    Scale(i64),
    /// An address in an array, indexed by the induction variable.
    Index(Value),
}

/// The most iterations a loop is unrolled for, and the most nodes the
/// unrolled copies can add up to.
const MAX_ITERATIONS: i64 = 8;
const MAX_NODES: usize = 96;

/// Fully unrolls a loop that runs a small, constant number of times, when its
/// header only decides whether to go round again and its body is one block.
/// Afterwards the header runs once more with the final values, and its
/// branch folds away.
pub(super) fn unroll(f: &mut Function) -> bool {
    let rpo = cfg::reverse_postorder(f);
    let preds = cfg::predecessors(f, &rpo);
    for l in cfg::loops(f) {
        let h = l.header;
        let [latch] = l.latches[..] else { continue };
        if l.body.len() != 2 || !f.blocks[h.index()].effects.is_empty() {
            continue;
        }
        let Some(Terminator::Branch(cond, t, e)) = f.blocks[h.index()].term.clone() else { continue };
        let (stay, leave_on_true) = if t.block == latch { (t.clone(), false) } else if e.block == latch { (e.clone(), true) } else { continue };
        if !stay.args.is_empty() || preds[latch.index()] != [h] {
            continue;
        }
        let forward: Vec<Block> = preds[h.index()].iter().copied().filter(|&p| p != latch).collect();
        let [entry] = forward[..] else { continue };
        let Some(start) = f.blocks[entry.index()].term.as_ref().and_then(|t| t.targets().into_iter().find(|t| t.block == h).cloned())
        else {
            continue;
        };
        if f.blocks[entry.index()].term.as_ref().unwrap().targets().iter().filter(|t| t.block == h).count() != 1 {
            continue;
        }
        let Some(Terminator::Jump(back)) = f.blocks[latch.index()].term.clone() else { continue };

        // the trip count, from an induction variable compared with a constant
        let steps = induction_steps(f, &l);
        let params = f.blocks[h.index()].params.clone();
        let Node::Binary(op, x, n) = f.values[cond.index()].node else { continue };
        let Some(i) = params.iter().position(|&p| p == x) else { continue };
        let (Some(&step), Some(init), Some(n)) = (steps.get(&i), f.const_value(start.args[i]), f.const_value(n)) else {
            continue;
        };
        if !matches!(op, BinOp::Lt | BinOp::Le | BinOp::Gt | BinOp::Ge | BinOp::Ne) || f.values[cond.index()].block != Some(h) {
            continue;
        }
        let small = |v: i64| (-(1 << 14)..1 << 14).contains(&v);
        let mut trips = 0;
        let mut value = init;
        loop {
            if !small(value) || trips > MAX_ITERATIONS {
                break;
            }
            let taken = fold::binary(op, value, n, 64) != 0;
            if taken == leave_on_true {
                break;
            }
            trips += 1;
            value += step;
        }
        if !small(value) || trips > MAX_ITERATIONS {
            continue;
        }
        let pinned = f.pinned();
        let body_size = pinned[latch.index()].len() + pinned[h.index()].len();
        if trips == 0 || trips as usize * body_size > MAX_NODES {
            continue;
        }

        // copy the header's values and the body once per iteration
        let mut env: HashMap<Value, Value> = params.iter().copied().zip(start.args.iter().copied()).collect();
        let first = f.new_block(0);
        let mut current = first;
        for trip in 0..trips {
            let mut map = env.clone();
            for &v in pinned[h.index()].iter().chain(&pinned[latch.index()]) {
                if !map.contains_key(&v) && !matches!(f.values[v.index()].node, Node::Param(..)) {
                    let mut node = f.values[v.index()].node.clone();
                    node.map_operands(|o| *map.get(&o).unwrap_or(&o));
                    let copy = f.push(node, Some(current));
                    map.insert(v, copy);
                }
            }
            // operands that refer to values copied later in the list
            let copies: Vec<Value> = map.values().copied().filter(|c| f.values[c.index()].block == Some(current)).collect();
            for c in copies {
                f.values[c.index()].node.map_operands(|o| *map.get(&o).unwrap_or(&o));
            }
            f.blocks[current.index()].effects = f.blocks[latch.index()].effects.iter().map(|e| map[e]).collect();
            env = params.iter().copied().zip(back.args.iter().map(|a| *map.get(a).unwrap_or(a))).collect();
            let next = if trip + 1 < trips { f.new_block(0) } else { h };
            let args = if next == h { params.iter().map(|p| env[p]).collect() } else { vec![] };
            f.blocks[current.index()].term = Some(Terminator::Jump(Target { block: next, args }));
            current = next;
        }
        f.blocks[entry.index()].term.as_mut().unwrap().map_targets(|t| {
            if t.block == h { Target { block: first, args: vec![] } } else { t.clone() }
        });
        // the copies carry the loop's values, so the body's own jump back
        // goes away, leaving the header to run once
        let exit = if leave_on_true { t } else { e };
        f.blocks[h.index()].term = Some(Terminator::Jump(exit));
        return true;
    }
    false
}
