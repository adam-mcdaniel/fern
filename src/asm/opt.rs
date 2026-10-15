//! An optimizer for VM programs: ops in, ops out, printing the same.
//! [`opt_fast`] makes a program take as few steps as it can, whatever that
//! does to its size; [`opt_size`] makes it as small as it can, whatever
//! that does to its speed. [`opt_with`] is told more about the program
//! ([`Facts`]: cells no pointer leads to, and calls only to labels), and
//! sees further for it.
//!
//! It works on the program's structure, loops and functions, and runs these
//! until nothing changes:
//!
//! - **Summaries of functions**, found together across the call graph:
//!   whether each gives the pointer back where it found it, whether it's
//!   only ever called from the first cell (so places in it are cells),
//!   which private cells it can write and read, and whether it can write
//!   anywhere else. Calls use them instead of assuming the worst.
//! - **Abstract interpretation** of each function, tracking where the pointer
//!   is (relative to where the function started, while it can tell), what
//!   `acc` holds, and what cells hold, as symbolic values: constants,
//!   addresses of cells, functions' addresses, and opaque values that are at
//!   least known to stay put. An op whose effect is already there is
//!   dropped: a load of what `acc` holds, a store of what the cell holds, a
//!   `?`, `@` or `Set` of what `acc` holds, a `#` of a 0 or 1. Arithmetic on
//!   constants folds into `Set`, and a load of a known value becomes one. A
//!   load reads whichever cell holding the same value is nearest, so copies
//!   are read through, and often end up never read at all.
//! - **Memory**: following the same pointer value always leads to the same
//!   place, so what's known about cells a pointer leads to lasts until a
//!   store that could be to them; a store to a private cell only changes
//!   that cell, and a store through a pointer changes no private one.
//! - **Lazy moves**: the pointer only moves when something needs it to be
//!   somewhere, so moves there and back cancel out. `[` and `]` only look at
//!   `acc`, so in a loop whose body comes back to where it started, the
//!   pointer waits where the body first needs it, and only the end of the
//!   body moves it back there. `&` waits too, so a `*` of the same pointer
//!   right after doesn't need either.
//! - **Dereferences of known addresses**: `*` through a cell holding the
//!   address of a cell the pointer can reach by moving, undone by `&` before
//!   anything it can't see happens, becomes a move, and both go.
//! - **Facts across control flow**: after `]`, `acc` is 0, and so is a cell
//!   that held what `acc` did. What's known about cells a loop's body never
//!   writes holds through the loop; for a loop with no loops inside, so does
//!   what its body leaves as it found it (assumed, then checked). What's
//!   known at the end of the body holds after the loop if it held before it,
//!   so values survive `if`s. A loop entered with `acc` known to be 0 never
//!   runs, so it goes; one entered with `acc` known not to be, whose body
//!   always leaves it 0, runs once, so its brackets go; one whose body only
//!   works out `acc`, leaving it 0, becomes `Set(0)`.
//! - **Inlining**: functions called once are inlined, and for speed, small
//!   ones (up to 64 ops) wherever they're called; functions nothing refers
//!   to are removed.
//! - **Dead code**: an op that only sets `acc` goes if `acc` is set again
//!   before anything reads it, and a store goes if its value is overwritten
//!   before anything could read it on every path: liveness over each
//!   sequence's flow graph, through loops, and across functions (what's
//!   live when a function returns is what's live after the calls to it; a
//!   call reads the private cells its callee reads before writing them, and
//!   any others, as does a read through a pointer). The tape the program
//!   leaves when it ends isn't kept, only what it prints.
//!
//! Then, for size, **outlining**: runs of ops (and whole loops) that recur
//! become calls to a function of them, the run that saves most first, while
//! any saves anything, including runs in the functions it makes.
//!
//! The routines `asm` writes for what the VM has no instructions for
//! (multiplying, dividing, comparing, the bitwise operations, shifting) are
//! about as fast as the VM allows, and targets that know them do them with
//! the machine's instructions instead, if they can tell what they are. So
//! each is optimized on its own, as if called from anywhere with everything
//! it leaves read after ([`routine_forms`]: one form for speed, one for
//! size), and a program's copy of one becomes the form for the goal and is
//! otherwise left as it is: not inlined, and not changed for what its
//! callers need of it. Targets know all its forms.
//!
//! Values mean the same at every cell width: only arithmetic that wraps
//! (`+`, `-`) folds freely, `#` only folds on numbers small enough to have
//! the same sign at 16 bits, and a number is only taken to be nonzero if it
//! is at 16 bits. The pointer never goes where the program wouldn't have
//! taken it (the VM stops a program whose pointer leaves the tape, even if
//! it doesn't touch a cell there). Functions' addresses are where they are
//! in the program, so they change: a program that prints one, or does
//! arithmetic on one, can print something else.

use crate::Op;
use std::collections::{HashMap, HashSet};

/// Optimizes a program for speed: fewest steps, whatever it costs in size.
pub fn opt_fast(ops: Vec<Op>) -> Vec<Op> {
    opt_with(ops, &Facts::default(), Goal::Fast)
}

/// Optimizes a program for size: fewest ops, whatever it costs in steps.
pub fn opt_size(ops: Vec<Op>) -> Vec<Op> {
    opt_with(ops, &Facts::default(), Goal::Size)
}

/// What to optimize for.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Goal {
    /// Fewest steps.
    Fast,
    /// Fewest ops.
    Size,
}

/// Optimizes a program for `goal`, given what's promised about it.
pub fn opt_with(ops: Vec<Op>, facts: &Facts, goal: Goal) -> Vec<Op> {
    let mut items = parse(ops);
    // (routines as their form for the goal, which nothing changes after)
    let kept = routines_in(&items);
    fn swap(items: &mut [Item], kept: &HashSet<Label>, goal: Goal) {
        for item in items {
            match item {
                Item::Func(l, body) if kept.contains(l) => {
                    let forms = &routine_forms()[&name(l)];
                    let form = match goal {
                        Goal::Fast => &forms[1],
                        Goal::Size => forms.iter().min_by_key(|f| f.len()).unwrap(),
                    };
                    *body = parse(form.clone());
                }
                Item::Func(_, body) | Item::Loop(body) => swap(body, kept, goal),
                Item::Op(_) => {}
            }
        }
    }
    swap(&mut items, &kept, goal);
    let mut items = optimize(items, facts, goal, &kept, &HashSet::new());
    // (the routines as they were, after the last tidying up, which doesn't
    // see into them)
    let mut bodies = HashMap::new();
    fn hollow(items: &mut [Item], kept: &HashSet<Label>, bodies: &mut HashMap<Label, Vec<Item>>) {
        for item in items {
            match item {
                Item::Func(l, body) if kept.contains(l) => {
                    bodies.insert(*l, std::mem::take(body));
                }
                Item::Func(_, body) | Item::Loop(body) => hollow(body, kept, bodies),
                Item::Op(_) => {}
            }
        }
    }
    if goal == Goal::Size {
        outline(&mut items, &kept);
    }
    hollow(&mut items, &kept, &mut bodies);
    let mut out = vec![];
    flatten(items, &mut out);
    let mut out = cleanup(out).into_iter();
    let mut ops = vec![];
    while let Some(op) = out.next() {
        ops.push(op);
        if let (Op::Func, [.., Op::Label(l), Op::Func]) = (op, &ops[..]) {
            if let Some(body) = bodies.remove(l) {
                flatten(body, &mut ops);
            }
        }
    }
    ops
}

/// The optimizations, until nothing changes (or a dozen times), leaving
/// `kept` functions as they are and not inlining `pinned` ones.
fn optimize(mut items: Vec<Item>, facts: &Facts, goal: Goal, kept: &HashSet<Label>, pinned: &HashSet<Label>) -> Vec<Item> {
    for _ in 0..12 {
        let mut changed = inline(&mut items, goal, kept, pinned);
        changed |= dead_acc(&mut items, true, kept);
        changed |= remove_unused(&mut items);
        let sums = Summaries::of(&items, facts);
        let mut o = Optimizer { tokens: Tokens::default(), sums, kept, changed: false };
        items = o.program(items);
        changed |= o.changed;
        let sums = Summaries::of(&items, facts);
        changed |= dead_stores(&mut items, &sums, kept);
        if !changed {
            break;
        }
    }
    items
}

/// The longest run of items (ops and whole loops) `outline` looks at.
const RUN: usize = 48;

/// For size: replaces runs of items that recur with calls to a function of
/// them, the run that saves most first, while any saves anything (a run of
/// `n` ops found `k` times saves `k n - 2 k - n - 3`: each becomes `@f !`,
/// and the function takes `@f : ;` as well). A run can be one only if what
/// `acc` holds when it starts doesn't matter (in the function it's the
/// function's address), it uses `*` and `&` evenly, it defines no functions,
/// and it doesn't split a call from the label that says what it calls. The
/// functions go at the end of the program, and their own runs are looked at
/// too. `kept` functions are left as they are.
fn outline(items: &mut Vec<Item>, kept: &HashSet<Label>) {
    let mut taken = HashSet::new();
    let mut uses = HashMap::new();
    references(items, &mut uses);
    taken.extend(uses.keys().copied());
    let mut defs = HashMap::new();
    functions(items, &mut defs);
    taken.extend(defs.keys().copied());
    let mut made = 0usize;

    /// How a run of items treats `acc`, `*`/`&`, and whether it can be one.
    fn flat(item: &Item) -> Vec<Op> {
        let mut ops = vec![];
        flatten(vec![item.clone()], &mut ops);
        ops
    }
    fn hash(ops: &[Op], h: &mut u64) {
        for op in ops {
            let mut x = std::collections::hash_map::DefaultHasher::new();
            std::hash::Hash::hash(&format!("{op:?}"), &mut x);
            *h = h.rotate_left(5) ^ std::hash::Hasher::finish(&x);
            *h = h.wrapping_mul(0x9e37_79b9_7f4a_7c15);
        }
    }
    /// Whether `*` and `&` are even in `ops`, never going below where they
    /// start.
    fn even(ops: &[Op]) -> bool {
        let mut depth = 0i64;
        for op in ops {
            match op {
                Op::Deref => depth += 1,
                Op::Refer => {
                    depth -= 1;
                    if depth < 0 {
                        return false;
                    }
                }
                _ => {}
            }
        }
        depth == 0
    }
    // each block (a sequence of items) to look in, by a path of indices:
    // the program's, its loops', and the functions' (but kept ones)
    fn blocks(items: &[Item], path: &mut Vec<usize>, kept: &HashSet<Label>, out: &mut Vec<Vec<usize>>) {
        out.push(path.clone());
        for (i, item) in items.iter().enumerate() {
            match item {
                Item::Loop(body) => {
                    path.push(i);
                    blocks(body, path, kept, out);
                    path.pop();
                }
                Item::Func(l, body) if !kept.contains(l) => {
                    path.push(i);
                    blocks(body, path, kept, out);
                    path.pop();
                }
                _ => {}
            }
        }
    }
    fn block<'a>(items: &'a [Item], path: &[usize]) -> &'a [Item] {
        match path.split_first() {
            None => items,
            Some((&i, rest)) => match &items[i] {
                Item::Loop(body) | Item::Func(_, body) => block(body, rest),
                Item::Op(_) => unreachable!(),
            },
        }
    }
    loop {
        // the runs, by what they hash to: how many times they're found (not
        // overlapping), how many ops, and one of them
        let mut paths = vec![];
        blocks(items, &mut vec![], kept, &mut paths);
        struct Found {
            count: usize,
            ops: usize,
            /// One of them: its block, start and length.
            at: (usize, usize, usize),
            /// The block the last one counted was in, and where it ended.
            last: (usize, usize),
        }
        let mut found: HashMap<u64, Found> = HashMap::new();
        for (b, path) in paths.iter().enumerate() {
            let seq = block(items, path);
            let flats: Vec<Vec<Op>> = seq.iter().map(flat).collect();
            for start in 0..seq.len() {
                if matches!(seq[start], Item::Op(Op::Call)) {
                    continue;
                }
                let (mut h, mut n, mut written) = (0u64, 0usize, false);
                let mut ops: Vec<Op> = vec![];
                for len in 1..=RUN.min(seq.len() - start) {
                    let item = &seq[start + len - 1];
                    if matches!(item, Item::Func(..)) {
                        break;
                    }
                    // (what acc holds at the start mustn't be read)
                    if !written {
                        let mut stop = false;
                        for op in &flats[start + len - 1] {
                            match op {
                                Op::Set(_) | Op::Label(_) | Op::Load | Op::Where | Op::Read => {
                                    written = true;
                                    break;
                                }
                                Op::Move(_) | Op::Deref | Op::Refer => {}
                                _ => {
                                    stop = true;
                                    break;
                                }
                            }
                        }
                        if stop {
                            break;
                        }
                    }
                    hash(&flats[start + len - 1], &mut h);
                    ops.extend_from_slice(&flats[start + len - 1]);
                    n += flats[start + len - 1].len();
                    if !written || n < 6 || matches!(item, Item::Op(Op::Label(_))) || !even(&ops) {
                        continue;
                    }
                    let key = h ^ (len as u64).wrapping_mul(0x51_7cc1_b727_220a);
                    let e = found.entry(key).or_insert(Found { count: 0, ops: n, at: (b, start, len), last: (usize::MAX, 0) });
                    // (not overlapping one already counted in this block)
                    if e.last.0 != b || start >= e.last.1 {
                        e.count += 1;
                        e.last = (b, start + len);
                    }
                }
            }
        }
        let best = found
            .values()
            .filter(|f| f.count * f.ops > 2 * f.count + f.ops + 3)
            .max_by_key(|f| ((f.count * f.ops) as i64 - (2 * f.count + f.ops + 3) as i64, std::cmp::Reverse(f.at)));
        let Some(&Found { at: (b, start, len), .. }) = best else { break };
        let run: Vec<Item> = block(items, &paths[b])[start..start + len].to_vec();
        let mut want = vec![];
        flatten(run.clone(), &mut want);
        // a name nothing else has
        let label = loop {
            let mut l = [0u8; 16];
            let name = format!("_o{made}");
            made += 1;
            l[..name.len()].copy_from_slice(name.as_bytes());
            if !taken.contains(&l) {
                taken.insert(l);
                break l;
            }
        };
        // every run that's the same (whole items, not overlapping), in every
        // block, becomes a call
        fn replace(items: &mut Vec<Item>, want: &[Op], len: usize, label: Label, kept: &HashSet<Label>) -> usize {
            let mut count = 0;
            let mut i = 0;
            while i + len <= items.len() {
                let mut ops = vec![];
                flatten(items[i..i + len].to_vec(), &mut ops);
                if ops == want {
                    items.splice(i..i + len, [Item::Op(Op::Label(label)), Item::Op(Op::Call)]);
                    count += 1;
                    i += 2;
                } else {
                    i += 1;
                }
            }
            for item in items.iter_mut() {
                match item {
                    Item::Loop(body) => count += replace(body, want, len, label, kept),
                    Item::Func(l, body) if !kept.contains(l) && *l != label => count += replace(body, want, len, label, kept),
                    _ => {}
                }
            }
            count
        }
        let count = replace(items, &want, len, label, kept);
        if count == 0 {
            break;
        }
        items.push(Item::Func(label, run));
        if count < 2 {
            // (one, after all: put it back)
            let Some(Item::Func(_, run)) = items.pop() else { unreachable!() };
            fn restore(items: &mut Vec<Item>, label: Label, run: &[Item]) -> bool {
                for i in 0..items.len() {
                    if matches!(items[i], Item::Op(Op::Label(l)) if l == label) {
                        items.splice(i..i + 2, run.iter().cloned());
                        return true;
                    }
                    if let Item::Loop(body) | Item::Func(_, body) = &mut items[i] {
                        if restore(body, label, run) {
                            return true;
                        }
                    }
                }
                false
            }
            restore(items, label, &run);
            break;
        }
    }
}

/// The routines `asm` writes, which targets may know and do with the
/// machine's own instructions instead (multiplying, dividing, comparing,
/// the bitwise operations, shifting), as they are: a function that is
/// exactly one of them is left as it is, not inlined, so that a target can
/// still tell what it is. (They're about as fast as the VM allows anyway.)
///
/// Each comes in forms that do just the same, by label: as `asm` writes it,
/// then optimized for speed, then for size, on its own (called from
/// anywhere, with everything it leaves read after), which these
/// optimizations leave it in, and which targets that know it know.
pub fn routine_forms() -> &'static HashMap<String, Vec<Vec<Op>>> {
    static FORMS: std::sync::OnceLock<HashMap<String, Vec<Vec<Op>>>> = std::sync::OnceLock::new();
    FORMS.get_or_init(|| {
        let mut forms = HashMap::new();
        for (label, body) in routines() {
            // (called after and before calls to something not in the
            // program: from anywhere, and then anything can be read)
            let mut unknown = [0u8; 16];
            unknown[..9].copy_from_slice(b"_anything");
            let mut ops = vec![Op::Label(unknown), Op::Call, Op::Label(*label), Op::Call, Op::Label(unknown), Op::Call, Op::Label(*label), Op::Func];
            ops.extend(body.iter().copied());
            ops.push(Op::EndFunc);
            let mut all = vec![body.clone()];
            for goal in [Goal::Fast, Goal::Size] {
                let items = optimize(parse(ops.clone()), &Facts::default(), goal, &HashSet::new(), &HashSet::from([*label]));
                let mut defs = HashMap::new();
                functions(&items, &mut defs);
                let mut form = vec![];
                flatten(defs.remove(label).unwrap_or_default(), &mut form);
                all.push(form);
            }
            forms.insert(name(label), all);
        }
        forms
    })
}

/// A label's name.
fn name(l: &Label) -> String {
    l.iter().take_while(|&&c| c != 0).map(|&c| c as char).collect()
}

fn routines() -> &'static HashMap<Label, Vec<Op>> {
    static ROUTINES: std::sync::OnceLock<HashMap<Label, Vec<Op>>> = std::sync::OnceLock::new();
    ROUTINES.get_or_init(|| {
        use super::*;
        let (x, y): (&Location, &Location) = (R1, R2);
        let builds: [fn(&mut Vec<Op>, &Location, &Location); 16] = [
            |o, x, y| mul_assign(o, x, y),
            |o, x, y| lt_assign(o, x, y),
            |o, x, y| ltu_assign(o, x, y),
            |o, x, y| divu_assign(o, x, y),
            |o, x, y| divu_small_assign(o, x, y),
            |o, x, _| and_const(o, x, 255),
            |o, x, _| rsh_const(o, x, 3),
            |o, x, _| rshu_const(o, x, 3),
            |o, x, _| lsh_const(o, x, 20),
            |o, x, y| and_assign(o, x, y),
            |o, x, y| or_assign(o, x, y),
            |o, x, y| xor_assign(o, x, y),
            |o, x, _| and_const(o, x, 5),
            |o, x, _| or_const(o, x, 5),
            |o, x, _| xor_const(o, x, 5),
            |o, x, y| div_assign(o, x, y),
        ];
        let mut out = HashMap::new();
        for build in builds {
            let mut ops = vec![];
            build(&mut ops, x, y);
            let mut found = HashMap::new();
            functions(&parse(ops), &mut found);
            for (label, body) in found {
                let mut ops = vec![];
                flatten(body, &mut ops);
                out.insert(label, ops);
            }
        }
        out
    })
}

/// The functions in `items` that are exactly routines `asm` writes, in
/// one of their forms (see `routine_forms`).
fn routines_in(items: &[Item]) -> HashSet<Label> {
    let mut defs = HashMap::new();
    functions(items, &mut defs);
    let forms = routine_forms();
    defs.into_iter()
        .filter(|(l, body)| {
            let mut ops = vec![];
            flatten(body.clone(), &mut ops);
            forms.get(&name(l)).is_some_and(|f| f.contains(&ops))
        })
        .map(|(l, _)| l)
        .collect()
}

/// An op, a loop, or a function's definition.
#[derive(Clone)]
enum Item {
    Op(Op),
    Loop(Vec<Item>),
    Func(Label, Vec<Item>),
}

type Label = [u8; 16];

fn parse(ops: Vec<Op>) -> Vec<Item> {
    fn seq(ops: &mut std::iter::Peekable<std::vec::IntoIter<Op>>) -> Vec<Item> {
        let mut items: Vec<Item> = vec![];
        while let Some(op) = ops.next() {
            match op {
                Op::While => items.push(Item::Loop(seq(ops))),
                Op::EndWhile | Op::EndFunc => return items,
                Op::Func => {
                    // its label is the op before it
                    let label = match items.pop() {
                        Some(Item::Op(Op::Label(l))) => l,
                        _ => [0; 16],
                    };
                    items.push(Item::Func(label, seq(ops)));
                }
                op => items.push(Item::Op(op)),
            }
        }
        items
    }
    seq(&mut ops.into_iter().peekable())
}

fn flatten(items: Vec<Item>, out: &mut Vec<Op>) {
    for item in items {
        match item {
            Item::Op(op) => out.push(op),
            Item::Loop(body) => {
                out.push(Op::While);
                flatten(body, out);
                out.push(Op::EndWhile);
            }
            Item::Func(label, body) => {
                out.push(Op::Label(label));
                out.push(Op::Func);
                flatten(body, out);
                out.push(Op::EndFunc);
            }
        }
    }
}

/// Drops ops that only set `acc` when nothing reads it before it's set
/// again, merges neighbouring moves, and drops moves of 0.
fn cleanup(mut ops: Vec<Op>) -> Vec<Op> {
    // whether acc is read before being set, going backwards; anything that
    // starts or ends a jump or a function could lead anywhere, so it reads
    let mut live = true;
    let mut keep = vec![true; ops.len()];
    for (i, op) in ops.iter().enumerate().rev() {
        match op {
            Op::Set(_) | Op::Label(_) | Op::Load | Op::Where => {
                keep[i] = live;
                live = false;
            }
            Op::Read => live = false,
            Op::Move(_) | Op::Deref | Op::Refer => {}
            _ => live = true,
        }
    }
    let mut keep = keep.into_iter();
    ops.retain(|_| keep.next().unwrap());
    let mut out: Vec<Op> = vec![];
    for op in ops {
        if let (Some(Op::Move(m)), Op::Move(n)) = (out.last(), &op) {
            let sum = m + n;
            out.pop();
            if sum != 0 {
                out.push(Op::Move(sum));
            }
            continue;
        }
        if op != Op::Move(0) {
            out.push(op);
        }
    }
    out
}

fn size(items: &[Item]) -> usize {
    items
        .iter()
        .map(|i| match i {
            Item::Op(_) => 1,
            Item::Loop(b) => 2 + size(b),
            Item::Func(_, b) => 3 + size(b),
        })
        .sum()
}

/// Every function definition, by label, wherever it is.
fn functions(items: &[Item], out: &mut HashMap<Label, Vec<Item>>) {
    for i in items {
        match i {
            Item::Func(l, body) => {
                out.insert(*l, body.clone());
                functions(body, out);
            }
            Item::Loop(body) => functions(body, out),
            Item::Op(_) => {}
        }
    }
}

/// How many times each label is used other than to define a function, and
/// how many of those are calls (the label right before `!`).
fn references(items: &[Item], uses: &mut HashMap<Label, (usize, usize)>) {
    for (k, i) in items.iter().enumerate() {
        match i {
            Item::Op(Op::Label(l)) => {
                let e = uses.entry(*l).or_default();
                e.0 += 1;
                if matches!(items.get(k + 1), Some(Item::Op(Op::Call))) {
                    e.1 += 1;
                }
            }
            Item::Loop(body) | Item::Func(_, body) => references(body, uses),
            Item::Op(_) => {}
        }
    }
}

/// Whether a function's body calls it directly.
fn calls_itself(label: &Label, body: &[Item]) -> bool {
    let mut uses = HashMap::new();
    references(body, &mut uses);
    uses.contains_key(label)
}

fn has_loops(items: &[Item]) -> bool {
    items.iter().any(|i| match i {
        Item::Loop(_) => true,
        Item::Func(_, body) => has_loops(body),
        Item::Op(_) => false,
    })
}

fn defines_functions(items: &[Item]) -> bool {
    items.iter().any(|i| match i {
        Item::Func(..) => true,
        Item::Loop(body) => defines_functions(body),
        Item::Op(_) => false,
    })
}

/// The most ops a function can have to be inlined wherever it's called,
/// for speed (for size, only ones of a single op, which take no more room
/// than the call). For speed, only functions without loops are: a call
/// costs a few steps, next to which a loop's are many, and targets can
/// often tell what a function with a loop does (that its effect is linear,
/// say) and do it another way, where they couldn't with it spread through
/// its callers.
const INLINE: usize = 64;

/// Replaces `@f !` with `@f` and `f`'s body, for small functions and ones
/// called once (keeping the label leaves `acc` as the call would have).
fn inline(items: &mut Vec<Item>, goal: Goal, kept: &HashSet<Label>, pinned: &HashSet<Label>) -> bool {
    let most = if goal == Goal::Fast { INLINE } else { 1 };
    let mut defs = HashMap::new();
    functions(items, &mut defs);
    let mut uses = HashMap::new();
    references(items, &mut uses);
    let candidates: HashMap<Label, Vec<Item>> = defs
        .into_iter()
        .filter(|(l, body)| {
            let (refs, calls) = uses.get(l).copied().unwrap_or_default();
            !kept.contains(l)
                && !pinned.contains(l)
                && !calls_itself(l, body)
                && !defines_functions(body)
                && calls > 0
                && (goal == Goal::Size || !has_loops(body))
                && (size(body) <= most || (refs == 1 && calls == 1))
        })
        .collect();
    if candidates.is_empty() {
        return false;
    }
    fn walk(items: &mut Vec<Item>, inside: Option<Label>, candidates: &HashMap<Label, Vec<Item>>, kept: &HashSet<Label>) -> bool {
        let mut changed = false;
        let old = std::mem::take(items);
        let mut iter = old.into_iter().peekable();
        while let Some(item) = iter.next() {
            match item {
                Item::Op(Op::Label(l)) if Some(l) != inside && candidates.contains_key(&l) && matches!(iter.peek(), Some(Item::Op(Op::Call))) => {
                    iter.next();
                    items.push(Item::Op(Op::Label(l)));
                    items.extend(candidates[&l].clone());
                    changed = true;
                }
                Item::Loop(mut body) => {
                    changed |= walk(&mut body, inside, candidates, kept);
                    items.push(Item::Loop(body));
                }
                Item::Func(l, mut body) => {
                    if !kept.contains(&l) {
                        changed |= walk(&mut body, Some(l), candidates, kept);
                    }
                    items.push(Item::Func(l, body));
                }
                item => items.push(item),
            }
        }
        changed
    }
    walk(items, None, &candidates, kept)
}

/// Drops ops that only set `acc` where nothing reads it before it's set
/// again; `live` says whether it's read after `items`.
fn dead_acc(items: &mut Vec<Item>, mut live: bool, kept: &HashSet<Label>) -> bool {
    let mut changed = false;
    let mut keep = vec![true; items.len()];
    for (i, item) in items.iter_mut().enumerate().rev() {
        match item {
            Item::Op(Op::Set(_) | Op::Label(_) | Op::Load | Op::Where) => {
                keep[i] = live;
                live = false;
            }
            Item::Op(Op::Read) => live = false,
            Item::Op(Op::Move(_) | Op::Deref | Op::Refer) => {}
            Item::Op(_) => live = true,
            Item::Loop(body) => {
                // `]` looks at acc, and `[` does
                changed |= dead_acc(body, true, kept);
                live = true;
            }
            Item::Func(l, body) => {
                if !kept.contains(l) {
                    changed |= dead_acc(body, true, kept);
                }
                live = true;
            }
        }
    }
    if keep.contains(&false) {
        let mut keep = keep.into_iter();
        items.retain(|_| keep.next().unwrap());
        changed = true;
    }
    changed
}

/// The cells that may be read before they're written, from some point on,
/// as places: frames of reference (0 is where the code started) and
/// offsets in them.
#[derive(Clone, Debug, Default, PartialEq)]
struct Live {
    /// Every cell.
    all: bool,
    /// Every cell that isn't private (anywhere a pointer could lead).
    memory: bool,
    cells: HashSet<(u32, i64)>,
}

impl Live {
    fn everything() -> Live {
        Live { all: true, memory: true, cells: HashSet::new() }
    }

    fn union(&mut self, other: &Live) {
        if self.all {
            return;
        }
        if other.all {
            *self = Live::everything();
            return;
        }
        self.memory |= other.memory;
        self.cells.extend(&other.cells);
    }
}

/// What a node of a sequence's flow graph does to what's live.
enum Effect {
    /// Stores to a place (`None`: through a pointer).
    Store(Option<(u32, i64)>),
    /// Reads a place (`None`: through a pointer).
    Read(Option<(u32, i64)>),
    /// Calls a function (`None`: whatever acc holds), from the first cell
    /// of an absolute frame (`true`) or somewhere else.
    Call(Option<Label>, bool),
    /// Anything could be read here, or what's live after can't be related
    /// to places before (the pointer moved somewhere unknown).
    Everything,
    Nothing,
}

/// The flow graph of a sequence (not into the functions it defines): a node
/// for each op, `[` and `]`, with where it is and what it does.
struct Flow {
    effects: Vec<Effect>,
    /// for `[` and `]`, the other one
    pair: HashMap<usize, usize>,
    frames: u32,
}

impl Flow {
    fn build(items: &[Item], sums: &Summaries) -> Flow {
        let mut flow = Flow { effects: vec![], pair: HashMap::new(), frames: 0 };
        flow.walk(items, Some((0, 0)), sums);
        flow
    }

    /// A place in a new frame of reference, unrelated to those before.
    fn frame(&mut self) -> Option<(u32, i64)> {
        self.frames += 1;
        Some((self.frames, 0))
    }

    /// Adds nodes for `items`, from place `at`; gives the place at the end.
    fn walk(&mut self, items: &[Item], mut at: Option<(u32, i64)>, sums: &Summaries) -> Option<(u32, i64)> {
        // the pointers saved by `*` (`None` inside pointers: those places
        // aren't tracked)
        let mut stack: Vec<Option<(u32, i64)>> = vec![];
        for (i, item) in items.iter().enumerate() {
            match item {
                Item::Op(Op::Move(n)) => {
                    at = at.map(|(f, d)| (f, d + n));
                    self.effects.push(Effect::Nothing);
                }
                Item::Op(Op::Store) => self.effects.push(Effect::Store(at)),
                Item::Op(Op::Load | Op::Add) => self.effects.push(Effect::Read(at)),
                Item::Op(Op::Deref) => {
                    self.effects.push(Effect::Read(at));
                    stack.push(at);
                    at = None;
                }
                Item::Op(Op::Refer) => match stack.pop() {
                    Some(p) => {
                        at = p;
                        self.effects.push(Effect::Nothing);
                    }
                    None => {
                        self.effects.push(Effect::Everything);
                        at = self.frame();
                    }
                },
                Item::Op(Op::Call) => {
                    let callee = callee(items, i);
                    self.effects.push(Effect::Call(callee, at == Some((0, 0))));
                    if !sums.balanced(callee) {
                        at = self.frame();
                        stack.iter_mut().for_each(|p| *p = None);
                    }
                }
                Item::Op(_) => self.effects.push(Effect::Nothing),
                Item::Func(..) => {}
                Item::Loop(body) => {
                    let open = self.effects.len();
                    let comes_back = at.is_some() && moves_back(body, sums);
                    if comes_back {
                        self.effects.push(Effect::Nothing);
                        self.walk(body, at, sums);
                        self.effects.push(Effect::Nothing);
                    } else {
                        // each time round starts somewhere else
                        self.effects.push(Effect::Everything);
                        let inner = self.frame();
                        self.walk(body, inner, sums);
                        self.effects.push(Effect::Everything);
                        at = self.frame();
                        stack.iter_mut().for_each(|p| *p = None);
                    }
                    let close = self.effects.len() - 1;
                    self.pair.insert(open, close);
                    self.pair.insert(close, open);
                }
            }
        }
        at
    }
}

/// The strongly connected components of a graph (Tarjan's algorithm), each
/// before any that lead to it.
fn components(edges: &[HashSet<usize>]) -> Vec<Vec<usize>> {
    struct Search<'a> {
        edges: &'a [HashSet<usize>],
        index: Vec<Option<usize>>,
        low: Vec<usize>,
        on_stack: Vec<bool>,
        stack: Vec<usize>,
        next: usize,
        out: Vec<Vec<usize>>,
    }
    impl Search<'_> {
        fn visit(&mut self, v: usize) {
            self.index[v] = Some(self.next);
            self.low[v] = self.next;
            self.next += 1;
            self.stack.push(v);
            self.on_stack[v] = true;
            for &w in self.edges[v].iter() {
                match self.index[w] {
                    None => {
                        self.visit(w);
                        self.low[v] = self.low[v].min(self.low[w]);
                    }
                    Some(i) if self.on_stack[w] => self.low[v] = self.low[v].min(i),
                    Some(_) => {}
                }
            }
            if Some(self.low[v]) == self.index[v] {
                let mut group = vec![];
                loop {
                    let w = self.stack.pop().expect("on the stack");
                    self.on_stack[w] = false;
                    group.push(w);
                    if w == v {
                        break;
                    }
                }
                self.out.push(group);
            }
        }
    }
    let n = edges.len();
    let mut search = Search { edges, index: vec![None; n], low: vec![0; n], on_stack: vec![false; n], stack: vec![], next: 0, out: vec![] };
    for v in 0..n {
        if search.index[v].is_none() {
            search.visit(v);
        }
    }
    search.out
}

/// The calls a sequence makes (not in the functions it defines): to what,
/// as `callee` sees it.
fn calls_in(items: &[Item]) -> Vec<Option<Label>> {
    let mut out = vec![];
    for (i, item) in items.iter().enumerate() {
        match item {
            Item::Op(Op::Call) => out.push(callee(items, i)),
            Item::Loop(body) => out.extend(calls_in(body)),
            _ => {}
        }
    }
    out
}

/// What liveness found in a sequence: its dead stores (by node), and for
/// each call, what it calls and what's live after it.
struct Liveness {
    dead: HashSet<usize>,
    calls: Vec<(Option<Label>, Live)>,
    /// What's live where it starts.
    entry: Live,
}

/// Works out what's live in a sequence, given what's live after it.
/// `absolute` says whether the
/// sequence starts at the first cell (so private cells are known there).
fn liveness(items: &[Item], end: &Live, absolute: bool, sums: &Summaries, reads: &HashMap<Label, Live>) -> Liveness {
    let flow = Flow::build(items, sums);
    let n = flow.effects.len();
    let private = |p: &(u32, i64)| absolute && p.0 == 0 && sums.private(p.1);
    let contains = |live: &Live, p: &(u32, i64)| live.all || live.cells.contains(p) || (live.memory && !private(p));
    let successors = |i: usize| -> [Option<usize>; 2] {
        // `[` can skip past its `]`, and `]` go back to after its `[`
        match flow.pair.get(&i) {
            Some(&j) if j > i => [Some(i + 1), Some(j + 1)],
            Some(&j) => [Some(j + 1), Some(i + 1)],
            None => [Some(i + 1), None],
        }
    };
    let mut predecessors: Vec<Vec<usize>> = vec![vec![]; n + 1];
    for i in 0..n {
        for s in successors(i).into_iter().flatten() {
            predecessors[s].push(i);
        }
    }
    // what's live before each node; node n is the end
    let mut before: Vec<Option<Live>> = vec![None; n + 1];
    before[n] = Some(end.clone());
    let after = |before: &Vec<Option<Live>>, i: usize| -> Live {
        let mut out = Live::default();
        for s in successors(i).into_iter().flatten() {
            if let Some(l) = &before[s] {
                out.union(l);
            }
        }
        out
    };
    let mut work: Vec<usize> = (0..n).collect();
    let mut queued = vec![true; n + 1];
    while let Some(i) = work.pop() {
        queued[i] = false;
        let mut live = after(&before, i);
        match &flow.effects[i] {
            Effect::Store(Some(p)) => {
                live.cells.remove(p);
            }
            Effect::Read(Some(p)) => {
                if !live.all {
                    live.cells.insert(*p);
                }
            }
            Effect::Read(None) => live.memory = true,
            Effect::Call(callee, from_start) => {
                // the callee reads the private cells it reads before it
                // writes them, and anything else
                let targets: Option<Vec<Label>> = match callee {
                    Some(l) => Some(vec![*l]),
                    None if sums.facts.labels_only => Some(sums.taken.iter().copied().collect()),
                    None => None,
                };
                let exposed = targets.filter(|_| absolute && *from_start).and_then(|ts| {
                    let mut exposed = Live { all: false, memory: true, cells: HashSet::new() };
                    for t in ts {
                        exposed.union(reads.get(&t)?);
                    }
                    Some(exposed)
                });
                match exposed {
                    Some(exposed) => live.union(&exposed),
                    None => live = Live::everything(),
                }
            }
            Effect::Everything => live = Live::everything(),
            Effect::Store(None) | Effect::Nothing => {}
        }
        if before[i].as_ref() != Some(&live) {
            before[i] = Some(live);
            for &p in &predecessors[i] {
                if !queued[p] {
                    queued[p] = true;
                    work.push(p);
                }
            }
        }
    }
    let entry = if n == 0 { end.clone() } else { before[0].clone().unwrap_or_default() };
    let mut out = Liveness { dead: HashSet::new(), calls: vec![], entry };
    for i in 0..n {
        match &flow.effects[i] {
            Effect::Store(Some(p)) if !contains(&after(&before, i), p) => {
                out.dead.insert(i);
            }
            Effect::Call(callee, from_start) => {
                let live = after(&before, i);
                // as the callee sees it: places are cells if this is
                // absolute and the call is from the first cell
                let seen = if absolute && *from_start {
                    Live { all: live.all, memory: true, cells: live.cells.iter().filter(|p| private(p)).copied().collect() }
                } else {
                    Live::everything()
                };
                out.calls.push((*callee, seen));
            }
            _ => {}
        }
    }
    out
}

/// Removes stores whose values are never read: overwritten first on every
/// path, or not read before the program ends. What's live when a function
/// returns is what's live after the calls to it (found together, for
/// recursion); a call reads the private cells its callee reads, and
/// anything else, as does a read through a pointer.
fn dead_stores(items: &mut Vec<Item>, sums: &Summaries, kept: &HashSet<Label>) -> bool {
    // every sequence to look at: the program, and each function's body
    fn bodies<'a>(items: &'a [Item], out: &mut Vec<(Label, &'a [Item])>) {
        for item in items {
            match item {
                Item::Func(l, body) => {
                    out.push((*l, body));
                    bodies(body, out);
                }
                Item::Loop(body) => bodies(body, out),
                Item::Op(_) => {}
            }
        }
    }
    let mut funcs = vec![];
    bodies(items, &mut funcs);
    // the sequences, by number: 0 is the program, then each function
    let labels: Vec<Option<Label>> = std::iter::once(None).chain(funcs.iter().map(|(l, _)| Some(*l))).collect();
    let code: Vec<&[Item]> = std::iter::once(&items[..]).chain(funcs.iter().map(|(_, b)| *b)).collect();
    let number: HashMap<Label, usize> = labels.iter().enumerate().filter_map(|(i, l)| l.map(|l| (l, i))).collect();
    let absolute: Vec<bool> = labels.iter().map(|l| l.is_none_or(|l| sums.call(Some(l)).absolute)).collect();
    // the sequences a call can go to
    let targets = |callee: &Option<Label>| -> Vec<usize> {
        match callee {
            Some(l) => number.get(l).into_iter().copied().collect(),
            None if sums.facts.labels_only => sums.taken.iter().filter_map(|l| number.get(l).copied()).collect(),
            None => (1..code.len()).collect(),
        }
    };
    // the sequences that call each one
    let mut callers: Vec<HashSet<usize>> = vec![HashSet::new(); code.len()];
    let mut callees: Vec<HashSet<usize>> = vec![HashSet::new(); code.len()];
    for (i, c) in code.iter().enumerate() {
        for callee in calls_in(c) {
            for t in targets(&callee) {
                callers[t].insert(i);
                callees[i].insert(t);
            }
        }
    }
    // the sequences in groups that call each other, callees' groups first
    let groups = components(&callees);
    let start = Live { all: false, memory: true, cells: HashSet::new() };
    // first, the private cells each function reads before writing them, as
    // it sees them: what's live where it starts, if nothing private is
    // live when it returns (found together, for recursion)
    let mut reads: HashMap<Label, Live> = funcs.iter().map(|(l, _)| (*l, start.clone())).collect();
    for group in &groups {
        loop {
            let mut changed = false;
            for &i in group.iter().filter(|&&i| i != 0) {
                let l = labels[i].expect("a function");
                let entry = if absolute[i] { liveness(code[i], &start, true, sums, &reads).entry } else { Live::everything() };
                if reads[&l] != entry {
                    reads.insert(l, entry);
                    changed = true;
                }
            }
            if !changed {
                break;
            }
        }
    }
    // then what's live when each function returns, as it sees it: what's
    // live after the calls to it (nothing private, to start with; and
    // anything, for a function nothing calls)
    let mut returns: Vec<Live> = (0..code.len())
        .map(|i| if i == 0 { Live::default() } else if callers[i].is_empty() { Live::everything() } else { start.clone() })
        .collect();
    // what each sequence's calls say is live after them, for each callee
    let mut said: Vec<HashMap<usize, Live>> = vec![HashMap::new(); code.len()];
    let mut found: Vec<Option<Liveness>> = (0..code.len()).map(|_| None).collect();
    // callers' groups first, so each function's callers are done before it
    let mut work: Vec<usize> = groups.iter().flatten().copied().collect();
    let mut queued = vec![true; code.len()];
    while let Some(i) = work.pop() {
        queued[i] = false;
        let result = liveness(code[i], &returns[i], absolute[i], sums, &reads);
        let mut says: HashMap<usize, Live> = HashMap::new();
        for (callee, live) in &result.calls {
            for t in targets(callee) {
                let seen = if absolute[t] { live.clone() } else { Live::everything() };
                says.entry(t).or_default().union(&seen);
            }
        }
        let affected: HashSet<usize> = says.keys().chain(said[i].keys()).copied().collect();
        said[i] = says;
        found[i] = Some(result);
        for t in affected {
            if callers[t].is_empty() {
                continue;
            }
            let mut r = start.clone();
            for c in &callers[t] {
                if let Some(l) = said[*c].get(&t) {
                    r.union(l);
                }
            }
            if r != returns[t] {
                returns[t] = r;
                if !queued[t] {
                    queued[t] = true;
                    work.push(t);
                }
            }
        }
    }
    let mut found = found.into_iter().map(|f| f.expect("each looked at"));
    let main = found.next().expect("the program");
    let each: Vec<Liveness> = found.collect();
    let found = (main, each);
    // remove what's dead, numbering the nodes as `Flow::walk` did
    fn remove(items: &mut Vec<Item>, next: &mut usize, dead: &HashSet<usize>) {
        let old = std::mem::take(items);
        for mut item in old {
            match &mut item {
                Item::Func(..) => {}
                Item::Loop(body) => {
                    *next += 1;
                    remove(body, next, dead);
                    *next += 1;
                }
                Item::Op(_) => {
                    let me = *next;
                    *next += 1;
                    if dead.contains(&me) {
                        continue;
                    }
                }
            }
            items.push(item);
        }
    }
    let (main, each) = found;
    let dead: HashMap<Label, HashSet<usize>> = funcs.iter().map(|(l, _)| *l).zip(each.into_iter().map(|e| e.dead)).filter(|(l, _)| !kept.contains(l)).collect();
    let changed = !main.dead.is_empty() || dead.values().any(|d| !d.is_empty());
    fn apply(items: &mut Vec<Item>, dead: &HashMap<Label, HashSet<usize>>) {
        for item in items.iter_mut() {
            match item {
                Item::Func(l, body) => {
                    apply(body, dead);
                    if let Some(d) = dead.get(l) {
                        remove(body, &mut 0, d);
                    }
                }
                Item::Loop(body) => apply(body, dead),
                Item::Op(_) => {}
            }
        }
    }
    apply(items, &dead);
    remove(items, &mut 0, &main.dead);
    changed
}

/// The function a call calls, if it's sure to be the one whose label was
/// last put in `acc` (the item at `call` is the call).
fn callee(items: &[Item], call: usize) -> Option<Label> {
    for item in items[..call].iter().rev() {
        match item {
            Item::Op(Op::Label(l)) => return Some(*l),
            Item::Op(Op::Move(_) | Op::Store | Op::Write | Op::Deref | Op::Refer) => {}
            _ => return None,
        }
    }
    None
}

/// Whether a loop's body always comes back to where it started.
fn moves_back(body: &[Item], sums: &Summaries) -> bool {
    let mut d = 0;
    let mut depth = 0i64;
    for (i, item) in body.iter().enumerate() {
        match item {
            Item::Op(Op::Move(n)) if depth == 0 => d += n,
            Item::Op(Op::Deref) => depth += 1,
            Item::Op(Op::Refer) => {
                depth -= 1;
                if depth < 0 {
                    return false;
                }
            }
            Item::Op(Op::Call) if !sums.balanced(callee(body, i)) => return false,
            Item::Loop(inner) if !moves_back(inner, sums) => return false,
            _ => {}
        }
    }
    d == 0 && depth == 0
}

/// Removes the definitions of functions nothing refers to. Running past a
/// definition can put the function's address in `acc`, so it only goes if
/// something sets `acc` before anything could see it (or the program ends).
fn remove_unused(items: &mut Vec<Item>) -> bool {
    let mut uses = HashMap::new();
    references(items, &mut uses);
    fn walk(items: &mut Vec<Item>, uses: &HashMap<Label, (usize, usize)>, top: bool) -> bool {
        let mut changed = false;
        let mut k = items.len();
        while k > 0 {
            k -= 1;
            let unused = matches!(&items[k], Item::Func(l, _) if !uses.contains_key(l));
            if unused && acc_unseen(&items[k + 1..], top) {
                items.remove(k);
                changed = true;
            }
        }
        for i in items.iter_mut() {
            if let Item::Loop(body) | Item::Func(_, body) = i {
                changed |= walk(body, uses, false);
            }
        }
        changed
    }
    walk(items, &uses, true)
}

/// Whether what `acc` holds before `items` is overwritten before they could
/// look at it (`end` says whether it doesn't matter at their end).
fn acc_unseen(items: &[Item], end: bool) -> bool {
    for item in items {
        match item {
            Item::Op(Op::Set(_) | Op::Label(_) | Op::Load | Op::Read | Op::Where) | Item::Func(..) => return true,
            Item::Op(Op::Move(_) | Op::Store | Op::Deref | Op::Refer) => {}
            _ => return false,
        }
    }
    end
}

/// What the optimizer is told about a program, beyond its ops: promises
/// that let it see further. [`Facts::default`] promises nothing.
#[derive(Clone, Debug, Default)]
pub struct Facts {
    /// Cells, counting from the one the pointer starts at, that no pointer
    /// ever leads to: the program only reaches them by moving, so storing
    /// through a pointer never changes them.
    pub private: std::ops::Range<i64>,
    /// Whether every call is to a function whose address a label put in
    /// acc (no arithmetic on functions' addresses), so a call through an
    /// address that isn't known is to one of the functions whose addresses
    /// the program keeps somewhere.
    pub labels_only: bool,
}

/// Some cells, or all of them.
#[derive(Clone, Debug, PartialEq, Eq)]
enum Cells {
    All,
    Some(std::collections::BTreeSet<i64>),
}

impl Cells {
    fn none() -> Cells {
        Cells::Some(Default::default())
    }

    fn insert(&mut self, c: i64) {
        if let Cells::Some(set) = self {
            set.insert(c);
        }
    }

    fn union(&mut self, other: &Cells) {
        match (&mut *self, other) {
            (Cells::All, _) => {}
            (_, Cells::All) => *self = Cells::All,
            (Cells::Some(a), Cells::Some(b)) => a.extend(b),
        }
    }

    fn contains(&self, c: i64) -> bool {
        match self {
            Cells::All => true,
            Cells::Some(set) => set.contains(&c),
        }
    }
}

/// What calling a function can do.
#[derive(Clone, Debug, PartialEq, Eq)]
struct Summary {
    /// It always returns with the pointer where it was when it was called,
    /// and the pointers `*` saved as they were.
    balanced: bool,
    /// It's only ever called with the pointer at the cell the program
    /// starts at, so where the pointer is in it, relative to where it
    /// started, is which cell it's at.
    absolute: bool,
    /// The private cells it can store to and read (directly or in the
    /// functions it calls).
    writes: Cells,
    reads: Cells,
    /// Whether it can store to cells that aren't private.
    memory: bool,
}

impl Summary {
    /// What's assumed of a function before it's looked at: the best, until
    /// it turns out otherwise.
    fn hopeful() -> Summary {
        Summary { balanced: true, absolute: true, writes: Cells::none(), reads: Cells::none(), memory: false }
    }

    /// A function nothing's known about.
    fn unknown() -> Summary {
        Summary { balanced: false, absolute: false, writes: Cells::All, reads: Cells::All, memory: true }
    }

    fn join(&mut self, other: &Summary) {
        self.balanced &= other.balanced;
        self.absolute &= other.absolute;
        self.writes.union(&other.writes);
        self.reads.union(&other.reads);
        self.memory |= other.memory;
    }
}

/// What's known about each function in a program.
struct Summaries {
    funcs: HashMap<Label, Summary>,
    /// The functions whose addresses the program keeps (uses a label for
    /// other than calling), which a call through an unknown address can
    /// reach.
    taken: HashSet<Label>,
    facts: Facts,
    /// What a call through an unknown address can do.
    indirect: Summary,
    /// What a function outside the program (the host's) can do: it
    /// doesn't move the pointer, but it can do anything else.
    external: Summary,
}

impl Summaries {
    /// What a call can do: to `callee`, or (`None`) to whatever acc holds.
    fn call(&self, callee: Option<Label>) -> &Summary {
        match callee {
            Some(l) => self.funcs.get(&l).unwrap_or(&self.external),
            None => &self.indirect,
        }
    }

    fn balanced(&self, callee: Option<Label>) -> bool {
        self.call(callee).balanced
    }

    /// Works out `indirect` from the functions' summaries.
    fn update_indirect(&mut self) {
        self.indirect = if self.facts.labels_only {
            let mut s = Summary::hopeful();
            for l in &self.taken {
                s.join(self.funcs.get(l).unwrap_or(&self.external));
            }
            s
        } else {
            Summary::unknown()
        };
    }

    fn private(&self, cell: i64) -> bool {
        self.facts.private.contains(&cell)
    }

    /// Works out what each function in `items` can do: everything's assumed
    /// as good as can be, and then made as bad as it turns out to be under
    /// those assumptions, until that holds up.
    fn of(items: &[Item], facts: &Facts) -> Summaries {
        let mut defs = HashMap::new();
        functions(items, &mut defs);
        let taken = taken_labels(items);
        let mut sums = Summaries {
            funcs: defs.keys().map(|l| (*l, Summary::hopeful())).collect(),
            taken,
            facts: facts.clone(),
            indirect: Summary::unknown(),
            external: Summary { balanced: true, ..Summary::unknown() },
        };
        sums.update_indirect();
        loop {
            // whether each function is only called with the pointer at the
            // first cell
            let mut at_start: HashMap<Label, bool> = defs.keys().map(|l| (*l, true)).collect();
            let mut next = HashMap::new();
            let mut main = Summarize { sums: &sums, absolute: true, summary: Summary::hopeful(), sites: vec![], lost: false };
            main.walk(items, Place::Cell(0));
            let mut sites = main.sites;
            for (l, body) in &defs {
                let mut w = Summarize { sums: &sums, absolute: sums.funcs[l].absolute, summary: Summary::hopeful(), sites: vec![], lost: false };
                let end = w.walk(body, Place::Cell(0));
                let mut summary = w.summary;
                summary.balanced = !w.lost && end == Place::Cell(0);
                next.insert(*l, summary);
                sites.extend(w.sites);
            }
            for (callee, at_cell0) in sites {
                let callees: Vec<Label> = match callee {
                    Some(l) => vec![l],
                    None => sums.taken.iter().copied().collect(),
                };
                for l in callees {
                    if let Some(a) = at_start.get_mut(&l) {
                        *a &= at_cell0;
                    }
                }
            }
            for (l, summary) in next.iter_mut() {
                summary.absolute = sums.funcs[l].absolute && at_start[l];
            }
            if next == sums.funcs {
                return sums;
            }
            sums.funcs = next;
            sums.update_indirect();
        }
    }
}

/// The labels a program uses for something other than calling the
/// function right away.
fn taken_labels(items: &[Item]) -> HashSet<Label> {
    let mut out = HashSet::new();
    fn walk(items: &[Item], out: &mut HashSet<Label>) {
        for (i, item) in items.iter().enumerate() {
            match item {
                Item::Op(Op::Label(l)) => {
                    // a call to it, unless something sees acc first
                    let called = items[i + 1..]
                        .iter()
                        .find(|x| !matches!(x, Item::Op(Op::Move(_) | Op::Store | Op::Write | Op::Deref | Op::Refer)));
                    let called = matches!(called, Some(Item::Op(Op::Call)));
                    // (a label right before a function's definition doesn't
                    // count: it's the definition's)
                    let defines = matches!(items.get(i + 1), Some(Item::Func(..)));
                    if !called && !defines {
                        out.insert(*l);
                    }
                }
                Item::Loop(body) | Item::Func(_, body) => walk(body, out),
                Item::Op(_) => {}
            }
        }
    }
    walk(items, &mut out);
    out
}

/// Where the pointer is, as far as working out summaries goes.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum Place {
    /// This many cells from where the code started.
    Cell(i64),
    /// Somewhere a pointer led.
    Pointer,
    /// Anywhere.
    Unknown,
}

/// Works out a summary of some code (`Summaries::of`).
struct Summarize<'a> {
    sums: &'a Summaries,
    /// Whether places relative to where the code started are cells.
    absolute: bool,
    summary: Summary,
    /// The calls it makes: to what, and whether from the first cell.
    sites: Vec<(Option<Label>, bool)>,
    /// Whether it can pop a pointer it didn't save.
    lost: bool,
}

impl Summarize<'_> {
    fn store(&mut self, at: Place) {
        match at {
            Place::Cell(c) if self.absolute && self.sums.private(c) => self.summary.writes.insert(c),
            Place::Cell(_) if self.absolute => self.summary.memory = true,
            Place::Pointer => self.summary.memory = true,
            _ => {
                self.summary.writes = Cells::All;
                self.summary.memory = true;
            }
        }
    }

    fn read(&mut self, at: Place) {
        match at {
            Place::Cell(c) if self.absolute && self.sums.private(c) => self.summary.reads.insert(c),
            Place::Cell(_) if self.absolute => {}
            Place::Pointer => {}
            _ => self.summary.reads = Cells::All,
        }
    }

    fn walk(&mut self, items: &[Item], mut at: Place) -> Place {
        let mut stack: Vec<Place> = vec![];
        for (i, item) in items.iter().enumerate() {
            match item {
                Item::Op(Op::Move(n)) => {
                    if let Place::Cell(c) = at {
                        at = Place::Cell(c + n);
                    }
                }
                Item::Op(Op::Store) => self.store(at),
                Item::Op(Op::Load | Op::Add) => self.read(at),
                Item::Op(Op::Deref) => {
                    self.read(at);
                    stack.push(at);
                    at = Place::Pointer;
                }
                Item::Op(Op::Refer) => match stack.pop() {
                    Some(p) => at = p,
                    None => {
                        self.lost = true;
                        at = Place::Unknown;
                    }
                },
                Item::Op(Op::Call) => {
                    let callee = callee(items, i);
                    let s = self.sums.call(callee);
                    self.summary.writes.union(&s.writes);
                    self.summary.reads.union(&s.reads);
                    self.summary.memory |= s.memory;
                    self.sites.push((callee, self.absolute && at == Place::Cell(0)));
                    if !s.balanced {
                        at = Place::Unknown;
                        stack.iter_mut().for_each(|p| *p = Place::Unknown);
                        self.lost = true;
                    }
                }
                Item::Loop(body) => {
                    if at != Place::Unknown && moves_back(body, self.sums) {
                        self.walk(body, at);
                    } else {
                        // each time round starts somewhere else
                        self.walk(body, Place::Unknown);
                        at = Place::Unknown;
                        stack.iter_mut().for_each(|p| *p = Place::Unknown);
                    }
                }
                Item::Op(_) | Item::Func(..) => {}
            }
        }
        if !stack.is_empty() {
            self.lost = true;
        }
        at
    }
}

/// A place on the tape: a region (0 is where the pointer reaches by moving
/// from where the code started; others are where a `*` led), and an offset.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
struct Pos {
    region: u32,
    offset: i64,
}

impl Pos {
    fn moved(self, n: i64) -> Pos {
        Pos { region: self.region, offset: self.offset + n }
    }
}

/// A symbolic value, by number.
type Tok = u32;

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
enum Value {
    Const(u64),
    /// The address of a place.
    Addr(Pos),
    Func(Label),
    /// Some value, unknown but fixed; with whether it's 0 or 1.
    Opaque(u32, bool),
    /// The negation of a value.
    Neg(Tok),
}

#[derive(Default)]
struct Tokens {
    values: Vec<Value>,
    ids: HashMap<Value, Tok>,
    fresh: u32,
    regions: u32,
    /// The region a pointer leads to, by its value: following the same
    /// value always leads to the same place.
    led: HashMap<Tok, u32>,
}

impl Tokens {
    fn get(&mut self, v: Value) -> Tok {
        if let Some(&t) = self.ids.get(&v) {
            return t;
        }
        let t = self.values.len() as Tok;
        self.values.push(v.clone());
        self.ids.insert(v, t);
        t
    }

    fn fresh(&mut self, boolean: bool) -> Tok {
        self.fresh += 1;
        self.get(Value::Opaque(self.fresh, boolean))
    }

    fn region(&mut self) -> u32 {
        self.regions += 1;
        self.regions
    }

    /// Where following a pointer with value `t` leads.
    fn follow(&mut self, t: Tok) -> Pos {
        if let Value::Addr(p) = self.value(t) {
            return *p;
        }
        let region = match self.led.get(&t) {
            Some(&r) => r,
            None => {
                let r = self.region();
                self.led.insert(t, r);
                r
            }
        };
        Pos { region, offset: 0 }
    }

    fn value(&self, t: Tok) -> &Value {
        &self.values[t as usize]
    }

    fn constant(&self, t: Tok) -> Option<u64> {
        match self.value(t) {
            Value::Const(c) => Some(*c),
            _ => None,
        }
    }

    fn is_bool(&self, t: Tok) -> bool {
        matches!(self.value(t), Value::Const(0 | 1) | Value::Opaque(_, true))
    }

    fn neg(&mut self, t: Tok) -> Tok {
        match self.value(t).clone() {
            Value::Const(c) => self.get(Value::Const(c.wrapping_neg())),
            Value::Neg(u) => u,
            _ => self.get(Value::Neg(t)),
        }
    }
}

/// Whether a constant isn't 0 at any width from 16 bits.
fn nonzero(c: u64) -> bool {
    c & 0xffff != 0
}

/// What `#` gives for a constant, if it's the same at every width from 16
/// bits.
fn positive(c: u64) -> Option<u64> {
    if c == 0 || c >= u64::MAX - (1 << 15) + 1 {
        Some(0)
    } else if c < 1 << 15 {
        Some(1)
    } else {
        None
    }
}

/// What's known at a point in the program.
#[derive(Clone)]
struct State {
    /// Where the pointer logically is, and where it actually is (moves are
    /// only made when something needs them).
    pos: Pos,
    real: Pos,
    acc: Tok,
    cells: HashMap<Pos, Tok>,
    /// The pointers `*` has saved since this code started: where to go
    /// back to, and where the pointer it really saved is (if it really ran,
    /// and wasn't turned into a move).
    stack: Vec<(Pos, Option<Pos>)>,
    /// A pointer `*` really saved that `&` has logically gone back to, but
    /// hasn't really: the pointer is still where `*` led, in case another
    /// `*` goes there again before anything needs it back.
    pending: Option<Pos>,
    /// For each region, the lowest and highest places the program has had
    /// the pointer at: the tape is all there between them, so the pointer
    /// can go anywhere in that span without going off it.
    span: HashMap<u32, (i64, i64)>,
    /// Whether places in region 0 are cells: the code started at the first
    /// cell.
    absolute: bool,
}

impl State {
    /// Nothing known, with the pointer at offset 0 of region 0.
    fn fresh(tokens: &mut Tokens) -> State {
        State::at(Pos { region: 0, offset: 0 }, tokens)
    }

    fn at(pos: Pos, tokens: &mut Tokens) -> State {
        let span = HashMap::from([(pos.region, (pos.offset, pos.offset))]);
        State { pos, real: pos, acc: tokens.fresh(false), cells: HashMap::new(), stack: vec![], pending: None, span, absolute: false }
    }

    /// Notes that the program has had the pointer at `p`.
    fn visit(&mut self, p: Pos) {
        let e = self.span.entry(p.region).or_insert((p.offset, p.offset));
        *e = (e.0.min(p.offset), e.1.max(p.offset));
    }

    fn reached(&self, p: Pos) -> bool {
        self.span.get(&p.region).is_some_and(|&(lo, hi)| lo <= p.offset && p.offset <= hi)
    }

    /// Nothing known, and the pointer somewhere unrelated to anywhere before
    /// (a new region, so places from before can't be confused with it).
    fn lost(tokens: &mut Tokens) -> State {
        let region = tokens.region();
        State::at(Pos { region, offset: 0 }, tokens)
    }
}

struct Optimizer<'a> {
    tokens: Tokens,
    sums: Summaries,
    /// The functions it leaves as they are (see `routines`).
    kept: &'a HashSet<Label>,
    changed: bool,
}

impl Optimizer<'_> {
    fn program(&mut self, items: Vec<Item>) -> Vec<Item> {
        let mut start = State::fresh(&mut self.tokens);
        start.absolute = true;
        self.sequence(items, start, 0).0
    }

    /// Whether `p` is a private cell, which only stores right to it change.
    fn private(&self, s: &State, p: Pos) -> bool {
        s.absolute && p.region == 0 && self.sums.private(p.offset)
    }

    /// Moves the pointer to where it logically is, if it isn't there yet.
    fn settle(&mut self, s: &mut State, out: &mut Vec<Item>) {
        if s.real.region != s.pos.region {
            self.flush(s, out);
        }
        if s.real != s.pos {
            debug_assert_eq!(s.real.region, s.pos.region);
            out.push(Item::Op(Op::Move(s.pos.offset - s.real.offset)));
            s.real = s.pos;
        }
    }

    /// Reads the cell the pointer is logically at, which holds `t`, with
    /// `op` (a load or an add): from the nearest cell that holds the same,
    /// where the pointer can move to.
    fn load(&mut self, s: &mut State, out: &mut Vec<Item>, unread: &mut HashMap<Pos, usize>, op: Op, t: Tok) {
        let here = s.pos;
        let mut at = here;
        if s.real.region == here.region {
            let distance = |q: &Pos| (q.offset - s.real.offset).abs();
            for (q, &u) in &s.cells {
                // (nearest first, then where it logically is, then lowest,
                // so the choice doesn't depend on the order cells come in)
                if u == t && q.region == here.region && s.reached(*q) && (distance(q), *q != here, q.offset) < (distance(&at), at != here, at.offset) {
                    at = *q;
                }
            }
        }
        if at == here {
            self.settle(s, out);
        } else {
            out.push(Item::Op(Op::Move(at.offset - s.real.offset)));
            s.real = at;
        }
        self.read(s, unread, at);
        out.push(Item::Op(op));
    }

    /// Really goes back to a pointer `&` has logically gone back to.
    fn flush(&mut self, s: &mut State, out: &mut Vec<Item>) {
        if let Some(q) = s.pending.take() {
            out.push(Item::Op(Op::Refer));
            s.real = q;
        }
    }

    /// Forgets what's known about cells that a store at `p` could change:
    /// just that one, if it's private; else the others that might be it
    /// (anywhere a pointer could lead, but not elsewhere in its region).
    fn clobber(&self, s: &mut State, p: Pos) {
        if self.private(s, p) {
            s.cells.remove(&p);
            return;
        }
        let cells = std::mem::take(&mut s.cells);
        s.cells = cells.into_iter().filter(|(q, _)| self.private(s, *q) || (q.region == p.region && q.offset != p.offset)).collect();
    }

    /// Notes that the cell at `p` has been read, which reads what was
    /// stored there, and maybe what was stored where a pointer led.
    fn read(&self, s: &State, unread: &mut HashMap<Pos, usize>, p: Pos) {
        if self.private(s, p) {
            unread.remove(&p);
        } else {
            unread.retain(|q, _| *q != p && (self.private(s, *q) || q.region == p.region));
        }
    }

    fn cell(&mut self, s: &mut State, p: Pos) -> Tok {
        if let Some(&t) = s.cells.get(&p) {
            return t;
        }
        let t = self.tokens.fresh(false);
        s.cells.insert(p, t);
        t
    }

    fn drop_op(&mut self) {
        self.changed = true;
    }

    /// Optimizes a sequence, from state `s`; gives the ops and the state at
    /// its end (`None` if where the pointer is can't be told any more). At
    /// the end, the pointer is put `delta` cells past where it logically is.
    fn sequence(&mut self, items: Vec<Item>, mut s: State, delta: i64) -> (Vec<Item>, Option<State>) {
        let mut out: Vec<Item> = vec![];
        // for each `*`, whether its `&` comes before anything this can't see
        // through (a loop, a call, or the end), so it can become a move
        let matched = matched_derefs(&items);
        // stores nothing's read since, by place: where they are in `out`
        let mut unread: HashMap<Pos, usize> = HashMap::new();
        let mut dead: HashSet<usize> = HashSet::new();
        let mut lost = false;
        for (index, item) in items.into_iter().enumerate() {
            let op = match item {
                Item::Op(op) => op,
                Item::Func(label, body) if self.kept.contains(&label) => {
                    out.push(Item::Func(label, body));
                    s.acc = self.tokens.fresh(false);
                    continue;
                }
                Item::Func(label, body) => {
                    let mut fresh = State::fresh(&mut self.tokens);
                    fresh.absolute = self.sums.call(Some(label)).absolute;
                    let (body, _) = self.sequence(body, fresh, 0);
                    out.push(Item::Func(label, body));
                    // its label, run on the way past, may leave its address
                    // in acc (or not: backends differ)
                    s.acc = self.tokens.fresh(false);
                    continue;
                }
                Item::Loop(body) => {
                    unread.clear();
                    let zero = self.tokens.get(Value::Const(0));
                    if s.acc == zero {
                        // never entered
                        self.drop_op();
                        continue;
                    }
                    // `[` and `]` only look at acc, so the pointer can be
                    // anywhere, as long as it's the same place relative to
                    // where it logically is each time round: where the body
                    // first needs it, so that only its end has to move it
                    // (a body that doesn't come back would take the pointer
                    // places the program never goes, though: off the tape,
                    // maybe, so for those it's where the program has it)
                    // (and the place the body first needs it might be off
                    // the tape if it never runs, unless the program's been
                    // further than that already)
                    self.flush(&mut s, &mut out);
                    let comes_back = moves_back(&body, &self.sums);
                    let home = match first_use(&body) {
                        _ if !comes_back => s.pos,
                        Some(d) if s.reached(s.pos.moved(d)) => s.pos.moved(d),
                        Some(_) => s.pos,
                        None => s.real,
                    };
                    if s.real != home {
                        out.push(Item::Op(Op::Move(home.offset - s.real.offset)));
                        s.real = home;
                    }
                    let delta = home.offset - s.pos.offset;
                    let entered = match self.tokens.value(s.acc) {
                        Value::Const(c) => nonzero(*c),
                        Value::Func(_) => true,
                        _ => false,
                    };
                    // the body starts where the loop does, knowing what's
                    // known about the cells it never writes
                    let here = s.pos;
                    let unwritten: HashMap<Pos, Tok> = match writes(&body) {
                        Some(written) => s
                            .cells
                            .iter()
                            .filter(|(p, _)| written.is_empty() || (p.region == here.region && !written.contains(&(p.offset - here.offset))))
                            .map(|(p, t)| (*p, *t))
                            .collect(),
                        None => HashMap::new(),
                    };
                    // and for a loop with no loops inside, whatever else
                    // turns out to be the same at the end of its body as at
                    // its start (assumed of everything known, then checked,
                    // dropping what isn't, until it all holds)
                    let innermost = !body.iter().any(|i| matches!(i, Item::Loop(_) | Item::Func(..)));
                    let mut known = if innermost { s.cells.clone() } else { unwritten.clone() };
                    let (body, end) = loop {
                        let changed = self.changed;
                        let mut inner = State::at(here, &mut self.tokens);
                        inner.real = home;
                        inner.absolute = s.absolute;
                        inner.cells = known.clone();
                        // (a body that doesn't come back starts somewhere
                        // else each time round, so it only knows that's on
                        // the tape)
                        if comes_back {
                            inner.span = s.span.clone();
                        }
                        let (out_body, end) = self.sequence(body.clone(), inner, delta);
                        if known.len() == unwritten.len() {
                            break (out_body, end);
                        }
                        // try again knowing less
                        self.changed = changed;
                        match &end {
                            Some(e) if e.pos == here && e.stack.is_empty() => {
                                let before = known.len();
                                known.retain(|p, t| e.cells.get(p) == Some(t));
                                if known.len() == before {
                                    break (out_body, end);
                                }
                            }
                            _ => known = unwritten.clone(),
                        }
                    };
                    let balanced = end.filter(|e| e.pos == s.pos && e.stack.is_empty());
                    match balanced {
                        Some(e) if entered && e.acc == zero => {
                            // runs exactly once: no brackets needed
                            out.extend(body);
                            s.cells = e.cells;
                            s.acc = zero;
                            self.drop_op();
                        }
                        Some(e) if e.acc == zero && body.iter().all(pure) => {
                            // only works out acc, which ends up 0
                            if s.acc != zero {
                                out.push(Item::Op(Op::Set(0)));
                            }
                            s.acc = zero;
                            self.drop_op();
                        }
                        Some(e) => {
                            out.push(Item::Loop(body));
                            // after the loop: what held before it, if it never
                            // ran, and what holds after its body, if it did;
                            // either way, acc was 0, and so is a cell that held
                            // what it did
                            let zeroed = |cells: &HashMap<Pos, Tok>, acc: Tok| -> HashMap<Pos, Tok> {
                                cells.iter().map(|(p, &t)| (*p, if t == acc { zero } else { t })).collect()
                            };
                            let after = zeroed(&e.cells, e.acc);
                            s.cells = zeroed(&s.cells, s.acc).into_iter().filter(|(p, t)| after.get(p) == Some(t)).collect();
                            s.acc = zero;
                        }
                        None => {
                            out.push(Item::Loop(body));
                            s = State::lost(&mut self.tokens);
                            s.real = s.pos.moved(delta);
                            s.acc = zero;
                            lost = true;
                        }
                    }
                    continue;
                }
            };
            match op {
                Op::Move(n) => {
                    s.pos = s.pos.moved(n);
                    let here = s.pos;
                    s.visit(here);
                }
                Op::Set(c) => {
                    let t = self.tokens.get(Value::Const(c));
                    if s.acc == t {
                        self.drop_op();
                    } else {
                        out.push(Item::Op(Op::Set(c)));
                        s.acc = t;
                    }
                }
                Op::Label(l) => {
                    let t = self.tokens.get(Value::Func(l));
                    if s.acc == t {
                        self.drop_op();
                    } else {
                        out.push(Item::Op(Op::Label(l)));
                        s.acc = t;
                    }
                }
                Op::Load => {
                    let here = s.pos;
                    let t = self.cell(&mut s, here);
                    if s.acc == t {
                        self.drop_op();
                    } else if let Some(c) = self.tokens.constant(t) {
                        // the cell's value is known: no need to read it
                        out.push(Item::Op(Op::Set(c)));
                        s.acc = t;
                        self.drop_op();
                    } else if let Value::Func(l) = *self.tokens.value(t) {
                        out.push(Item::Op(Op::Label(l)));
                        s.acc = t;
                        self.drop_op();
                    } else {
                        self.load(&mut s, &mut out, &mut unread, Op::Load, t);
                        s.acc = t;
                    }
                }
                Op::Store => {
                    if s.cells.get(&s.pos) == Some(&s.acc) {
                        self.drop_op();
                        continue;
                    }
                    self.settle(&mut s, &mut out);
                    if let Some(earlier) = unread.insert(s.pos, out.len()) {
                        dead.insert(earlier);
                    }
                    out.push(Item::Op(Op::Store));
                    let here = s.pos;
                    self.clobber(&mut s, here);
                    s.cells.insert(s.pos, s.acc);
                }
                Op::Add => {
                    let here = s.pos;
                    let c = self.cell(&mut s, here);
                    match (self.tokens.constant(s.acc), self.tokens.constant(c)) {
                        (_, Some(0)) => self.drop_op(),
                        (Some(a), Some(b)) => {
                            let sum = a.wrapping_add(b);
                            out.push(Item::Op(Op::Set(sum)));
                            s.acc = self.tokens.get(Value::Const(sum));
                            self.drop_op();
                        }
                        (Some(0), None) => {
                            // the same as loading it
                            if s.acc != c {
                                self.load(&mut s, &mut out, &mut unread, Op::Load, c);
                                s.acc = c;
                            }
                            self.drop_op();
                        }
                        _ => {
                            self.load(&mut s, &mut out, &mut unread, Op::Add, c);
                            s.acc = self.tokens.fresh(false);
                        }
                    }
                }
                Op::Neg => {
                    let n = self.tokens.neg(s.acc);
                    if let Some(c) = self.tokens.constant(n) {
                        out.push(Item::Op(Op::Set(c)));
                    } else {
                        out.push(Item::Op(Op::Neg));
                    }
                    s.acc = n;
                }
                Op::Positive => {
                    if self.tokens.is_bool(s.acc) {
                        self.drop_op();
                    } else if let Some(r) = self.tokens.constant(s.acc).and_then(positive) {
                        out.push(Item::Op(Op::Set(r)));
                        s.acc = self.tokens.get(Value::Const(r));
                        self.drop_op();
                    } else {
                        out.push(Item::Op(Op::Positive));
                        s.acc = self.tokens.fresh(true);
                    }
                }
                Op::Where => {
                    let t = self.tokens.get(Value::Addr(s.pos));
                    if s.acc == t {
                        self.drop_op();
                    } else {
                        self.settle(&mut s, &mut out);
                        out.push(Item::Op(Op::Where));
                        s.acc = t;
                    }
                }
                Op::Deref => {
                    let target = s.cells.get(&s.pos).map(|&t| self.tokens.value(t).clone());
                    self.read(&s, &mut unread, s.pos);
                    match target {
                        // a move, if its `&` is near and the place it leads
                        // to is reachable by moving
                        Some(Value::Addr(p)) if matched[index] && p.region == s.real.region => {
                            s.stack.push((s.pos, None));
                            s.pos = p;
                            s.visit(p);
                            self.drop_op();
                        }
                        _ => {
                            let here = s.pos;
                            let t = self.cell(&mut s, here);
                            let target = self.tokens.follow(t);
                            match s.pending {
                                // the pointer is still where a `*` of the same
                                // value from the same region led, and that `*`
                                // saved a pointer to go back to there
                                Some(q) if s.real.region == target.region && q.region == here.region && target.region != here.region => {
                                    s.pending = None;
                                    s.stack.push((here, Some(q)));
                                    // (dropping that `&` and this `*`)
                                    self.drop_op();
                                }
                                _ => {
                                    self.flush(&mut s, &mut out);
                                    self.settle(&mut s, &mut out);
                                    out.push(Item::Op(Op::Deref));
                                    s.stack.push((here, Some(here)));
                                    s.real = target;
                                }
                            }
                            s.pos = target;
                            s.visit(target);
                        }
                    }
                }
                Op::Refer => match s.stack.pop() {
                    Some((p, None)) => {
                        s.pos = p;
                        self.drop_op();
                    }
                    Some((p, Some(q))) => {
                        // not yet: only when something needs the pointer
                        // back (see `settle`)
                        self.flush(&mut s, &mut out);
                        s.pending = Some(q);
                        s.pos = p;
                    }
                    None => {
                        // back to somewhere saved before this code: where
                        // that is can't be told
                        self.flush(&mut s, &mut out);
                        self.settle(&mut s, &mut out);
                        unread.clear();
                        out.push(Item::Op(Op::Refer));
                        s = State::lost(&mut self.tokens);
                        lost = true;
                    }
                },
                Op::Call => {
                    self.flush(&mut s, &mut out);
                    self.settle(&mut s, &mut out);
                    let callee = match self.tokens.value(s.acc) {
                        Value::Func(l) => Some(*l),
                        _ => None,
                    };
                    out.push(Item::Op(Op::Call));
                    // the callee changes acc, and the cells it writes (all
                    // that aren't private, if it writes any of those); it
                    // reads the private cells it reads, and any others
                    let summary = self.sums.call(callee);
                    if summary.balanced {
                        let cells = std::mem::take(&mut s.cells);
                        s.cells = cells
                            .into_iter()
                            .filter(|(p, _)| if self.private(&s, *p) { !summary.writes.contains(p.offset) } else { !summary.memory })
                            .collect();
                        unread.retain(|p, _| self.private(&s, *p) && !summary.reads.contains(p.offset));
                        s.acc = self.tokens.fresh(false);
                    } else {
                        // (and what it does to the saved pointers)
                        s = State::lost(&mut self.tokens);
                        lost = true;
                    }
                }
                Op::Read => {
                    out.push(Item::Op(Op::Read));
                    s.acc = self.tokens.fresh(false);
                }
                Op::Write => out.push(Item::Op(Op::Write)),
                Op::While | Op::EndWhile | Op::Func | Op::EndFunc => unreachable!("structured by parse"),
            }
        }
        self.flush(&mut s, &mut out);
        let end = s.pos.moved(delta);
        if s.real != end {
            out.push(Item::Op(Op::Move(end.offset - s.real.offset)));
            s.real = end;
        }
        if !dead.is_empty() {
            self.changed = true;
            out = out.into_iter().enumerate().filter(|(i, _)| !dead.contains(i)).map(|(_, x)| x).collect();
        }
        (out, if lost { None } else { Some(s) })
    }
}

/// Whether an item only changes acc (and moves the pointer).
fn pure(item: &Item) -> bool {
    matches!(item, Item::Op(Op::Set(_) | Op::Label(_) | Op::Load | Op::Add | Op::Neg | Op::Positive | Op::Where | Op::Move(_)))
}

/// The offsets, from where it starts, of the cells a loop's body can
/// store to, if it only stores to cells it reaches by moving (and comes
/// back to where it started).
fn writes(body: &[Item]) -> Option<HashSet<i64>> {
    fn walk(items: &[Item], d: &mut i64, out: &mut HashSet<i64>) -> Option<()> {
        for item in items {
            match item {
                Item::Op(Op::Move(n)) => *d += n,
                Item::Op(Op::Store) => {
                    out.insert(*d);
                }
                Item::Op(Op::Deref | Op::Refer | Op::Call) => return None,
                Item::Op(_) | Item::Func(..) => {}
                Item::Loop(inner) => {
                    let start = *d;
                    walk(inner, d, out)?;
                    if *d != start {
                        return None;
                    }
                }
            }
        }
        Some(())
    }
    let (mut d, mut out) = (0, HashSet::new());
    walk(body, &mut d, &mut out)?;
    (d == 0).then_some(out)
}

/// How far a loop's body moves before it first needs the pointer to be
/// somewhere, if that's before anything else could move it.
fn first_use(body: &[Item]) -> Option<i64> {
    let mut d = 0;
    for item in body {
        match item {
            Item::Op(Op::Move(n)) => d += n,
            Item::Op(Op::Load | Op::Store | Op::Add | Op::Where | Op::Deref | Op::Call) => return Some(d),
            Item::Op(Op::Set(_) | Op::Label(_) | Op::Neg | Op::Positive | Op::Read | Op::Write) => {}
            _ => return None,
        }
    }
    None
}

/// For each item in a sequence, if it's a `*`, whether its `&` comes later
/// in the sequence with only ops in between (no loops, calls or functions).
fn matched_derefs(items: &[Item]) -> Vec<bool> {
    let mut matched = vec![false; items.len()];
    let mut open: Vec<usize> = vec![];
    for (i, item) in items.iter().enumerate() {
        match item {
            Item::Op(Op::Deref) => open.push(i),
            Item::Op(Op::Refer) => {
                if let Some(j) = open.pop() {
                    matched[j] = true;
                }
            }
            Item::Op(Op::Call) | Item::Loop(_) | Item::Func(..) => open.clear(),
            Item::Op(_) => {}
        }
    }
    matched
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::interp::Machine;

    /// A small random number generator (xorshift), so the programs are the
    /// same every run.
    struct Rng(u64);

    impl Rng {
        fn next(&mut self) -> u64 {
            self.0 ^= self.0 << 13;
            self.0 ^= self.0 >> 7;
            self.0 ^= self.0 << 17;
            self.0
        }

        fn below(&mut self, n: u64) -> u64 {
            self.next() % n
        }
    }

    fn label(name: &str) -> Label {
        let mut l = [0; 16];
        l[..name.len()].copy_from_slice(name.as_bytes());
        l
    }

    /// A random sequence of ops, `depth` loops deep at most, calling the
    /// first `funcs` functions; gives how far it moves the pointer, if it's
    /// known.
    fn random(rng: &mut Rng, out: &mut Vec<Op>, len: usize, depth: usize, funcs: usize) -> Option<i64> {
        let mut net = Some(0);
        for _ in 0..len {
            match rng.below(24) {
                0..=2 => {
                    let n = rng.below(7) as i64 - 3;
                    out.push(Op::Move(n));
                    net = net.map(|m| m + n);
                }
                3 => out.push(Op::Set(rng.below(5))),
                4 => out.push(Op::Set(rng.below(3).wrapping_sub(1).wrapping_mul([1, 1 << 15, 1 << 16, 1 << 40][rng.below(4) as usize]))),
                5..=6 => out.push(Op::Load),
                7..=8 => out.push(Op::Store),
                9 => out.push(Op::Add),
                10 => out.push(Op::Neg),
                11 => out.push(Op::Positive),
                12 => out.push(Op::Write),
                13 => out.push(Op::Read),
                14 => {
                    // the address of a nearby cell, kept nearby
                    let (k, j) = (rng.below(5) as i64 - 2, rng.below(5) as i64 - 2);
                    out.extend([Op::Move(k), Op::Where, Op::Move(j - k), Op::Store, Op::Move(-j)]);
                }
                15..=16 => {
                    // through a pointer, mostly one put there just now
                    if rng.below(10) != 0 {
                        let k = rng.below(7) as i64 - 3;
                        out.extend([Op::Move(k), Op::Where, Op::Move(-k), Op::Store]);
                    }
                    out.push(Op::Deref);
                    random(rng, out, 3, 0, 0);
                    out.push(Op::Refer);
                }
                17..=19 if depth > 0 => {
                    // a loop that counts down a cell, so it ends
                    let k = rng.below(5) as i64 - 2;
                    out.extend([Op::Set(rng.below(4)), Op::Move(k), Op::Store, Op::Move(-k), Op::While]);
                    let moved = random(rng, out, 6, depth - 1, funcs);
                    // mostly coming back to where it started
                    match moved {
                        Some(m) if rng.below(4) != 0 => out.push(Op::Move(-m)),
                        _ => net = None,
                    }
                    out.extend([Op::Move(k), Op::Set(1), Op::Neg, Op::Add, Op::Store, Op::Positive, Op::Move(-k)]);
                    out.push(Op::EndWhile);
                }
                20 if depth > 0 => {
                    // an `if`
                    out.push(Op::While);
                    match random(rng, out, 4, depth - 1, funcs) {
                        Some(m) if rng.below(4) != 0 => out.push(Op::Move(-m)),
                        _ => net = None,
                    }
                    out.push(Op::Set(0));
                    out.push(Op::EndWhile);
                }
                21 if funcs > 0 => {
                    out.push(Op::Label(label(&format!("f{}", rng.below(funcs as u64)))));
                    out.push(Op::Call);
                    net = None;
                }
                _ => out.push(Op::Load),
            }
        }
        net
    }

    fn program(rng: &mut Rng) -> Vec<Op> {
        let mut ops = vec![Op::Move(40)];
        let funcs = rng.below(4) as usize;
        for f in 0..funcs {
            // (functions' addresses are where they are in the program, so
            // acc never holds one where the program could look at it: they
            // change when the program does)
            ops.push(Op::Label(label(&format!("f{f}"))));
            ops.push(Op::Func);
            ops.push(Op::Set(rng.below(3)));
            // each calls only the ones before it, so calls end
            let moved = random(rng, &mut ops, 8, 1, f);
            if let Some(m) = moved.filter(|_| rng.below(3) != 0) {
                ops.push(Op::Move(-m));
            } else if rng.below(2) == 0 {
                ops.push(Op::Move(rng.below(3) as i64 - 1));
            }
            ops.push(Op::EndFunc);
            ops.push(Op::Set(rng.below(3)));
        }
        random(rng, &mut ops, 40, 3, funcs);
        ops
    }

    const INPUT: &[u8] = b"\x05\x00\xff\x7f";

    /// Whether `ops` keeps the promise `facts` makes about it (when it runs
    /// on `INPUT`): no pointer leads to a private cell.
    fn keeps(ops: &[Op], facts: &Facts) -> bool {
        let mut pair = vec![0; ops.len()];
        let mut open = vec![];
        let mut funcs = HashMap::new();
        for (i, op) in ops.iter().enumerate() {
            match op {
                Op::While | Op::Func => open.push(i),
                Op::EndWhile | Op::EndFunc => {
                    let j = open.pop().unwrap();
                    (pair[i], pair[j]) = (j, i);
                }
                _ => {}
            }
            if let (Op::Func, Some(Op::Label(l))) = (op, i.checked_sub(1).map(|j| ops[j])) {
                funcs.insert(l, i + 1);
            }
        }
        let mut tape = vec![0i64; 1 << 16];
        let (mut p, mut acc, mut pc, mut steps) = (0i64, 0i64, 0, 0);
        let (mut ptrs, mut rets) = (vec![], vec![]);
        let mut input = INPUT.iter();
        let cell = |p: i64| usize::try_from(p).ok().filter(|&c| c < 1 << 16);
        while pc < ops.len() && steps < 100_000 {
            steps += 1;
            let mut next = pc + 1;
            match ops[pc] {
                Op::Deref => {
                    let Some(c) = cell(p) else { return true };
                    ptrs.push(p);
                    p = tape[c];
                }
                Op::Refer => match ptrs.pop() {
                    Some(q) => p = q,
                    None => return true,
                },
                Op::Where => acc = p,
                Op::Move(n) => p += n,
                Op::Set(n) => acc = n as i64,
                Op::Label(l) => acc = *funcs.get(&l).unwrap_or(&0) as i64,
                Op::Load => acc = cell(p).map_or(0, |c| tape[c]),
                Op::Store => {
                    let Some(c) = cell(p) else { return true };
                    tape[c] = acc;
                }
                Op::Call => {
                    rets.push(next);
                    next = acc as usize;
                }
                Op::Read => acc = input.next().map_or(-1, |&b| b as i64),
                Op::Write => {}
                Op::Add => acc = acc.wrapping_add(cell(p).map_or(0, |c| tape[c])),
                Op::Neg => acc = acc.wrapping_neg(),
                Op::Positive => acc = (acc > 0) as i64,
                Op::While if acc == 0 => next = pair[pc] + 1,
                Op::EndWhile if acc != 0 => next = pair[pc] + 1,
                Op::While | Op::EndWhile => {}
                Op::Func => next = pair[pc] + 1,
                Op::EndFunc => match rets.pop() {
                    Some(r) => next = r,
                    None => return true,
                },
            }
            if !ptrs.is_empty() && facts.private.contains(&p) {
                return false;
            }
            if next >= ops.len() + 1 {
                return true;
            }
            pc = next;
        }
        true
    }

    /// Whether `ops` works on `machine` and prints something else (or fails)
    /// once optimized with `facts` (which it keeps).
    fn breaks(ops: &[Op], machine: &Machine, facts: &Facts, goal: Goal) -> bool {
        let Ok(want) = machine.run(ops, INPUT) else { return false };
        keeps(ops, facts) && machine.run(&opt_with(ops.to_vec(), facts, goal), INPUT).map_or(true, |got| got.output != want.output)
    }

    /// The smallest program found by removing ops from `ops` (keeping its
    /// brackets matched) that `breaks` still.
    fn minimize(mut ops: Vec<Op>, machine: &Machine, facts: &Facts, goal: Goal) -> Vec<Op> {
        let balanced = |ops: &[Op]| {
            // calls only go to labels, and functions have them
            for (i, op) in ops.iter().enumerate() {
                if matches!(op, Op::Call | Op::Func) && !matches!(i.checked_sub(1).map(|j| ops[j]), Some(Op::Label(_))) {
                    return false;
                }
                if matches!(op, Op::Label(_)) && !matches!(ops.get(i + 1), Some(Op::Call | Op::Func)) {
                    return false;
                }
                // and nothing sees a function's address (see `program`)
                if matches!(op, Op::Func | Op::EndFunc) && !matches!(ops.get(i + 1), Some(Op::Set(_))) {
                    return false;
                }
            }
            let mut stack = vec![];
            for op in ops {
                match op {
                    Op::While | Op::Func => stack.push(*op),
                    Op::EndWhile if stack.pop() != Some(Op::While) => return false,
                    Op::EndFunc if stack.pop() != Some(Op::Func) => return false,
                    _ => {}
                }
            }
            stack.is_empty()
        };
        loop {
            let mut smaller = false;
            for len in [8, 4, 2, 1] {
                let mut i = 0;
                while i + len <= ops.len() {
                    let mut candidate = ops.clone();
                    candidate.drain(i..i + len);
                    if balanced(&candidate) && breaks(&candidate, machine, facts, goal) {
                        ops = candidate;
                        smaller = true;
                    } else {
                        i += 1;
                    }
                }
            }
            if !smaller {
                return ops;
            }
        }
    }

    #[test]
    fn optimized_random_programs_print_the_same() {
        // FUZZ=n tries n programs instead (with FUZZ_SEED, from another seed)
        let count = std::env::var("FUZZ").ok().and_then(|n| n.parse().ok()).unwrap_or(6000);
        let seed = std::env::var("FUZZ_SEED").ok().and_then(|n| n.parse().ok()).unwrap_or(0x9e3779b97f4a7c15);
        let mut rng = Rng(seed);
        let (mut compared, mut shorter, mut smaller) = (0, 0, 0);
        // with no promises, and promising that no pointer leads to some of
        // the cells the programs work with (which they keep, mostly)
        let promises = [Facts::default(), Facts { private: 30..38, labels_only: true }];
        for _ in 0..count {
            let ops = program(&mut rng);
            for (facts, goal) in promises.iter().flat_map(|f| [(f, Goal::Fast), (f, Goal::Size)]) {
                if !keeps(&ops, facts) {
                    continue;
                }
                let optimized = opt_with(ops.clone(), facts, goal);
                if goal == Goal::Size {
                    assert!(optimized.len() <= ops.len(), "optimizing for size made {} ops {}", ops.len(), optimized.len());
                    smaller += (optimized.len() < ops.len()) as usize;
                }
                for machine in [Machine::cpu(), Machine::cpu_xlen(16), Machine::c()] {
                    let machine = Machine { max_steps: 100_000, ..machine };
                    // programs that fail (a pointer out of range, say) prove
                    // nothing; ones that work must work the same optimized
                    let Ok(want) = machine.run(&ops, INPUT) else { continue };
                    if breaks(&ops, &machine, facts, goal) {
                        let small = minimize(ops.clone(), &machine, facts, goal);
                        let show = |ops: &[Op]| ops.iter().map(|o| format!("{o:?}")).collect::<Vec<_>>().join(" ");
                        let (a, b) = (machine.run(&small, INPUT), machine.run(&opt_with(small.clone(), facts, goal), INPUT));
                        panic!(
                            "\nwith {facts:?}, for {goal:?}\n{}\n=>\n{}\nprints {:?}, then {:?}",
                            show(&small),
                            show(&opt_with(small.clone(), facts, goal)),
                            a.map(|h| h.output),
                            b.map(|h| h.output)
                        );
                    }
                    let got = machine.run(&optimized, INPUT).unwrap();
                    if goal == Goal::Fast {
                        compared += 1;
                        shorter += (got.steps < want.steps) as usize;
                    }
                }
            }
        }
        eprintln!("{compared} programs compared, {shorter} faster; {smaller} smaller");
        assert!(compared > count / 2, "only {compared} programs ran");
        assert!(shorter * 2 > compared, "only {shorter} of {compared} got faster");
    }

    #[test]
    fn routine_forms_do_what_the_routines_do() {
        // each routine, as `asm` writes it and in its other forms, called
        // with all sorts of values in the cells near the pointer (mostly
        // small, sometimes not, and the counts some count down small), from
        // a cell other than the first: the tape and acc after are the same
        let mut rng = Rng(77);
        let forms = routine_forms();
        let mut labels: Vec<&String> = forms.keys().collect();
        labels.sort();
        let mut compared = 0;
        for name in labels {
            let all = &forms[name];
            assert!(all.len() == 3, "{name}");
            for _ in 0..60 {
                let mut setup = vec![Op::Move(5)];
                for c in 0..20 {
                    let v = match rng.below(4) {
                        0 => rng.below(4),
                        1 => rng.below(300),
                        2 => rng.next(),
                        _ => rng.below(1 << 20).wrapping_neg(),
                    };
                    let v = if c == 7 && rng.below(2) == 0 { rng.below(70) } else { v };
                    setup.extend([Op::Set(v), Op::Store, Op::Move(1)]);
                }
                setup.push(Op::Move(-20));
                let run = |body: &[Op]| {
                    let mut ops = setup.clone();
                    ops.extend([Op::Label(label(name)), Op::Call, Op::Move(30), Op::Store, Op::Move(-35)]);
                    ops.extend([Op::Label(label(name)), Op::Func]);
                    ops.extend(body.iter().copied());
                    ops.push(Op::EndFunc);
                    Machine { max_steps: 200_000, cells: 64, ..Machine::cpu() }.run(&ops, b"").map(|h| h.tape)
                };
                let Ok(want) = run(&all[0]) else { continue };
                for (k, form) in all.iter().enumerate().skip(1) {
                    assert_eq!(run(form), Ok(want.clone()), "{name}, form {k}");
                }
                compared += 1;
            }
        }
        assert!(compared > 300, "only {compared} compared");
    }

    #[test]
    fn optimizing_gives_the_same_ops_every_time() {
        // (hash maps iterate in a different order each time)
        let mut rng = Rng(12345);
        for _ in 0..300 {
            let ops = program(&mut rng);
            let facts = Facts { private: 30..38, labels_only: true };
            for goal in [Goal::Fast, Goal::Size] {
                assert_eq!(opt_with(ops.clone(), &facts, goal), opt_with(ops.clone(), &facts, goal));
            }
        }
    }
}
