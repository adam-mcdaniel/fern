//! Building blocks for writing IR imperatively, for runtime code: variables
//! are allocas, which the optimizer turns into SSA values, and loops and
//! conditionals are closures that build their blocks.

use super::{Function, Value};

pub(in crate::ir) fn var(f: &mut Function, init: Value) -> Value {
    let v = f.alloca(1);
    f.store(v, init);
    v
}

pub(in crate::ir) fn set(f: &mut Function, var: Value, x: Value) {
    f.store(var, x);
}

pub(in crate::ir) fn get(f: &mut Function, var: Value) -> Value {
    f.load(var)
}

pub(in crate::ir) fn k(f: &mut Function, n: i64) -> Value {
    f.int(n)
}

pub(in crate::ir) fn terminated(f: &Function) -> bool {
    f.terminator(f.current()).is_some()
}

/// `if (cond) then`
pub(in crate::ir) fn when(f: &mut Function, cond: Value, then: impl FnOnce(&mut Function)) {
    when_else(f, cond, then, |_| {});
}

/// `if (cond) then else otherwise`
pub(in crate::ir) fn when_else(
    f: &mut Function,
    cond: Value,
    then: impl FnOnce(&mut Function),
    otherwise: impl FnOnce(&mut Function),
) {
    let (yes, no, after) = (f.new_block(0), f.new_block(0), f.new_block(0));
    f.branch(cond, yes, &[], no, &[]);
    f.switch_to(yes);
    then(f);
    if !terminated(f) {
        f.jump(after, &[]);
    }
    f.switch_to(no);
    otherwise(f);
    if !terminated(f) {
        f.jump(after, &[]);
    }
    f.switch_to(after);
}

/// `if (cond) yes else no`, as a value.
pub(in crate::ir) fn choose(f: &mut Function, cond: Value, yes: Value, no: Value) -> Value {
    let (a, b, after) = (f.new_block(0), f.new_block(0), f.new_block(1));
    f.branch(cond, a, &[], b, &[]);
    f.switch_to(a);
    f.jump(after, &[yes]);
    f.switch_to(b);
    f.jump(after, &[no]);
    f.switch_to(after);
    f.block_param(after, 0)
}

/// `while (cond) body`
pub(in crate::ir) fn repeat(f: &mut Function, cond: impl FnOnce(&mut Function) -> Value, body: impl FnOnce(&mut Function)) {
    let (head, inside, after) = (f.new_block(0), f.new_block(0), f.new_block(0));
    f.jump(head, &[]);
    f.switch_to(head);
    let c = cond(f);
    f.branch(c, inside, &[], after, &[]);
    f.switch_to(inside);
    body(f);
    if !terminated(f) {
        f.jump(head, &[]);
    }
    f.switch_to(after);
}

/// `for (i = from; i != to; i++) body(i)`, for `from <= to`. (Comparing
/// with `!=` is cheaper than with `<`.)
pub(in crate::ir) fn each(f: &mut Function, from: Value, to: Value, body: impl FnOnce(&mut Function, Value)) {
    let i = var(f, from);
    repeat(
        f,
        |f| {
            let x = get(f, i);
            f.ne(x, to)
        },
        |f| {
            let x = get(f, i);
            body(f, x);
            let one = k(f, 1);
            let next = f.add(x, one);
            set(f, i, next);
        },
    );
}

/// Sets the `n` cells from `p` on to 0.
pub(in crate::ir) fn clear(f: &mut Function, p: Value, n: Value) {
    let start = k(f, 0);
    each(f, start, n, |f, j| {
        let a = f.index(p, j);
        let zero = k(f, 0);
        f.store(a, zero);
    });
}

/// `p[i]`, for a constant `i`.
pub(in crate::ir) fn field(f: &mut Function, p: Value, i: i64) -> Value {
    let i = k(f, i);
    let a = f.index(p, i);
    f.load(a)
}

pub(in crate::ir) fn set_field(f: &mut Function, p: Value, i: i64, x: Value) {
    let i = k(f, i);
    let a = f.index(p, i);
    f.store(a, x);
}

