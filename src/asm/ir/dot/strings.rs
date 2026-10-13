//! The runtime functions behind strings, added to a module that uses them.
//!
//! A string is a record of its length and then its characters, one per
//! cell, allocated with `gc_alloc`, so the garbage collector frees it once
//! nothing uses it.

use super::super::imperative::*;
use crate::asm::ir::{Function, Module, Value};
use std::collections::HashSet;

/// What each runtime function calls, so that it's added too.
fn needs(name: &str) -> &'static [&'static str] {
    match name {
        "_s_charc" => &["_s_char"],
        "_s_sub1" => &["_s_sub2"],
        "_s_sub2" => &["_s_sub"],
        _ => &[],
    }
}

/// Adds the runtime functions named in `wanted`, and the ones they call.
pub fn add(module: &mut Module, wanted: &HashSet<&'static str>) {
    let mut all: HashSet<&'static str> = HashSet::new();
    let mut work: Vec<&'static str> = wanted.iter().copied().collect();
    while let Some(name) = work.pop() {
        if all.insert(name) {
            work.extend(needs(name));
        }
    }
    let mut all: Vec<&str> = all.into_iter().collect();
    all.sort();
    for name in all {
        let (params, body): (usize, fn(&mut Function)) = match name {
            "_s_cat" => (2, concat),
            "_s_eq" => (2, equal),
            "_s_print" => (1, print),
            "_s_int" => (1, of_int),
            "_s_bool" => (1, of_bool),
            "_s_char" => (2, char_at),
            "_s_sub" => (3, substring),
            "_s_read" => (0, read_line),
            "_s_charc" => (2, char_at_closure),
            "_s_sub1" => (2, substring_closure),
            "_s_sub2" => (2, substring_partial),
            _ => unreachable!("no runtime function {name}"),
        };
        body(module.function(name, params));
    }
}

/// A new string of the characters of `s`.
pub fn literal(f: &mut Function, s: &str) -> Value {
    let size = f.int(s.len() as i64 + 1);
    let r = f.gc_alloc(size);
    let len = f.int(s.len() as i64);
    f.store(r, len);
    for (i, b) in s.bytes().enumerate() {
        let c = f.int(b as i64);
        set_field(f, r, i as i64 + 1, c);
    }
    r
}

/// A string of `n` characters, all 0 for now.
fn new_string(f: &mut Function, n: Value) -> Value {
    let one = k(f, 1);
    let size = f.add(n, one);
    let r = f.gc_alloc(size);
    f.store(r, n);
    r
}

/// The address of character `i` of `s`.
fn char_addr(f: &mut Function, s: Value, i: Value) -> Value {
    let one = k(f, 1);
    let at = f.add(i, one);
    f.index(s, at)
}

/// Copies `n` cells from `from` to `to`.
fn copy(f: &mut Function, from: Value, to: Value, n: Value) {
    let zero = k(f, 0);
    each(f, zero, n, |f, i| {
        let a = f.index(from, i);
        let x = f.load(a);
        let b = f.index(to, i);
        f.store(b, x);
    });
}

fn fail(f: &mut Function, message: &str) {
    f.puts(&format!("error: {message}\n"));
    f.abort();
    let zero = k(f, 0);
    f.ret(zero);
}

fn concat(f: &mut Function) {
    let (a, b) = (f.param(0), f.param(1));
    let la = f.load(a);
    let lb = f.load(b);
    let n = f.add(la, lb);
    let r = new_string(f, n);
    let zero = k(f, 0);
    let (from, to) = (char_addr(f, a, zero), char_addr(f, r, zero));
    copy(f, from, to, la);
    let (from, to) = (char_addr(f, b, zero), char_addr(f, r, la));
    copy(f, from, to, lb);
    f.ret(r);
}

fn equal(f: &mut Function) {
    let (a, b) = (f.param(0), f.param(1));
    let la = f.load(a);
    let lb = f.load(b);
    let differ = f.ne(la, lb);
    let zero = k(f, 0);
    when(f, differ, |f| f.ret(zero));
    each(f, zero, la, |f, i| {
        let pa = char_addr(f, a, i);
        let ca = f.load(pa);
        let pb = char_addr(f, b, i);
        let cb = f.load(pb);
        let differ = f.ne(ca, cb);
        let zero = k(f, 0);
        when(f, differ, |f| f.ret(zero));
    });
    let one = k(f, 1);
    f.ret(one);
}

fn print(f: &mut Function) {
    let s = f.param(0);
    let n = f.load(s);
    let zero = k(f, 0);
    each(f, zero, n, |f, i| {
        let p = char_addr(f, s, i);
        let c = f.load(p);
        f.put_char(c);
    });
    let zero = k(f, 0);
    f.ret(zero);
}

/// The decimal digits of `n`.
fn of_int(f: &mut Function) {
    let n = f.param(0);
    let ten = k(f, 10);
    let zero = k(f, 0);
    // count the digits
    let digits = var(f, zero);
    let rest = var(f, n);
    let one = k(f, 1);
    let first = var(f, one);
    repeat(
        f,
        |f| {
            let r = get(f, rest);
            let zero = k(f, 0);
            let more = f.ne(r, zero);
            let again = get(f, first);
            f.or(more, again)
        },
        |f| {
            let zero = k(f, 0);
            set(f, first, zero);
            let d = get(f, digits);
            let one = k(f, 1);
            let d = f.add(d, one);
            set(f, digits, d);
            let r = get(f, rest);
            let r = f.div(r, ten);
            set(f, rest, r);
        },
    );
    let negative = f.lt(n, zero);
    let d = get(f, digits);
    let len = f.add(d, negative);
    let s = new_string(f, len);
    // then write them from the end
    let at = var(f, len);
    set(f, rest, n);
    let one = k(f, 1);
    set(f, first, one);
    repeat(
        f,
        |f| {
            let r = get(f, rest);
            let zero = k(f, 0);
            let more = f.ne(r, zero);
            let again = get(f, first);
            f.or(more, again)
        },
        |f| {
            let zero = k(f, 0);
            set(f, first, zero);
            let r = get(f, rest);
            let ten = k(f, 10);
            let digit = f.rem(r, ten);
            let digit = f.abs(digit);
            let base = k(f, b'0' as i64);
            let c = f.add(digit, base);
            let i = get(f, at);
            let p = f.index(s, i);
            f.store(p, c);
            let one = k(f, 1);
            let i = f.sub(i, one);
            set(f, at, i);
            let r = f.div(r, ten);
            set(f, rest, r);
        },
    );
    when(f, negative, |f| {
        let minus = k(f, b'-' as i64);
        set_field(f, s, 1, minus);
    });
    f.ret(s);
}

fn of_bool(f: &mut Function) {
    let b = f.param(0);
    when_else(
        f,
        b,
        |f| {
            let s = literal(f, "true");
            f.ret(s);
        },
        |f| {
            let s = literal(f, "false");
            f.ret(s);
        },
    );
    let zero = k(f, 0);
    f.ret(zero);
}

fn char_at(f: &mut Function) {
    let (s, i) = (f.param(0), f.param(1));
    let n = f.load(s);
    let zero = k(f, 0);
    let below = f.lt(i, zero);
    let above = f.ge(i, n);
    let out = f.or(below, above);
    when(f, out, |f| fail(f, "string index out of range"));
    let p = char_addr(f, s, i);
    let c = f.load(p);
    f.ret(c);
}

fn substring(f: &mut Function) {
    let (s, from, to) = (f.param(0), f.param(1), f.param(2));
    let n = f.load(s);
    let zero = k(f, 0);
    let below = f.lt(from, zero);
    let above = f.gt(to, n);
    let backwards = f.gt(from, to);
    let out = f.or(below, above);
    let out = f.or(out, backwards);
    when(f, out, |f| fail(f, "string index out of range"));
    let len = f.sub(to, from);
    let r = new_string(f, len);
    let src = char_addr(f, s, from);
    let dst = char_addr(f, r, zero);
    copy(f, src, dst, len);
    f.ret(r);
}

/// Reads up to a newline or the end of the input, into a buffer that doubles
/// when it fills up.
fn read_line(f: &mut Function) {
    let sixteen = k(f, 16);
    let zero = k(f, 0);
    let capacity = var(f, sixteen);
    let first = new_string(f, sixteen);
    let buffer = var(f, first);
    let count = var(f, zero);
    let done = var(f, zero);
    repeat(
        f,
        |f| {
            let d = get(f, done);
            f.lnot(d)
        },
        |f| {
            let c = f.get_char();
            let zero = k(f, 0);
            let end = f.lt(c, zero);
            let newline = k(f, b'\n' as i64);
            let line = f.eq(c, newline);
            let stop = f.or(end, line);
            when_else(
                f,
                stop,
                |f| {
                    let one = k(f, 1);
                    set(f, done, one);
                },
                |f| {
                    let n = get(f, count);
                    let cap = get(f, capacity);
                    let full = f.eq(n, cap);
                    when(f, full, |f| {
                        let two = k(f, 2);
                        let bigger = f.mul(cap, two);
                        let fresh = new_string(f, bigger);
                        let old = get(f, buffer);
                        let zero = k(f, 0);
                        let (from, to) = (char_addr(f, old, zero), char_addr(f, fresh, zero));
                        copy(f, from, to, n);
                        set(f, buffer, fresh);
                        set(f, capacity, bigger);
                    });
                    let b = get(f, buffer);
                    let p = char_addr(f, b, n);
                    f.store(p, c);
                    let one = k(f, 1);
                    let n = f.add(n, one);
                    set(f, count, n);
                },
            );
        },
    );
    let b = get(f, buffer);
    let n = get(f, count);
    f.store(b, n);
    f.ret(b);
}

/// `s.charAt` as a function: a closure of `s`.
fn char_at_closure(f: &mut Function) {
    let (env, i) = (f.param(0), f.param(1));
    let s = field(f, env, 1);
    let c = f.call("_s_char", &[s, i]);
    f.ret(c);
}

/// `s.substring` as a function, which takes `from` and gives a function
/// taking `to`.
fn substring_closure(f: &mut Function) {
    let (env, from) = (f.param(0), f.param(1));
    let s = field(f, env, 1);
    let three = k(f, 3);
    let r = f.gc_alloc(three);
    let code = f.func_addr("_s_sub2");
    f.store(r, code);
    set_field(f, r, 1, s);
    set_field(f, r, 2, from);
    f.ret(r);
}

fn substring_partial(f: &mut Function) {
    let (env, to) = (f.param(0), f.param(1));
    let s = field(f, env, 1);
    let from = field(f, env, 2);
    let r = f.call("_s_sub", &[s, from, to]);
    f.ret(r);
}
