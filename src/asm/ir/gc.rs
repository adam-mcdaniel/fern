//! The garbage collector behind `gc_alloc`, written in the IR and added to
//! a module when it's lowered.
//!
//! It's a conservative, non-moving mark-sweep collector. Every value a
//! function keeps is in a cell, between `roots_start` and the stack pointer
//! (fixed cells, then stack frames), so those cells are the roots. A root is
//! taken to point to an object if it points anywhere into one, so pointers
//! into the middle of an object keep it alive too; an integer that happens to
//! look like a pointer only keeps garbage around.
//!
//! The heap is made of chunks of `CHUNK` cells, below a table with one cell
//! per chunk saying what's in it. A small object, of up to `MAX_SMALL`
//! cells, goes in a chunk of objects its size, which starts with its size, a
//! link to the next chunk of that size, how many objects it holds and where
//! they start, then a state for each: 0 free, 1 allocated, 2 marked. A large
//! object gets a run of chunks to itself: the lowest chunk starts with how
//! many chunks there are, the object's state and its size.
//!
//! Allocating an object of a constant size calls a function made for that
//! size, which steps along the states of the current chunk of that size to
//! the next free one. The heap grows down, a chunk at a time, while that
//! leaves the stack room; when it can't, the collector marks everything
//! reachable from the roots (with a mark stack in the free cells above the
//! stack, rescanning the heap if that overflows), then frees what's
//! unmarked, gives chunks with nothing left in them to other sizes, and gives
//! free chunks at the bottom of the heap back to the stack. If there's still
//! no room, the program prints "out of memory" and stops.

use super::imperative::*;
use super::{Function, Intrinsic, Module, Value};

/// The chunk size, in cells.
const CHUNK: i64 = 64;
/// The largest size of object that shares a chunk with others.
pub(super) const MAX_SMALL: i64 = 20;
/// A small chunk's header: size, next, count, where the objects start, and
/// the size of an object in address units; then the states.
const HEADER: i64 = 5;
/// The most objects a small chunk holds is less than `2^SLOT_BITS`.
const SLOT_BITS: u32 = 5;
/// The most chunks there can be is less than `2^(MAX_POWER + 1)`.
const MAX_POWER: u32 = 20;

// The collector's global cells, from its first.
/// The address of the chunk table, just above chunk 0.
const END: u32 = 0;
const NCHUNKS: u32 = 1;
const MAX_CHUNKS: u32 = 2;
/// The size of a chunk, in address units.
const CHUNK_UNITS: u32 = 3;
/// How many cells to leave the stack when growing the heap.
const RESERVE: u32 = 4;
const OVERFLOW: u32 = 5;
const STACK_BASE: u32 = 6;
const STACK_LIMIT: u32 = 7;
const STACK_TOP: u32 = 8;
/// No chunk below this one is free.
const HINT: u32 = 9;
/// Arrays indexed by object size: the first chunk of that size with
/// anything in it after the last collection, and where to look for a free
/// slot next: a chunk, the state to look at, and the object it's the state
/// of.
const HEAD: u32 = 10;
const CURSOR: u32 = HEAD + MAX_SMALL as u32 + 1;
const STATE: u32 = CURSOR + MAX_SMALL as u32 + 1;
const OBJECT: u32 = STATE + MAX_SMALL as u32 + 1;
/// The chunk size times each power of two up to one at least as big as the
/// number of chunks there can be, and those powers, for finding the chunk a
/// pointer points into without dividing; and the addresses of the last of
/// each.
const POWERS: u32 = OBJECT + MAX_SMALL as u32 + 1;
const BITS: u32 = POWERS + MAX_POWER + 1;
const TOP_POWER: u32 = BITS + MAX_POWER + 1;
const TOP_BIT: u32 = TOP_POWER + 1;
const GLOBALS: u32 = TOP_BIT + 1;

/// The function that sets the collector up, which `main` calls first.
pub(super) const INIT: &str = "_gc_init";
/// The function that allocates objects of any size.
pub(super) const ALLOC: &str = "_gc_alloc";

/// The function that allocates objects of `size` cells, a constant.
pub(super) fn alloc_of(size: i64) -> Option<String> {
    (1..=MAX_SMALL).contains(&size).then(|| format!("_gc_s{size}"))
}

/// Adds the collector's functions to `module`: the ones it always needs, one
/// for each of `sizes`, and one for any size if `any`.
pub(super) fn add(module: &mut Module, sizes: &[i64], any: bool) {
    let g = module.add_globals(GLOBALS);
    let mut functions: Vec<(String, usize, Box<dyn Fn(&mut Function)>)> = vec![
        (INIT.to_string(), 0, Box::new(move |f| init(f, g))),
        ("_gc_chunks".to_string(), 1, Box::new(move |f| chunks(f, g))),
        ("_gc_large".to_string(), 1, Box::new(move |f| large(f, g))),
        ("_gc_push".to_string(), 2, Box::new(move |f| push(f, g))),
        ("_gc_mark".to_string(), 1, Box::new(move |f| mark(f, g))),
        ("_gc_scan".to_string(), 2, Box::new(scan)),
        ("_gc_drain".to_string(), 0, Box::new(move |f| drain(f, g))),
        ("_gc_collect".to_string(), 0, Box::new(move |f| collect(f, g))),
    ];
    for &size in sizes {
        let name = alloc_of(size).unwrap();
        functions.push((name, 0, Box::new(move |f| {
            let s = f.int(size);
            small(f, g, s);
        })));
    }
    if any {
        functions.push(("_gc_small".to_string(), 1, Box::new(move |f| {
            let s = f.param(0);
            small(f, g, s);
        })));
        functions.push((ALLOC.to_string(), 1, Box::new(alloc)));
    }
    for (name, params, body) in functions {
        body(module.function(&name, params));
    }
}

/// The address of the collector's global `i`, or element `at` of the array
/// that starts there.
fn global(f: &mut Function, g: u32, i: u32) -> Value {
    f.global_addr(g + i)
}

fn global_at(f: &mut Function, g: u32, i: u32, at: Value) -> Value {
    match f.const_value(at) {
        Some(k) => f.global_addr(g + i + k as u32),
        None => {
            let base = f.global_addr(g + i);
            f.index(base, at)
        }
    }
}

fn load_global(f: &mut Function, g: u32, i: u32) -> Value {
    let a = global(f, g, i);
    f.load(a)
}

fn store_global(f: &mut Function, g: u32, i: u32, x: Value) {
    let a = global(f, g, i);
    f.store(a, x);
}

/// Whether either of two booleans is true, as a branch condition: cheaper
/// than a bitwise or.
fn either(f: &mut Function, a: Value, b: Value) -> Value {
    f.add(a, b)
}

/// The address of the table cell for chunk `i`.
fn table(f: &mut Function, g: u32, i: Value) -> Value {
    let end = load_global(f, g, END);
    f.index(end, i)
}

/// The address where chunk `i` starts.
fn chunk(f: &mut Function, g: u32, i: Value) -> Value {
    let end = load_global(f, g, END);
    let one = k(f, 1);
    let n = f.add(i, one);
    let size = k(f, -CHUNK);
    let cells = f.mul(n, size);
    f.index(end, cells)
}

fn out_of_memory(f: &mut Function) {
    f.puts("out of memory\n");
    f.abort();
    let zero = k(f, 0);
    f.ret(zero);
}

/// Sets up the heap: the chunk table goes at the top, and chunks below it.
fn init(f: &mut Function, g: u32) {
    let end = f.intrinsic(Intrinsic::HeapPointer, &[]);
    let roots = f.intrinsic(Intrinsic::RootsStart, &[]);
    let one = k(f, 1);
    let next = f.index(end, one);
    let cell = f.sub(next, end);
    let span = f.sub(end, roots);
    let total = f.div(span, cell);
    let per_chunk = k(f, CHUNK + 1);
    let max = f.div(total, per_chunk);
    let below = f.neg(max);
    let table = f.index(end, below);
    f.intrinsic(Intrinsic::SetHeapPointer, &[table]);
    store_global(f, g, END, table);
    store_global(f, g, MAX_CHUNKS, max);
    let size = k(f, CHUNK);
    let past = f.index(table, size);
    let units = f.sub(past, table);
    store_global(f, g, CHUNK_UNITS, units);
    let eight = k(f, 8);
    let reserve = f.div(total, eight);
    let extra = k(f, 64);
    let reserve = f.add(reserve, extra);
    store_global(f, g, RESERVE, reserve);
    // the chunk size times 1, 2, 4, ... while the power is at most the
    // number of chunks there can be
    store_global(f, g, POWERS, units);
    let one = k(f, 1);
    store_global(f, g, BITS, one);
    let power = var(f, units);
    let bit = var(f, one);
    let zero = k(f, 0);
    let at = var(f, zero);
    let limit = k(f, MAX_POWER as i64);
    repeat(
        f,
        |f| {
            let b = get(f, bit);
            let twice = f.add(b, b);
            let fits = f.le(twice, max);
            let a = get(f, at);
            let room = f.lt(a, limit);
            f.and(fits, room)
        },
        |f| {
            let a = get(f, at);
            let one = k(f, 1);
            let a = f.add(a, one);
            set(f, at, a);
            let p = get(f, power);
            let p = f.add(p, p);
            set(f, power, p);
            let b = get(f, bit);
            let b = f.add(b, b);
            set(f, bit, b);
            let cell = global_at(f, g, POWERS, a);
            f.store(cell, p);
            let cell = global_at(f, g, BITS, a);
            f.store(cell, b);
        },
    );
    let a = get(f, at);
    let top = global_at(f, g, POWERS, a);
    store_global(f, g, TOP_POWER, top);
    let top = global_at(f, g, BITS, a);
    store_global(f, g, TOP_BIT, top);
    f.ret_void();
}

/// Finds `k` free chunks in a row, growing the heap if it has to and can,
/// and returns the number of the lowest (the one with the highest number),
/// or -1.
fn chunks(f: &mut Function, g: u32) {
    let want = f.param(0);
    let n = load_global(f, g, NCHUNKS);
    let zero = k(f, 0);
    let run = var(f, zero);
    let hint = load_global(f, g, HINT);
    each(f, hint, n, |f, i| {
        let t = table(f, g, i);
        let kind = f.load(t);
        let zero = k(f, 0);
        let free = f.eq(kind, zero);
        when_else(
            f,
            free,
            |f| {
                let r = get(f, run);
                let one = k(f, 1);
                let r = f.add(r, one);
                set(f, run, r);
            },
            |f| {
                let zero = k(f, 0);
                set(f, run, zero);
            },
        );
        let r = get(f, run);
        let enough = f.eq(r, want);
        when(f, enough, |f| {
            // taking one chunk leaves none free up to it
            let one = k(f, 1);
            let single = f.eq(want, one);
            when(f, single, |f| {
                let one = k(f, 1);
                let past = f.add(i, one);
                store_global(f, g, HINT, past);
            });
            f.ret(i);
        });
    });
    // a run of free chunks at the bottom only needs the rest added
    let r = get(f, run);
    let more = f.sub(want, r);
    let total = f.add(n, more);
    let max = load_global(f, g, MAX_CHUNKS);
    let too_many = f.gt(total, max);
    let none = k(f, -1);
    when(f, too_many, |f| f.ret(none));
    let one = k(f, 1);
    let last = f.sub(total, one);
    let bottom = chunk(f, g, last);
    let sp = f.intrinsic(Intrinsic::StackPointer, &[]);
    let reserve = load_global(f, g, RESERVE);
    let limit = f.index(sp, reserve);
    let crowded = f.lt(bottom, limit);
    when(f, crowded, |f| f.ret(none));
    each(f, n, total, |f, i| {
        let t = table(f, g, i);
        let zero = k(f, 0);
        f.store(t, zero);
    });
    f.intrinsic(Intrinsic::SetHeapPointer, &[bottom]);
    store_global(f, g, NCHUNKS, total);
    // a single chunk only comes from growing when none were free
    let one = k(f, 1);
    let single = f.eq(want, one);
    when(f, single, |f| store_global(f, g, HINT, total));
    f.ret(last);
}

/// Points the cursor for size `s` at the start of chunk `c`.
fn start_cursor(f: &mut Function, g: u32, s: Value, c: Value) {
    let cursor = global_at(f, g, CURSOR, s);
    f.store(cursor, c);
    let header = k(f, HEADER);
    let first_state = f.index(c, header);
    let state = global_at(f, g, STATE, s);
    f.store(state, first_state);
    let area = field(f, c, 3);
    let object = global_at(f, g, OBJECT, s);
    f.store(object, area);
}

/// A small object of `s` cells: the next free slot in a chunk of that size,
/// or one in a new chunk, after collecting if need be.
fn small(f: &mut Function, g: u32, s: Value) {
    let zero = k(f, 0);
    let collected = var(f, zero);
    let one = k(f, 1);
    repeat(
        f,
        |_| one,
        |f| {
            let cursor = global_at(f, g, CURSOR, s);
            let state_at = global_at(f, g, STATE, s);
            let object_at = global_at(f, g, OBJECT, s);
            let first = f.load(cursor);
            let c = var(f, first);
            repeat(
                f,
                |f| {
                    let cv = get(f, c);
                    let zero = k(f, 0);
                    f.ne(cv, zero)
                },
                |f| {
                    let cv = get(f, c);
                    // the states end where the objects start
                    let area = field(f, cv, 3);
                    let start = f.load(state_at);
                    let state = var(f, start);
                    let start = f.load(object_at);
                    let object = var(f, start);
                    repeat(
                        f,
                        |f| {
                            let st = get(f, state);
                            f.ne(st, area)
                        },
                        |f| {
                            let st = get(f, state);
                            let o = get(f, object);
                            let value = f.load(st);
                            let zero = k(f, 0);
                            let free = f.eq(value, zero);
                            let one = k(f, 1);
                            let next_state = f.index(st, one);
                            let next_object = f.index(o, s);
                            when(f, free, |f| {
                                let one = k(f, 1);
                                f.store(st, one);
                                f.store(state_at, next_state);
                                f.store(object_at, next_object);
                                clear(f, o, s);
                                f.ret(o);
                            });
                            set(f, state, next_state);
                            set(f, object, next_object);
                        },
                    );
                    // on to the next chunk of this size
                    let next = field(f, cv, 1);
                    set(f, c, next);
                    f.store(cursor, next);
                    let zero = k(f, 0);
                    let more = f.ne(next, zero);
                    when(f, more, |f| start_cursor(f, g, s, next));
                },
            );
            // no free slot: a new chunk, or collect, or give up
            let one = k(f, 1);
            let i = f.call("_gc_chunks", &[one]);
            let zero = k(f, 0);
            let found = f.ge(i, zero);
            when_else(
                f,
                found,
                |f| {
                    let c = chunk(f, g, i);
                    let t = table(f, g, i);
                    f.store(t, s);
                    let one = k(f, 1);
                    let stride = f.add(s, one);
                    let room = k(f, CHUNK - HEADER);
                    let count = f.div(room, stride);
                    set_field(f, c, 0, s);
                    // the cursor has been through every other chunk of
                    // this size, so the new one ends the chain; collecting
                    // relinks them all from the table
                    let zero = k(f, 0);
                    set_field(f, c, 1, zero);
                    set_field(f, c, 2, count);
                    let header = k(f, HEADER);
                    let states = f.index(c, header);
                    let area = f.index(states, count);
                    set_field(f, c, 3, area);
                    let past = f.index(area, s);
                    let units = f.sub(past, area);
                    set_field(f, c, 4, units);
                    clear(f, states, count);
                    start_cursor(f, g, s, c);
                },
                |f| {
                    let done = get(f, collected);
                    let zero = k(f, 0);
                    let first_time = f.eq(done, zero);
                    when_else(
                        f,
                        first_time,
                        |f| {
                            f.call("_gc_collect", &[]);
                            let one = k(f, 1);
                            set(f, collected, one);
                        },
                        out_of_memory,
                    );
                },
            );
        },
    );
    let zero = k(f, 0);
    f.ret(zero);
}

/// A large object of `n` cells, in chunks of its own.
fn large(f: &mut Function, g: u32) {
    let n = f.param(0);
    let extra = k(f, 3 + CHUNK - 1);
    let cells = f.add(n, extra);
    let size = k(f, CHUNK);
    let count = f.div(cells, size);
    let zero = k(f, 0);
    let collected = var(f, zero);
    let one = k(f, 1);
    repeat(
        f,
        |_| one,
        |f| {
            let i = f.call("_gc_chunks", &[count]);
            let zero = k(f, 0);
            let found = f.ge(i, zero);
            when(f, found, |f| {
                let t = table(f, g, i);
                let head = k(f, -1);
                f.store(t, head);
                let one = k(f, 1);
                // the chunks above the lowest say how far down it is
                each(f, one, count, |f, j| {
                    let at = f.sub(i, j);
                    let t = table(f, g, at);
                    let one = k(f, 1);
                    let d = f.add(j, one);
                    let code = f.neg(d);
                    f.store(t, code);
                });
                let c = chunk(f, g, i);
                set_field(f, c, 0, count);
                let one = k(f, 1);
                set_field(f, c, 1, one);
                set_field(f, c, 2, n);
                let three = k(f, 3);
                let object = f.index(c, three);
                clear(f, object, n);
                f.ret(object);
            });
            let done = get(f, collected);
            let zero = k(f, 0);
            let first_time = f.eq(done, zero);
            when_else(
                f,
                first_time,
                |f| {
                    f.call("_gc_collect", &[]);
                    let one = k(f, 1);
                    set(f, collected, one);
                },
                out_of_memory,
            );
        },
    );
    let zero = k(f, 0);
    f.ret(zero);
}

/// An object of any size.
fn alloc(f: &mut Function) {
    let n = f.param(0);
    let one = k(f, 1);
    let n = f.max(n, one);
    let limit = k(f, MAX_SMALL);
    let fits = f.le(n, limit);
    when_else(
        f,
        fits,
        |f| {
            let p = f.call("_gc_small", &[n]);
            f.ret(p);
        },
        |f| {
            let p = f.call("_gc_large", &[n]);
            f.ret(p);
        },
    );
    let zero = k(f, 0);
    f.ret(zero);
}

/// Pushes the `n` cells at `p` onto the mark stack, to scan, or notes that
/// the stack overflowed.
fn push(f: &mut Function, g: u32) {
    let (p, n) = (f.param(0), f.param(1));
    let top = load_global(f, g, STACK_TOP);
    let two = k(f, 2);
    let next = f.index(top, two);
    let limit = load_global(f, g, STACK_LIMIT);
    let full = f.gt(next, limit);
    when_else(
        f,
        full,
        |f| {
            let one = k(f, 1);
            store_global(f, g, OVERFLOW, one);
        },
        |f| {
            f.store(top, p);
            set_field(f, top, 1, n);
            store_global(f, g, STACK_TOP, next);
        },
    );
    f.ret_void();
}

/// Marks the object `w` points into, if it does, and pushes its cells to be
/// scanned. Finding the chunk and the object takes no division or
/// multiplication (both slow routines): only subtractions and tests of sign,
/// over the multiples of the chunk and object sizes by powers of two.
fn mark(f: &mut Function, g: u32) {
    let w = f.param(0);
    let end = load_global(f, g, END);
    let n = load_global(f, g, NCHUNKS);
    let size = k(f, -CHUNK);
    let cells = f.mul(n, size);
    let low = f.index(end, cells);
    // w - low is where it is from the bottom of the heap; differences wrap
    // around, which keeps this right for any w
    let d = f.sub(w, low);
    let zero = k(f, 0);
    let below = f.lt(d, zero);
    let span = f.sub(end, low);
    let past = f.sub(d, span);
    let above = f.ge(past, zero);
    let outside = either(f, below, above);
    when(f, outside, |f| f.ret_void());
    // j = d / chunk size, counting chunks from the bottom
    let rest = var(f, d);
    let j = var(f, zero);
    let first_power = load_global(f, g, TOP_POWER);
    let power = var(f, first_power);
    let first_bit = load_global(f, g, TOP_BIT);
    let bit = var(f, first_bit);
    let stop = f.global_addr(g + POWERS - 1);
    repeat(
        f,
        |f| {
            let p = get(f, power);
            f.ne(p, stop)
        },
        |f| {
            let p = get(f, power);
            let b = get(f, bit);
            let r = get(f, rest);
            let u = f.load(p);
            let left = f.sub(r, u);
            let zero = k(f, 0);
            let fits = f.ge(left, zero);
            let x = get(f, j);
            let v = f.load(b);
            let more = f.add(x, v);
            let r = choose(f, fits, left, r);
            set(f, rest, r);
            let x = choose(f, fits, more, x);
            set(f, j, x);
            let minus_one = k(f, -1);
            let p = f.index(p, minus_one);
            set(f, power, p);
            let b = f.index(b, minus_one);
            set(f, bit, b);
        },
    );
    let jv = get(f, j);
    let one = k(f, 1);
    let top = f.sub(n, one);
    let i = f.sub(top, jv);
    let offset = get(f, rest);
    let c = f.sub(w, offset);
    let t = table(f, g, i);
    let kind = f.load(t);
    let free = f.eq(kind, zero);
    when(f, free, |f| f.ret_void());
    let positive = f.gt(kind, zero);
    when(f, positive, |f| {
        // a small object: slot = (w - area) / object size, the same way
        let count = field(f, c, 2);
        let area = field(f, c, 3);
        let units = field(f, c, 4);
        let off = f.sub(w, area);
        let zero = k(f, 0);
        let before = f.lt(off, zero);
        when(f, before, |f| f.ret_void());
        let mut multiples = vec![units];
        for _ in 1..SLOT_BITS {
            let last = *multiples.last().unwrap();
            multiples.push(f.add(last, last));
        }
        let (mut rest, mut slot) = (off, zero);
        for (bit, &u) in multiples.iter().enumerate().rev() {
            let left = f.sub(rest, u);
            let zero = k(f, 0);
            let fits = f.ge(left, zero);
            let b = k(f, 1 << bit);
            let more = f.add(slot, b);
            rest = choose(f, fits, left, rest);
            slot = choose(f, fits, more, slot);
        }
        let sv = slot;
        let beyond = f.sub(sv, count);
        let zero = k(f, 0);
        let beyond = f.ge(beyond, zero);
        when(f, beyond, |f| f.ret_void());
        let header = k(f, HEADER);
        let at = f.add(sv, header);
        let state = f.index(c, at);
        let st = f.load(state);
        let one = k(f, 1);
        let allocated = f.eq(st, one);
        when(f, allocated, |f| {
            let two = k(f, 2);
            f.store(state, two);
            let object = f.sub(w, rest);
            f.call("_gc_push", &[object, kind]);
        });
        f.ret_void();
    });
    // a large object: chunks above its lowest say how far down that is
    let minus_one = k(f, -1);
    let above_head = f.lt(kind, minus_one);
    let head = var(f, c);
    when(f, above_head, |f| {
        let d = f.neg(kind);
        let one = k(f, 1);
        let d = f.sub(d, one);
        let size = k(f, -CHUNK);
        let cells = f.mul(d, size);
        let h = f.index(c, cells);
        set(f, head, h);
    });
    let h = get(f, head);
    let three = k(f, 3);
    let object = f.index(h, three);
    let size = field(f, h, 2);
    let into = f.sub(w, object);
    let zero = k(f, 0);
    let before = f.lt(into, zero);
    let past = f.index(object, size);
    let beyond = f.sub(w, past);
    let after = f.ge(beyond, zero);
    let missed = either(f, before, after);
    when(f, missed, |f| f.ret_void());
    let st = field(f, h, 1);
    let one = k(f, 1);
    let allocated = f.eq(st, one);
    when(f, allocated, |f| {
        let two = k(f, 2);
        set_field(f, h, 1, two);
        f.call("_gc_push", &[object, size]);
    });
    f.ret_void();
}

/// Marks what each cell from `p` up to `end` points to.
fn scan(f: &mut Function) {
    let (p, end) = (f.param(0), f.param(1));
    let at = var(f, p);
    repeat(
        f,
        |f| {
            let a = get(f, at);
            f.ne(a, end)
        },
        |f| {
            let a = get(f, at);
            let w = f.load(a);
            f.call("_gc_mark", &[w]);
            let one = k(f, 1);
            let next = f.index(a, one);
            set(f, at, next);
        },
    );
    f.ret_void();
}

/// Scans everything on the mark stack, until it's empty.
fn drain(f: &mut Function, g: u32) {
    repeat(
        f,
        |f| {
            let top = load_global(f, g, STACK_TOP);
            let base = load_global(f, g, STACK_BASE);
            f.ne(top, base)
        },
        |f| {
            let top = load_global(f, g, STACK_TOP);
            let minus_two = k(f, -2);
            let top = f.index(top, minus_two);
            store_global(f, g, STACK_TOP, top);
            let p = f.load(top);
            let n = field(f, top, 1);
            let end = f.index(p, n);
            f.call("_gc_scan", &[p, end]);
        },
    );
    f.ret_void();
}

/// Marks everything reachable, and frees the rest.
fn collect(f: &mut Function, g: u32) {
    // the mark stack goes in the free cells between the stack and the heap
    let sp = f.intrinsic(Intrinsic::StackPointer, &[]);
    let eight = k(f, 8);
    let base = f.index(sp, eight);
    store_global(f, g, STACK_BASE, base);
    store_global(f, g, STACK_TOP, base);
    let hp = f.intrinsic(Intrinsic::HeapPointer, &[]);
    let minus_two = k(f, -2);
    let limit = f.index(hp, minus_two);
    store_global(f, g, STACK_LIMIT, limit);
    let zero = k(f, 0);
    store_global(f, g, OVERFLOW, zero);
    let roots = f.intrinsic(Intrinsic::RootsStart, &[]);
    f.call("_gc_scan", &[roots, sp]);
    f.call("_gc_drain", &[]);
    // if the mark stack overflowed, some marked objects weren't scanned:
    // scan every marked object again until it doesn't
    repeat(
        f,
        |f| load_global(f, g, OVERFLOW),
        |f| {
            let zero = k(f, 0);
            store_global(f, g, OVERFLOW, zero);
            let n = load_global(f, g, NCHUNKS);
            each(f, zero, n, |f, i| {
                let t = table(f, g, i);
                let kind = f.load(t);
                let c = chunk(f, g, i);
                let zero = k(f, 0);
                let is_small = f.gt(kind, zero);
                when_else(
                    f,
                    is_small,
                    |f| {
                        let count = field(f, c, 2);
                        let area = field(f, c, 3);
                        let zero = k(f, 0);
                        each(f, zero, count, |f, slot| {
                            let header = k(f, HEADER);
                            let at = f.add(slot, header);
                            let state = f.index(c, at);
                            let st = f.load(state);
                            let two = k(f, 2);
                            let marked = f.eq(st, two);
                            when(f, marked, |f| {
                                let cells = f.mul(slot, kind);
                                let object = f.index(area, cells);
                                let end = f.index(object, kind);
                                f.call("_gc_scan", &[object, end]);
                            });
                        });
                    },
                    |f| {
                        let minus_one = k(f, -1);
                        let is_large = f.eq(kind, minus_one);
                        when(f, is_large, |f| {
                            let st = field(f, c, 1);
                            let two = k(f, 2);
                            let marked = f.eq(st, two);
                            when(f, marked, |f| {
                                let three = k(f, 3);
                                let object = f.index(c, three);
                                let size = field(f, c, 2);
                                let end = f.index(object, size);
                                f.call("_gc_scan", &[object, end]);
                            });
                        });
                    },
                );
            });
            f.call("_gc_drain", &[]);
        },
    );

    // sweep, relinking the chunks of each size that still hold something
    let zero = k(f, 0);
    store_global(f, g, HINT, zero);
    let one = k(f, 1);
    let sizes = k(f, MAX_SMALL + 1);
    each(f, one, sizes, |f, s| {
        let head = global_at(f, g, HEAD, s);
        let zero = k(f, 0);
        f.store(head, zero);
    });
    let n = load_global(f, g, NCHUNKS);
    let zero = k(f, 0);
    each(f, zero, n, |f, i| {
        let t = table(f, g, i);
        let kind = f.load(t);
        let c = chunk(f, g, i);
        let zero = k(f, 0);
        let is_small = f.gt(kind, zero);
        when_else(
            f,
            is_small,
            |f| {
                let count = field(f, c, 2);
                let zero = k(f, 0);
                let live = var(f, zero);
                each(f, zero, count, |f, slot| {
                    let header = k(f, HEADER);
                    let at = f.add(slot, header);
                    let state = f.index(c, at);
                    let st = f.load(state);
                    let two = k(f, 2);
                    let marked = f.eq(st, two);
                    when_else(
                        f,
                        marked,
                        |f| {
                            let one = k(f, 1);
                            f.store(state, one);
                            set(f, live, one);
                        },
                        |f| {
                            let zero = k(f, 0);
                            f.store(state, zero);
                        },
                    );
                });
                let l = get(f, live);
                when_else(
                    f,
                    l,
                    |f| {
                        let head = global_at(f, g, HEAD, kind);
                        let old = f.load(head);
                        set_field(f, c, 1, old);
                        f.store(head, c);
                    },
                    |f| {
                        let zero = k(f, 0);
                        f.store(t, zero);
                    },
                );
            },
            |f| {
                let minus_one = k(f, -1);
                let is_large = f.eq(kind, minus_one);
                when(f, is_large, |f| {
                    let st = field(f, c, 1);
                    let two = k(f, 2);
                    let marked = f.eq(st, two);
                    when_else(
                        f,
                        marked,
                        |f| {
                            let one = k(f, 1);
                            set_field(f, c, 1, one);
                        },
                        |f| {
                            let count = field(f, c, 0);
                            let zero = k(f, 0);
                            each(f, zero, count, |f, j| {
                                let at = f.sub(i, j);
                                let t = table(f, g, at);
                                let zero = k(f, 0);
                                f.store(t, zero);
                            });
                        },
                    );
                });
            },
        );
    });
    // allocation starts again from the first chunk of each size
    let one = k(f, 1);
    each(f, one, sizes, |f, s| {
        let head = global_at(f, g, HEAD, s);
        let c = f.load(head);
        let cursor = global_at(f, g, CURSOR, s);
        f.store(cursor, c);
        let zero = k(f, 0);
        let some = f.ne(c, zero);
        when(f, some, |f| start_cursor(f, g, s, c));
    });
    // free chunks at the bottom go back to the stack
    let n = load_global(f, g, NCHUNKS);
    let count = var(f, n);
    repeat(
        f,
        |f| {
            let c = get(f, count);
            let zero = k(f, 0);
            let any = f.ne(c, zero);
            // (a branch, so the table isn't read when there are no chunks)
            let (check, done, after) = (f.new_block(0), f.new_block(0), f.new_block(1));
            f.branch(any, check, &[], done, &[]);
            f.switch_to(check);
            let one = k(f, 1);
            let last = f.sub(c, one);
            let t = table(f, g, last);
            let kind = f.load(t);
            let free = f.eq(kind, zero);
            f.jump(after, &[free]);
            f.switch_to(done);
            f.jump(after, &[zero]);
            f.switch_to(after);
            f.block_param(after, 0)
        },
        |f| {
            let c = get(f, count);
            let one = k(f, 1);
            let fewer = f.sub(c, one);
            set(f, count, fewer);
        },
    );
    let n = get(f, count);
    store_global(f, g, NCHUNKS, n);
    let end = load_global(f, g, END);
    let size = k(f, -CHUNK);
    let cells = f.mul(n, size);
    let bottom = f.index(end, cells);
    f.intrinsic(Intrinsic::SetHeapPointer, &[bottom]);
    f.ret_void();
}
