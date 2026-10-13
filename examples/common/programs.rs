//! The IR programs the examples measure.

use bf::asm::ir::{Function, Module, Value};

/// `for i in 0..n { body(i) }`, leaving the builder after the loop.
pub fn counted_loop(f: &mut Function, n: Value, body: impl FnOnce(&mut Function, Value)) {
    let head = f.new_block(1);
    let (inside, after) = (f.new_block(0), f.new_block(0));
    let zero = f.int(0);
    f.jump(head, &[zero]);
    f.switch_to(head);
    let i = f.block_param(head, 0);
    let more = f.lt(i, n);
    f.branch(more, inside, &[], after, &[]);
    f.switch_to(inside);
    body(f, i);
    let one = f.int(1);
    let next = f.add(i, one);
    f.jump(head, &[next]);
    f.switch_to(after);
}

pub fn fib() -> Module {
    fib_upto(14)
}

/// Prints fib(i) for i from 0 up to `count`.
pub fn fib_upto(count: i64) -> Module {
    let mut m = Module::new();
    let f = m.function("fib", 1);
    let n = f.param(0);
    let (base, recurse) = (f.new_block(0), f.new_block(0));
    let two = f.int(2);
    let small = f.lt(n, two);
    f.branch(small, base, &[], recurse, &[]);
    f.switch_to(base);
    f.ret(n);
    f.switch_to(recurse);
    let one = f.int(1);
    let a = f.sub(n, one);
    let fa = f.call("fib", &[a]);
    let b = f.sub(n, two);
    let fb = f.call("fib", &[b]);
    let sum = f.add(fa, fb);
    f.ret(sum);
    let f = m.main();
    let n = f.int(count);
    counted_loop(f, n, |f, i| {
        let r = f.call("fib", &[i]);
        f.put_int(r);
        f.puts(" ");
    });
    f.ret_void();
    m
}

pub fn sieve() -> Module {
    let mut m = Module::new();
    let f = m.main();
    let n = f.int(300);
    let one = f.int(1);
    let size = f.add(n, one);
    let flags = f.heap_alloc(size);
    counted_loop(f, size, |f, i| {
        let at = f.index(flags, i);
        let zero = f.int(0);
        f.store(at, zero);
    });
    // cross out multiples of i for i in 2..n
    let head = f.new_block(2);
    let (check, mark, next, done) = (f.new_block(0), f.new_block(0), f.new_block(1), f.new_block(0));
    let two = f.int(2);
    let zero = f.int(0);
    f.jump(head, &[two, zero]);
    f.switch_to(head);
    let (i, count) = (f.block_param(head, 0), f.block_param(head, 1));
    let more = f.le(i, n);
    f.branch(more, check, &[], done, &[]);
    f.switch_to(check);
    let at = f.index(flags, i);
    let crossed = f.load(at);
    f.branch(crossed, next, &[count], mark, &[]);
    f.switch_to(mark);
    let inner = f.new_block(1);
    let (body, after) = (f.new_block(0), f.new_block(0));
    let double = f.add(i, i);
    f.jump(inner, &[double]);
    f.switch_to(inner);
    let j = f.block_param(inner, 0);
    let in_range = f.le(j, n);
    f.branch(in_range, body, &[], after, &[]);
    f.switch_to(body);
    let at = f.index(flags, j);
    f.store(at, one);
    let j2 = f.add(j, i);
    f.jump(inner, &[j2]);
    f.switch_to(after);
    let count2 = f.add(count, one);
    f.jump(next, &[count2]);
    f.switch_to(next);
    let c = f.block_param(next, 0);
    let i2 = f.add(i, one);
    f.jump(head, &[i2, c]);
    f.switch_to(done);
    f.put_int(count);
    f.ret_void();
    m
}

pub fn demo() -> Module {
    let mut m = Module::new();
    {
        let f = m.function("gcd", 2);
        let head = f.new_block(2);
        let (step, done) = (f.new_block(0), f.new_block(0));
        let (a, b) = (f.param(0), f.param(1));
        f.jump(head, &[a, b]);
        f.switch_to(head);
        let (a, b) = (f.block_param(head, 0), f.block_param(head, 1));
        let zero = f.int(0);
        let more = f.ne(b, zero);
        f.branch(more, step, &[], done, &[]);
        f.switch_to(step);
        let r = f.rem(a, b);
        f.jump(head, &[b, r]);
        f.switch_to(done);
        f.ret(a);
    }
    {
        let f = m.function("collatz", 1);
        let head = f.new_block(2);
        let (step, even, odd, done) = (f.new_block(0), f.new_block(0), f.new_block(0), f.new_block(0));
        let n = f.param(0);
        let zero = f.int(0);
        f.jump(head, &[n, zero]);
        f.switch_to(head);
        let (n, steps) = (f.block_param(head, 0), f.block_param(head, 1));
        let one = f.int(1);
        let more = f.gt(n, one);
        f.branch(more, step, &[], done, &[]);
        f.switch_to(step);
        let next = f.add(steps, one);
        let bit = f.and(n, one);
        f.branch(bit, odd, &[], even, &[]);
        f.switch_to(even);
        let two = f.int(2);
        let half = f.div(n, two);
        f.jump(head, &[half, next]);
        f.switch_to(odd);
        let three = f.int(3);
        let triple = f.mul(n, three);
        let up = f.add(triple, one);
        f.jump(head, &[up, next]);
        f.switch_to(done);
        f.ret(steps);
    }
    {
        let f = m.function("fact", 1);
        let (base, recurse) = (f.new_block(0), f.new_block(0));
        let n = f.param(0);
        let one = f.int(1);
        let small = f.le(n, one);
        f.branch(small, base, &[], recurse, &[]);
        f.switch_to(base);
        f.ret(one);
        f.switch_to(recurse);
        let less = f.sub(n, one);
        let r = f.call("fact", &[less]);
        let product = f.mul(n, r);
        f.ret(product);
    }
    let f = m.main();
    let head = f.new_block(0);
    let (body, done) = (f.new_block(0), f.new_block(0));
    f.jump(head, &[]);
    f.switch_to(head);
    let n = f.get_int();
    let zero = f.int(0);
    let more = f.ne(n, zero);
    f.branch(more, body, &[], done, &[]);
    f.switch_to(body);
    let steps = f.call("collatz", &[n]);
    f.put_int(steps);
    f.puts(" ");
    let k = f.int(360);
    let g = f.call("gcd", &[n, k]);
    f.put_int(g);
    f.puts(" ");
    let eight = f.int(8);
    let small = f.rem(n, eight);
    let r = f.call("fact", &[small]);
    f.put_int(r);
    f.puts("\n");
    f.jump(head, &[]);
    f.switch_to(done);
    f.ret_void();
    m
}

/// A loop with work that doesn't change between iterations, repeated loads,
/// a small helper function, and comparisons and division on small values.
pub fn kernel() -> Module {
    let mut m = Module::new();
    let f = m.function("mix", 3);
    let (a, b, c) = (f.param(0), f.param(1), f.param(2));
    let ab = f.add(a, b);
    let r = f.sub(ab, c);
    f.ret(r);

    let f = m.main();
    let (a, b, c) = (f.get_int(), f.get_int(), f.get_int());
    let table = f.alloca(8);
    let head = f.new_block(2);
    let (body, done) = (f.new_block(0), f.new_block(0));
    let zero = f.int(0);
    f.jump(head, &[zero, zero]);
    f.switch_to(head);
    let (i, sum) = (f.block_param(head, 0), f.block_param(head, 1));
    let limit = f.int(200);
    let more = f.lt(i, limit);
    f.branch(more, body, &[], done, &[]);
    f.switch_to(body);
    // invariant: a * b + c
    let ab = f.mul(a, b);
    let k = f.add(ab, c);
    let seven = f.int(7);
    let slot = f.and(i, seven);
    let at = f.index(table, slot);
    f.store(at, i);
    let x = f.load(at);
    let y = f.load(at);
    let xy = f.add(x, y);
    let four = f.int(4);
    let quarter = f.div(i, four);
    let mixed = f.call("mix", &[xy, quarter, k]);
    let sum2 = f.add(sum, mixed);
    let one = f.int(1);
    let next = f.add(i, one);
    f.jump(head, &[next, sum2]);
    f.switch_to(done);
    f.put_int(sum);
    f.ret_void();
    m
}

/// gcd by tail recursion.
pub fn tail() -> Module {
    let mut m = Module::new();
    let f = m.function("gcd", 2);
    let (a, b) = (f.param(0), f.param(1));
    let (done, recurse) = (f.new_block(0), f.new_block(0));
    let zero = f.int(0);
    let finished = f.eq(b, zero);
    f.branch(finished, done, &[], recurse, &[]);
    f.switch_to(done);
    f.ret(a);
    f.switch_to(recurse);
    let r = f.rem(a, b);
    let g = f.call("gcd", &[b, r]);
    f.ret(g);
    let f = m.main();
    let n = f.int(60);
    counted_loop(f, n, |f, i| {
        let k = f.int(1000);
        let x = f.add(i, k);
        let y = f.int(360);
        let g = f.call("gcd", &[x, y]);
        f.put_int(g);
        f.puts(" ");
    });
    f.ret_void();
    m
}

/// Loops over an array with an index that's a multiple of the counter, a load
/// that doesn't change inside the loop, a short loop with a constant count,
/// and a function called with different constants.
pub fn loops() -> Module {
    let mut m = Module::new();
    let f = m.function("poly", 2);
    let (x, k) = (f.param(0), f.param(1));
    let xx = f.mul(x, x);
    let kx = f.mul(k, x);
    let sum = f.add(xx, kx);
    let one = f.int(1);
    let r = f.add(sum, one);
    let ten = f.int(10);
    let (big, small) = (f.new_block(0), f.new_block(0));
    let over = f.gt(r, ten);
    f.branch(over, big, &[], small, &[]);
    f.switch_to(big);
    let r2 = f.sub(r, ten);
    f.ret(r2);
    f.switch_to(small);
    f.ret(r);

    let f = m.main();
    let scale = f.alloca(1);
    let s = f.get_int();
    f.store(scale, s);
    let table = f.alloca(64);
    let n = f.int(20);
    counted_loop(f, n, |f, i| {
        let three = f.int(3);
        let at = f.mul(i, three);
        let slot = f.index(table, at);
        let factor = f.load(scale);
        let v = f.mul(i, factor);
        f.store(slot, v);
    });
    let total = f.alloca(1);
    let zero = f.int(0);
    f.store(total, zero);
    counted_loop(f, n, |f, i| {
        let three = f.int(3);
        let at = f.mul(i, three);
        let slot = f.index(table, at);
        let v = f.load(slot);
        let four = f.int(4);
        counted_loop(f, four, |f, j| {
            let t = f.load(total);
            let w = f.add(v, j);
            let t2 = f.add(t, w);
            f.store(total, t2);
        });
    });
    let t = f.load(total);
    f.put_int(t);
    f.puts(" ");
    let (two, seven) = (f.int(2), f.int(7));
    counted_loop(f, n, |f, i| {
        let a = f.call("poly", &[i, two]);
        let b = f.call("poly", &[i, seven]);
        let c = f.add(a, b);
        f.put_int(c);
        f.puts(",");
    });
    f.ret_void();
    m
}


/// Every program, with the input it reads.
pub fn all() -> Vec<(&'static str, Module, &'static [u8])> {
    vec![
        ("fib", fib(), b""),
        ("sieve", sieve(), b""),
        ("demo", demo(), b"27 97 360 12 7 0"),
        ("kernel", kernel(), b"3 4 5"),
        ("tail", tail(), b""),
        ("loops", loops(), b"5"),
    ]
}
