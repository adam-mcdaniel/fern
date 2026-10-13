//! A program built with the SSA IR: reads numbers until a 0, and prints
//! facts about each. Prints the program as source; `hw/gen.sh` saves it as a
//! hardware test.

use bf::asm::ir::{optimize, Function, Module};
use bf::asm::to_source;

/// gcd(a, b), passing (b, a % b) around a loop.
fn gcd(f: &mut Function) {
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

/// How many steps of n -> n / 2 or 3n + 1 it takes to reach 1.
fn collatz(f: &mut Function) {
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

/// n!, recursively.
fn fact(f: &mut Function) {
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

fn main() {
    let mut m = Module::new();
    gcd(m.function("gcd", 2));
    collatz(m.function("collatz", 1));
    fact(m.function("fact", 1));

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
    f.put_int(n);
    f.puts(": collatz ");
    let steps = f.call("collatz", &[n]);
    f.put_int(steps);
    f.puts(", gcd with 360 ");
    let k = f.int(360);
    let g = f.call("gcd", &[n, k]);
    f.put_int(g);
    let eight = f.int(8);
    let small = f.rem(n, eight);
    f.puts(", ");
    f.put_int(small);
    f.puts("! = ");
    let r = f.call("fact", &[small]);
    f.put_int(r);
    f.puts("\n");
    f.jump(head, &[]);
    f.switch_to(done);
    f.ret_void();

    optimize(&mut m);
    if std::env::args().any(|a| a == "--ir") {
        print!("{m}");
    } else {
        print!("{}", to_source(&bf::asm::ir::lower(&m).unwrap()));
    }
}
