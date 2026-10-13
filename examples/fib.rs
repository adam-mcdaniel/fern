//! Reads a count and then that many numbers, and prints the Fibonacci number
//! of each, computed recursively. Prints the program as source; `hw/gen.sh`
//! saves it as a hardware test.

use bf::asm::*;

fn main() {
    let o = &mut vec![];

    begin_func(o, "fib", 2);
    mov(o, R1, &arg(0));
    lt_const(o, R1, 2);
    begin_if(o, R1);
    mov(o, R0, &arg(0));
    ret(o);
    end_if(o);
    mov(o, &local(0), &arg(0));
    dec(o, &local(0));
    call(o, "fib", &[&local(0)]);
    mov(o, &local(1), R0);
    dec(o, &local(0));
    call(o, "fib", &[&local(0)]);
    add_assign(o, R0, &local(1));
    end_func(o);

    init(o);
    getint(o, R5);
    while_loop(
        o,
        R6,
        |o| {
            mov(o, R6, R5);
            gt_const(o, R6, 0);
        },
        |o| {
            getint(o, R7);
            // fib only uses R0 and R1, so R5 and R7 survive the call
            call(o, "fib", &[R7]);
            puts(o, "fib(");
            putint(o, R7);
            puts(o, ") = ");
            putint(o, R0);
            puts(o, "\n");
            dec(o, R5);
        },
    );
    print!("{}", to_source(o));
}
