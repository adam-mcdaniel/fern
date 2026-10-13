//! Reads N and prints the primes up to N with a sieve in a heap array. Prints
//! the program as source; `hw/gen.sh` saves it as a hardware test.

use bf::asm::*;

fn main() {
    let o = &mut vec![];
    let (n, sieve, i, t, j, flag) = (R1, R2, R3, R4, R5, R6);
    init(o);
    getint(o, n);
    mov(o, t, n);
    inc(o, t);
    heap_alloc(o, sieve, t);

    // clear it, since the C backend's tape starts out uninitialized
    set(o, i, 0);
    set(o, t, 0);
    while_loop(o, flag, |o| { mov(o, flag, i); le_assign(o, flag, n); }, |o| {
        store_index(o, sieve, i, t);
        inc(o, i);
    });

    // cross out multiples of each prime up to sqrt(n)
    set(o, i, 1);
    begin_loop(o);
    inc(o, i);
    mov(o, t, i);
    mul_assign(o, t, i);
    gt_assign(o, t, n);
    break_if(o, t);
    load_index(o, t, sieve, i);
    begin_if(o, t);
    continue_loop(o);
    end_if(o);
    mov(o, j, i);
    mul_assign(o, j, i);
    set(o, t, 1);
    while_loop(o, flag, |o| { mov(o, flag, j); le_assign(o, flag, n); }, |o| {
        store_index(o, sieve, j, t);
        add_assign(o, j, i);
    });
    end_loop(o);

    set(o, i, 2);
    while_loop(o, flag, |o| { mov(o, flag, i); le_assign(o, flag, n); }, |o| {
        load_index(o, t, sieve, i);
        lnot_assign(o, t);
        begin_if(o, t);
        putint(o, i);
        puts(o, " ");
        end_if(o);
        inc(o, i);
    });
    puts(o, "\n");
    print!("{}", to_source(o));
}
