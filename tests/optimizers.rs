//! `opt_fast` and `opt_size` on programs the `asm` helpers build: each
//! optimized program prints what the program does, on the interpreter (with
//! the C backend's addresses and the CPU's, at 64 and 16 bits), and says how
//! many steps and ops it takes. `opt_size` never makes a program bigger.

mod common;

use bf::asm::*;
use bf::interp::Machine;
use bf::Op;
use common::*;

/// Checks a program both ways, and says how it went.
fn optimizes(name: &str, ops: Vec<Op>, input: &[u8]) -> (f64, f64) {
    let fast = opt_fast(ops.clone());
    let small = opt_size(ops.clone());
    assert!(small.len() <= ops.len(), "{name}: optimizing for size made {} ops {}", ops.len(), small.len());
    let mut ratios = (0.0, 0.0);
    for machine in [Machine { cells: 100_064, ..Machine::c() }, Machine { cells: 100_064, ..Machine::cpu() }, Machine { cells: 60_000, ..Machine::cpu_xlen(16) }] {
        let machine = Machine { max_steps: 2_000_000_000, ..machine };
        let Ok(want) = machine.run(&ops, input) else { continue };
        let got = machine.run(&fast, input).unwrap_or_else(|e| panic!("{name}: optimized for speed, it fails: {e}"));
        assert_eq!(String::from_utf8_lossy(&got.output), String::from_utf8_lossy(&want.output), "{name}: optimized for speed, it prints something else");
        let got_small = machine.run(&small, input).unwrap_or_else(|e| panic!("{name}: optimized for size, it fails: {e}"));
        assert_eq!(String::from_utf8_lossy(&got_small.output), String::from_utf8_lossy(&want.output), "{name}: optimized for size, it prints something else");
        if machine.xlen == 64 && machine.stride == 8 {
            eprintln!(
                "{name}: {} ops, {} steps; opt_fast {} ops ({:.0}%), {} steps ({:.0}%); opt_size {} ops ({:.0}%), {} steps ({:.0}%)",
                ops.len(),
                want.steps,
                fast.len(),
                100.0 * fast.len() as f64 / ops.len() as f64,
                got.steps,
                100.0 * got.steps as f64 / want.steps as f64,
                small.len(),
                100.0 * small.len() as f64 / ops.len() as f64,
                got_small.steps,
                100.0 * got_small.steps as f64 / want.steps as f64
            );
            ratios = (got.steps as f64 / want.steps as f64, small.len() as f64 / ops.len() as f64);
        }
    }
    ratios
}

#[test]
fn optimized_programs_print_the_same() {
    let mut all = vec![];
    // a sieve
    all.push(optimizes(
        "sieve",
        program(|o| {
            let (s, i, j, t, n) = (R1, R2, R3, R4, R5);
            set(o, n, 3000);
            heap_alloc(o, s, n);
            set(o, t, 1);
            for_range(o, i, 0, n, R0, |o| store_index(o, s, i, t));
            set(o, i, 2);
            while_loop(o, R0, |o| { mov(o, R0, i); mul_assign(o, R0, i); lt_assign(o, R0, n); }, |o| {
                load_index(o, t, s, i);
                begin_if(o, t);
                mov(o, j, i);
                mul_assign(o, j, i);
                set(o, t, 0);
                while_loop(o, R0, |o| { mov(o, R0, j); lt_assign(o, R0, n); }, |o| {
                    store_index(o, s, j, t);
                    add_assign(o, j, i);
                });
                end_if(o);
                inc(o, i);
            });
            set(o, t, 0);
            for_range(o, i, 2, n, R0, |o| {
                load_index(o, j, s, i);
                add_assign(o, t, j);
            });
            putint(o, t);
            puts(o, "\n");
        }),
        b"",
    ));
    // a small matrix product
    all.push(optimizes(
        "matmul",
        program(|o| {
            let (a, b, i, j, k, s, t, u) = (R1, R2, R3, R4, R5, R6, R7, R8);
            const N: i64 = 12;
            heap_alloc_const(o, a, N * N);
            heap_alloc_const(o, b, N * N);
            for_const(o, i, 0, N * N, R0, |o| {
                mov(o, t, i);
                rem_const(o, t, 7);
                store_index(o, a, i, t);
                mov(o, t, i);
                mul_const(o, t, 3);
                rem_const(o, t, 5);
                store_index(o, b, i, t);
            });
            set(o, u, 0);
            for_const(o, i, 0, N, R9, |o| {
                for_const(o, j, 0, N, R0, |o| {
                    set(o, s, 0);
                    for_const(o, k, 0, N, R0, |o| {
                        mov(o, t, i);
                        mul_const(o, t, N);
                        add_assign(o, t, k);
                        load_index(o, t, a, t);
                        push(o, t);
                        mov(o, t, k);
                        mul_const(o, t, N);
                        add_assign(o, t, j);
                        load_index(o, t, b, t);
                        pop(o, R0);
                        mul_assign(o, t, R0);
                        add_assign(o, s, t);
                    });
                    add_assign(o, u, s);
                });
            });
            putint(o, u);
            puts(o, "\n");
        }),
        b"",
    ));
    // functions: a recursive Fibonacci, through the stack
    all.push(optimizes(
        "fib",
        program(|o| {
            begin_func(o, "fib", 2);
            mov(o, &local(0), &arg(0));
            mov(o, R0, &local(0));
            lt_const(o, R0, 2);
            begin_if(o, R0);
            mov(o, R0, &local(0));
            begin_else(o);
            mov(o, R1, &local(0));
            dec(o, R1);
            call(o, "fib", &[R1]);
            mov(o, &local(1), R0);
            mov(o, R1, &local(0));
            sub_const(o, R1, 2);
            call(o, "fib", &[R1]);
            add_assign(o, R0, &local(1));
            end_if(o);
            end_func(o);
            set(o, R2, 16);
            call(o, "fib", &[R2]);
            putint(o, R0);
            puts(o, "\n");
        }),
        b"",
    ));
    // reading, and strings
    all.push(optimizes(
        "strings",
        program(|o| {
            let (buf, n, i, c, t) = (R1, R2, R3, R4, R5);
            heap_alloc_const(o, buf, 64);
            set(o, n, 63);
            read_line(o, R6, buf, n);
            str_len(o, n, buf);
            putint(o, n);
            puts(o, " ");
            // upper-case it, backwards
            mov(o, i, n);
            while_loop(o, R0, |o| mov(o, R0, i), |o| {
                dec(o, i);
                load_index(o, c, buf, i);
                mov(o, t, c);
                ge_const(o, t, 'a' as i64);
                mov(o, R0, c);
                le_const(o, R0, 'z' as i64);
                land_assign(o, t, R0);
                begin_if(o, t);
                sub_const(o, c, 32);
                end_if(o);
                putchar(o, c);
            });
            puts(o, "\n");
            heap_str(o, R7, "hello");
            str_cmp(o, t, R7, buf);
            putint(o, t);
            puts(o, "\n");
        }),
        b"Hello, optimizer world\n",
    ));
    // arithmetic of all kinds, on a few values
    all.push(optimizes(
        "arith",
        program(|o| {
            let (x, y, t) = (R1, R2, R3);
            for (a, b) in [(1234567i64, 89), (-5000, 7), (1 << 20, -3), (77, 77)] {
                set_int(o, x, a);
                set_int(o, y, b);
                for f in [add_assign, sub_assign, mul_assign, div_assign, rem_assign, lt_assign, ge_assign, eq_assign, and_assign, xor_assign] {
                    mov(o, t, x);
                    f(o, t, y);
                    putint(o, t);
                    puts(o, " ");
                }
                mov(o, t, x);
                rsh_const(o, t, 3);
                putint(o, t);
                puts(o, "\n");
            }
        }),
        b"",
    ));
    // collatz lengths
    all.push(optimizes(
        "collatz",
        program(|o| {
            let (n, x, steps, best, t) = (R1, R2, R3, R4, R5);
            set(o, best, 0);
            for_const(o, n, 1, 300, R9, |o| {
                mov(o, x, n);
                set(o, steps, 0);
                while_loop(o, R0, |o| { mov(o, R0, x); gt_const(o, R0, 1); }, |o| {
                    mov(o, t, x);
                    and_const(o, t, 1);
                    begin_if(o, t);
                    mul_const(o, x, 3);
                    inc(o, x);
                    begin_else(o);
                    rshu_const(o, x, 1);
                    end_if(o);
                    inc(o, steps);
                });
                max_assign(o, best, steps);
            });
            putint(o, best);
            puts(o, "\n");
        }),
        b"",
    ));
    let geo = |f: fn(&(f64, f64)) -> f64| (all.iter().map(|r| f(r).ln()).sum::<f64>() / all.len() as f64).exp();
    eprintln!("steps optimized for speed: {:.0}% of what they were; ops optimized for size: {:.0}%", 100.0 * geo(|r| r.0), 100.0 * geo(|r| r.1));
}
