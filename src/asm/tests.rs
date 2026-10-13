use super::*;
use crate::interp::Machine;

/// Runs a program with the CPU's and the C backend's address models and
/// checks that their output agrees. Returns the output and a way to read
/// registers, which also checks that both models agree on the value (so
/// don't use it on registers holding addresses).
fn run_with(input: &[u8], build: impl Fn(&mut Vec<Op>)) -> (String, impl Fn(&Location) -> i64) {
    let mut ops = vec![];
    build(&mut ops);
    crate::cpu::assemble(&ops, 64).expect("the CPU backend rejected the program");
    let cpu = Machine::cpu().run(&ops, input).unwrap();
    let c = Machine::c().run(&ops, input).unwrap();
    assert_eq!(cpu.output, c.output, "address models disagree");
    let output = String::from_utf8(cpu.output).unwrap();
    let value = move |loc: &Location| {
        let Location::Static(StaticLocation(i)) = loc else { panic!("not a register") };
        let (x, y) = (cpu.tape[*i as usize], c.tape[*i as usize]);
        assert_eq!(x, y, "address models disagree");
        x
    };
    (output, value)
}

fn run(build: impl Fn(&mut Vec<Op>)) -> String {
    run_with(b"", build).0
}

type BinOp = fn(&mut dyn Program, &Location, &Location);

/// `R1 = a; R2 = b; f(R1, R2)`, returning R1 and checking R2 is untouched.
fn binop(f: BinOp, a: i64, b: i64) -> i64 {
    let (_, value) = run_with(b"", |o| {
        set(o, R1, a as u64);
        set(o, R2, b as u64);
        f(o, R1, R2);
    });
    assert_eq!(value(R2), b, "src was modified");
    value(R1)
}

struct Rng(u64);

impl Rng {
    fn bits(&mut self, bits: u32) -> i64 {
        self.0 ^= self.0 << 13;
        self.0 ^= self.0 >> 7;
        self.0 ^= self.0 << 17;
        ((self.0 >> 1) & ((1u64 << bits) - 1)) as i64
    }

    fn signed(&mut self, bits: u32) -> i64 {
        let x = self.bits(bits);
        if self.bits(1) == 1 { -x } else { x }
    }

    /// Any 64-bit value.
    fn any(&mut self) -> i64 {
        (self.bits(32) << 32) ^ self.bits(32)
    }
}

#[test]
fn arithmetic_matches_rust() {
    let mut rng = Rng(0x9e3779b97f4a7c15);
    for bits in [3, 8, 16, 32, 48, 62, 64] {
        for _ in 0..4 {
            let (a, b) = if bits == 64 { (rng.any(), rng.any()) } else { (rng.signed(bits), rng.signed(bits)) };
            let s = rng.bits(7) % 70;
            assert_eq!(binop(add_assign, a, b), a.wrapping_add(b));
            assert_eq!(binop(sub_assign, a, b), a.wrapping_sub(b));
            assert_eq!(binop(mul_assign, a, b), a.wrapping_mul(b), "{a} * {b}");
            if b != 0 {
                assert_eq!(binop(div_assign, a, b), a / b, "{a} / {b}");
                assert_eq!(binop(rem_assign, a, b), a % b, "{a} % {b}");
            }
            assert_eq!(binop(xor_assign, a, b), a ^ b, "{a} ^ {b}");
            assert_eq!(binop(and_assign, a, b), a & b, "{a} & {b}");
            assert_eq!(binop(or_assign, a, b), a | b, "{a} | {b}");
            assert_eq!(binop(lsh_assign, a, s), a.checked_shl(s as u32).unwrap_or(0), "{a} << {s}");
            let rsh = a.checked_shr(s as u32).unwrap_or(if a < 0 { -1 } else { 0 });
            assert_eq!(binop(rsh_assign, a, s), rsh, "{a} >> {s}");
        }
    }
}

#[test]
fn arithmetic_edge_cases() {
    let (min, max) = (i64::MIN, i64::MAX);
    assert_eq!(binop(div_assign, 7, 0), -1);
    assert_eq!(binop(rem_assign, 7, 0), 7);
    assert_eq!(binop(div_assign, -7, 0), -1);
    assert_eq!(binop(rem_assign, -7, 0), -7);
    assert_eq!(binop(div_assign, max, 1), max);
    assert_eq!(binop(div_assign, max, max), 1);
    assert_eq!(binop(rsh_assign, -1, 63), -1);
    assert_eq!(binop(rsh_assign, 100, -3), 100);
    assert_eq!(binop(lsh_assign, 100, -3), 100);
    assert_eq!(binop(mul_assign, 0, -5), 0);
    assert_eq!(binop(mul_assign, -1, -1), 1);
    // the most negative value
    for (a, b) in [(min, 1), (min, -1), (min, 2), (min, -3), (min, min), (min, max), (max, min), (5, min), (-5, min), (min, 7)] {
        assert_eq!(binop(div_assign, a, b), a.wrapping_div(b), "{a} / {b}");
        assert_eq!(binop(rem_assign, a, b), a.wrapping_rem(b), "{a} % {b}");
        assert_eq!(binop(mul_assign, a, b), a.wrapping_mul(b), "{a} * {b}");
        assert_eq!(binop(mul_assign, b, a), b.wrapping_mul(a), "{b} * {a}");
        assert_eq!(binop(xor_assign, a, b), a ^ b);
        assert_eq!(binop(and_assign, a, b), a & b);
        assert_eq!(binop(or_assign, a, b), a | b);
    }
    assert_eq!(binop(rsh_assign, min, 1), min >> 1);
    assert_eq!(binop(rsh_assign, min, 63), -1);
    assert_eq!(binop(rsh_assign, min, max), -1);
    assert_eq!(binop(rsh_assign, max, 64), 0);
    assert_eq!(binop(div_assign, min, 0), -1);
    assert_eq!(binop(rem_assign, min, 0), min);
}

#[test]
fn same_register_for_both_operands() {
    let alias = |f: BinOp, x: i64| {
        let (_, value) = run_with(b"", |o| {
            set(o, R1, x as u64);
            f(o, R1, R1);
        });
        value(R1)
    };
    assert_eq!(alias(mul_assign, -6), 36);
    assert_eq!(alias(div_assign, -6), 1);
    assert_eq!(alias(rem_assign, -6), 0);
    assert_eq!(alias(xor_assign, 6), 0);
    assert_eq!(alias(eq_assign, 6), 1);
    assert_eq!(alias(lt_assign, 6), 0);
    assert_eq!(alias(min_assign, 6), 6);
}

#[test]
fn comparisons() {
    // including pairs where a - b overflows
    let vals = [i64::MIN, i64::MIN + 1, -7, -1, 0, 1, 2, i64::MAX - 1, i64::MAX];
    for a in vals {
        for b in vals {
            assert_eq!(binop(lt_assign, a, b), (a < b) as i64, "{a} < {b}");
            assert_eq!(binop(gt_assign, a, b), (a > b) as i64, "{a} > {b}");
            assert_eq!(binop(le_assign, a, b), (a <= b) as i64, "{a} <= {b}");
            assert_eq!(binop(ge_assign, a, b), (a >= b) as i64, "{a} >= {b}");
            assert_eq!(binop(eq_assign, a, b), (a == b) as i64, "{a} == {b}");
            assert_eq!(binop(ne_assign, a, b), (a != b) as i64, "{a} != {b}");
            assert_eq!(binop(min_assign, a, b), a.min(b));
            assert_eq!(binop(max_assign, a, b), a.max(b));
        }
    }
}

#[test]
fn logical_ops() {
    let vals = [0, 1, -3, 9];
    for a in vals {
        for b in vals {
            assert_eq!(binop(land_assign, a, b), (a != 0 && b != 0) as i64);
            assert_eq!(binop(lor_assign, a, b), (a != 0 || b != 0) as i64);
        }
    }
    let unop = |f: fn(&mut dyn Program, &Location), x: i64| {
        let (_, value) = run_with(b"", |o| {
            set(o, R1, x as u64);
            f(o, R1);
        });
        value(R1)
    };
    for x in [i64::MIN, -3, 0, 1, 9] {
        assert_eq!(unop(lnot_assign, x), (x == 0) as i64);
        assert_eq!(unop(neg_assign, x), x.wrapping_neg());
        assert_eq!(unop(not_assign, x), !x);
    }
    for x in [i64::MIN, -3, 0, 1, 9] {
        assert_eq!(unop(abs_assign, x), x.wrapping_abs());
    }
}

#[test]
fn if_else() {
    let out = run(|o| {
        for c in [0i64, 1, -3] {
            set(o, R1, c as u64);
            begin_if(o, R1);
            puts(o, "T");
            begin_else(o);
            puts(o, "F");
            end_if(o);
        }
        // nested in both branches
        for (x, y) in [(0, 0), (0, 1), (1, 0), (1, 1)] {
            set(o, R1, x);
            set(o, R2, y);
            begin_if(o, R1);
            begin_if(o, R2);
            puts(o, "A");
            begin_else(o);
            puts(o, "B");
            end_if(o);
            begin_else(o);
            begin_if(o, R2);
            puts(o, "C");
            end_if(o);
            end_if(o);
        }
    });
    assert_eq!(out, "FTTCBA");
}

#[test]
fn while_loop_with_a_comparison() {
    let out = run(|o| {
        set(o, R1, 0);
        set(o, R2, 5);
        while_loop(
            o,
            R3,
            |o| {
                mov(o, R3, R1);
                lt_assign(o, R3, R2);
            },
            |o| {
                putint(o, R1);
                inc(o, R1);
            },
        );
    });
    assert_eq!(out, "01234");
}

#[test]
fn printing() {
    let vals = [0, 7, 10, 99, 100, 12345, -1, -909, i64::MAX, i64::MIN, i64::MIN + 1];
    let out = run(|o| {
        puts(o, "n:");
        for v in vals {
            set(o, R1, v as u64);
            putint(o, R1);
            puts(o, " ");
        }
    });
    let want: String = vals.iter().map(|v| format!("{v} ")).collect();
    assert_eq!(out, format!("n:{want}"));
}

#[test]
fn reading_numbers() {
    let (out, _) = run_with(b"  42\n-17 x 0007", |o| {
        for _ in 0..4 {
            getint(o, R1);
            putint(o, R1);
            puts(o, ",");
        }
    });
    assert_eq!(out, "42,-17,0,7,");
}

#[test]
fn pointers_and_arrays() {
    let (out, value) = run_with(b"", |o| {
        // R1 = 99 through a pointer to it
        addr_of(o, R2, R1);
        set(o, R3, 99);
        mov(o, &R2.deref(), R3);

        // squares into an array, then sum them back
        addr_of(o, R3, &STACK_START.offset(100));
        set(o, R4, 0);
        set(o, R6, 10);
        let i_lt_10 = |o: &mut dyn Program| {
            mov(o, R7, R4);
            lt_assign(o, R7, R6);
        };
        while_loop(o, R7, i_lt_10, |o| {
            mov(o, R5, R4);
            mul_assign(o, R5, R4);
            store_index(o, R3, R4, R5);
            inc(o, R4);
        });
        set(o, R4, 0);
        set(o, R8, 0);
        while_loop(o, R7, i_lt_10, |o| {
            load_index(o, R5, R3, R4);
            add_assign(o, R8, R5);
            inc(o, R4);
        });
        putint(o, R8);
        puts(o, " ");

        // negative index: element 7 seen from element 9
        set(o, R4, 9);
        index(o, R5, R3, R4);
        set(o, R4, -2i64 as u64);
        load_index(o, R8, R5, R4);
        putint(o, R8);
    });
    assert_eq!(value(R1), 99);
    assert_eq!(out, "285 49");
}

#[test]
fn stack() {
    let out = run(|o| {
        init(o);
        for v in [1, 2, 3] {
            set(o, R1, v);
            push(o, R1);
        }
        for _ in 0..3 {
            pop(o, R1);
            putint(o, R1);
        }
    });
    assert_eq!(out, "321");
}

#[test]
fn functions() {
    let (out, value) = run_with(b"", |o| {
        begin_func(o, "sub", 0);
        mov(o, R0, &arg(0));
        sub_assign(o, R0, &arg(1));
        end_func(o);

        // recursive, with locals that must survive the inner calls
        begin_func(o, "fib", 2);
        mov(o, R1, &arg(0));
        set(o, R2, 2);
        lt_assign(o, R1, R2);
        begin_if(o, R1);
        mov(o, R0, &arg(0));
        begin_else(o);
        mov(o, &local(0), &arg(0));
        dec(o, &local(0));
        call(o, "fib", &[&local(0)]);
        mov(o, &local(1), R0);
        dec(o, &local(0));
        call(o, "fib", &[&local(0)]);
        add_assign(o, R0, &local(1));
        end_if(o);
        end_func(o);

        init(o);
        mov(o, R9, SP);
        set(o, R1, 10);
        set(o, R2, 3);
        call(o, "sub", &[R1, R2]);
        putint(o, R0);
        puts(o, " ");
        set(o, R1, 15);
        call(o, "fib", &[R1]);
        putint(o, R0);
        // R3 = SP is back where it started
        mov(o, R3, SP);
        eq_assign(o, R3, R9);
    });
    assert_eq!(out, "7 610");
    assert_eq!(value(R3), 1, "SP not restored");
}

#[test]
fn functions_defined_anywhere() {
    let program = |o: &mut Vec<Op>| {
        init(o);
        set(o, R1, 3);
        set(o, R4, 0);
        // defined inside a loop, and named like C's own functions
        while_loop(o, R5, |o| mov(o, R5, R1), |o| {
            begin_func(o, "puts", 0);
            mov(o, R0, &arg(0));
            add_assign(o, R0, R0);
            end_func(o);

            call(o, "puts", &[R1]);
            add_assign(o, R4, R0);
            dec(o, R1);
        });
        putint(o, R4);
        puts(o, " ");

        // defined inside an if, with another function defined inside it
        set(o, R1, 1);
        begin_if(o, R1);
        begin_func(o, "main", 1);
        begin_func(o, "inner", 0);
        set(o, R0, 40);
        end_func(o);
        call(o, "inner", &[]);
        set(o, R2, 2);
        add_assign(o, R0, R2);
        end_func(o);
        end_if(o);

        call(o, "main", &[]);
        putint(o, R0);
    };
    assert_eq!(run(program), "12 42");

    // every definition ended up at the top level
    let mut ops = vec![];
    program(&mut ops);
    let mut depth = 0;
    for op in &ops {
        match op {
            Op::Func => assert_eq!(depth, 0, "function not at the top level"),
            Op::While => depth += 1,
            Op::EndWhile => depth -= 1,
            _ => {}
        }
    }
}

/// Sign-extends the low `xlen` bits of `v`.
fn wrap(v: i64, xlen: u32) -> i64 {
    (v << (64 - xlen)) >> (64 - xlen)
}

/// Runs on the CPU's address model with `xlen`-bit cells, returning the
/// output and R1.
fn run_xlen(xlen: u32, build: impl Fn(&mut Vec<Op>)) -> (String, i64) {
    let mut ops = vec![];
    build(&mut ops);
    let halted = Machine::cpu_xlen(xlen).run(&ops, b"").unwrap();
    let Location::Static(StaticLocation(r1)) = R1 else { unreachable!() };
    (String::from_utf8(halted.output).unwrap(), halted.tape[*r1 as usize])
}

#[test]
fn narrow_cells() {
    let mut rng = Rng(0x2545f4914f6cdd1d);
    // 8-bit cores can't hold the shared routines: they only address 256
    // bytes of program
    for xlen in [16, 32] {
        let (min, max) = (wrap(1 << (xlen - 1), xlen), (1i64 << (xlen - 1)) - 1);
        let mut pairs: Vec<(i64, i64)> = (0..12).map(|_| (wrap(rng.any(), xlen), wrap(rng.any(), xlen))).collect();
        pairs.extend([(min, -1), (min, 1), (min, min), (max, min), (min, max), (max, 2), (-1, max)]);
        for (a, b) in pairs {
            let op = |f: BinOp, b: i64| {
                run_xlen(xlen, |o| {
                    set(o, R1, a as u64);
                    set(o, R2, b as u64);
                    f(o, R1, R2);
                })
                .1
            };
            let s = rng.bits(6) % (xlen as i64 + 4);
            let w = |v: i64| wrap(v, xlen);
            assert_eq!(op(add_assign, b), w(a + b), "{xlen}: {a} + {b}");
            assert_eq!(op(sub_assign, b), w(a - b), "{xlen}: {a} - {b}");
            assert_eq!(op(mul_assign, b), w(a.wrapping_mul(b)), "{xlen}: {a} * {b}");
            if b != 0 {
                assert_eq!(op(div_assign, b), w(a / b), "{xlen}: {a} / {b}");
                assert_eq!(op(rem_assign, b), a % b, "{xlen}: {a} % {b}");
            }
            assert_eq!(op(xor_assign, b), a ^ b);
            assert_eq!(op(and_assign, b), a & b);
            assert_eq!(op(or_assign, b), a | b);
            assert_eq!(op(lt_assign, b), (a < b) as i64, "{xlen}: {a} < {b}");
            assert_eq!(op(ge_assign, b), (a >= b) as i64, "{xlen}: {a} >= {b}");
            assert_eq!(op(lsh_assign, s), w(a << s), "{xlen}: {a} << {s}");
            assert_eq!(op(rsh_assign, s), a >> s, "{xlen}: {a} >> {s}");
        }

        let (out, _) = run_xlen(xlen, |o| {
            for v in [min, max, -1, 0, 100] {
                set(o, R1, v as u64);
                putint(o, R1);
                puts(o, " ");
            }
        });
        assert_eq!(out, format!("{min} {max} -1 0 100 "));
    }
}

#[test]
fn narrow_cells_call_functions() {
    // defined after the main code, so it starts past op 255
    let program = |o: &mut Vec<Op>| {
        init(o);
        set(o, R1, 21);
        call(o, "twice", &[R1]);
        putint(o, R0);
        begin_func(o, "twice", 0);
        mov(o, R0, &arg(0));
        add_assign(o, R0, R0);
        end_func(o);
    };
    assert_eq!(run_xlen(16, program).0, "42");
    // too big for 8-bit code addresses, as on the real CPU
    let mut ops = vec![];
    program(&mut ops);
    assert!(Machine::cpu_xlen(8).run(&ops, b"").is_err());
}

fn build(f: impl Fn(&mut Vec<Op>)) -> Vec<Op> {
    let mut ops = vec![];
    f(&mut ops);
    ops
}

fn count_funcs(ops: &[Op]) -> usize {
    ops.iter().filter(|op| **op == Op::Func).count()
}

#[test]
fn routines_are_defined_once() {
    let one = build(|o| {
        putint(o, R1);
        div_assign(o, R1, R1);
        mul_assign(o, R1, R2);
    });
    let many = build(|o| {
        for r in [R1, R2, R3, R4, R5, R6] {
            putint(o, r);
            div_assign(o, r, R1);
            mul_assign(o, r, R2);
        }
    });
    assert_eq!(count_funcs(&one), count_funcs(&many));
    // each extra use is just a call, not another copy
    let per_use = (many.len() - one.len()) / 15;
    assert!(per_use < 40, "{per_use} ops per use");
    // and the whole program is small enough for the CPU's 4 KiB default
    let bytes = crate::cpu::assemble(&many, 64).unwrap().len();
    assert!(bytes < 4096, "{bytes} bytes");
}

#[test]
fn peephole_merges_moves_and_drops_dead_ops() {
    let ops = build(|o| {
        mov(o, R1, R2);
        mov(o, R3, R1);
    });
    // moves between neighbouring helpers are merged, and the second mov's
    // load of R1 is dropped because acc already holds it
    let loads = ops.iter().filter(|op| **op == Op::Load).count();
    assert_eq!(loads, 1);
    for pair in ops.windows(2) {
        assert!(!matches!(pair, [Op::Move(_), Op::Move(_)]), "unmerged moves");
    }
}

#[test]
fn source_round_trips() {
    let ops = build(|o| {
        init(o);
        begin_func(o, "f", 1);
        set_int(o, &local(0), -12345);
        putint(o, &local(0));
        end_func(o);
        call(o, "f", &[]);
        set(o, R1, u64::MAX);
        set(o, R2, 7);
        set(o, R3, 8);
        div_assign(o, R1, R2);
    });
    let source = to_source(&ops);
    assert_eq!(crate::parse(&source).unwrap(), ops);
}

#[test]
fn constants() {
    let unop = |f: &dyn Fn(&mut Vec<Op>), x: i64| {
        let (_, value) = run_with(b"", |o| {
            set_int(o, R1, x);
            f(o);
        });
        value(R1)
    };
    for x in [i64::MIN, -100, -1, 0, 1, 7, 12345, i64::MAX] {
        for k in [i64::MIN, -1000, -3, -1, 0, 1, 2, 10, 255, i64::MAX] {
            assert_eq!(unop(&|o| add_const(o, R1, k), x), x.wrapping_add(k));
            assert_eq!(unop(&|o| sub_const(o, R1, k), x), x.wrapping_sub(k));
            assert_eq!(unop(&|o| mul_const(o, R1, k), x), x.wrapping_mul(k), "{x} * {k}");
            if k != 0 {
                assert_eq!(unop(&|o| div_const(o, R1, k), x), x.wrapping_div(k), "{x} / {k}");
                assert_eq!(unop(&|o| rem_const(o, R1, k), x), x.wrapping_rem(k), "{x} % {k}");
            }
            assert_eq!(unop(&|o| lt_const(o, R1, k), x), (x < k) as i64);
            assert_eq!(unop(&|o| gt_const(o, R1, k), x), (x > k) as i64);
            assert_eq!(unop(&|o| le_const(o, R1, k), x), (x <= k) as i64);
            assert_eq!(unop(&|o| ge_const(o, R1, k), x), (x >= k) as i64);
            assert_eq!(unop(&|o| eq_const(o, R1, k), x), (x == k) as i64);
            assert_eq!(unop(&|o| ne_const(o, R1, k), x), (x != k) as i64);
        }
    }
}

#[test]
fn unsigned_ops() {
    let mut rng = Rng(0x5851f42d4c957f2d);
    let mut pairs: Vec<(u64, u64)> = (0..12).map(|_| (rng.any() as u64, rng.any() as u64)).collect();
    pairs.extend([(u64::MAX, 1), (u64::MAX, u64::MAX), (1 << 63, 3), (5, u64::MAX), (100, 7), (0, 9)]);
    for (a, b) in pairs {
        let op = |f: BinOp| binop(f, a as i64, b as i64) as u64;
        assert_eq!(op(divu_assign), a / b, "{a} / {b}");
        assert_eq!(op(remu_assign), a % b, "{a} % {b}");
        assert_eq!(op(ltu_assign), (a < b) as u64, "{a} < {b}");
        assert_eq!(op(gtu_assign), (a > b) as u64);
        assert_eq!(op(leu_assign), (a <= b) as u64);
        assert_eq!(op(geu_assign), (a >= b) as u64);
        let s = b % 70;
        assert_eq!(binop(rshu_assign, a as i64, s as i64) as u64, a.checked_shr(s as u32).unwrap_or(0), "{a} >> {s}");
    }
    assert_eq!(binop(divu_assign, 7, 0), -1);
    assert_eq!(binop(remu_assign, 7, 0), 7);

    let vals = [0, 7, u64::MAX, 1 << 63, 12345678901234567890];
    let out = run(|o| {
        for v in vals {
            set(o, R1, v);
            putuint(o, R1);
            puts(o, " ");
        }
    });
    let want: String = vals.iter().map(|v| format!("{v} ")).collect();
    assert_eq!(out, want);
}

#[test]
fn huge_shift_counts_are_quick() {
    // these would take ~10^12 passes one bit at a time
    assert_eq!(binop(lsh_assign, 5, 1_000_000_000_000), 0);
    assert_eq!(binop(rsh_assign, -5, 1_000_000_000_000), -1);
    assert_eq!(binop(rshu_assign, -5, 1_000_000_000_000), 0);
}

#[test]
fn heap_and_strings() {
    let (out, value) = run_with(b"hello world\nhi\n", |o| {
        init(o);
        // an array sized at run time
        set(o, R1, 10);
        heap_alloc(o, R2, R1);
        set(o, R3, 0);
        while_loop(o, R4, |o| { mov(o, R4, R3); lt_const(o, R4, 10); }, |o| {
            mov(o, R5, R3);
            mul_const(o, R5, 3);
            store_index(o, R2, R3, R5);
            inc(o, R3);
        });
        set(o, R3, 9);
        load_index(o, R6, R2, R3);
        putint(o, R6);
        puts(o, "|");

        heap_str(o, R7, "hello");
        print_str(o, R7);
        str_len(o, R6, R7);
        putint(o, R6);
        puts(o, "|");

        // read lines into a 6-cell buffer: 5 characters and the 0
        heap_alloc_const(o, R8, 6);
        set(o, R1, 6);
        for _ in 0..3 {
            read_line(o, R6, R8, R1);
            print_str(o, R8);
            puts(o, ":");
            putint(o, R6);
            puts(o, ",");
        }
        puts(o, "|");

        for (a, b) in [("abc", "abd"), ("abc", "abc"), ("b", "abc"), ("ab", "abc"), ("", "")] {
            heap_str(o, R2, a);
            heap_str(o, R3, b);
            str_cmp(o, R4, R2, R3);
            putint(o, R4);
            puts(o, " ");
        }
        // the first array is untouched by later allocations
        set(o, R3, 4);
        load_index(o, R0, R2, R3);
        heap_str(o, R2, "");
    });
    // "hello world" is cut at 5 characters; the rest of the line comes next
    assert_eq!(out, "27|hello5|hello:5, worl:5,d:1,|-1 0 1 -1 0 ");
    let _ = value;
}

#[test]
fn break_and_continue() {
    let out = run(|o| {
        // print odd numbers below 10, stopping at 7
        set(o, R1, 0);
        begin_loop(o);
        inc(o, R1);
        mov(o, R2, R1);
        eq_const(o, R2, 7);
        break_if(o, R2);
        mov(o, R2, R1);
        rem_const(o, R2, 2);
        lnot_assign(o, R2);
        begin_if(o, R2);
        continue_loop(o);
        end_if(o);
        putint(o, R1);
        end_loop(o);
        puts(o, "|");

        // nested loops: break only leaves the inner one
        set(o, R1, 0);
        while_loop(o, R3, |o| { mov(o, R3, R1); lt_const(o, R3, 3); }, |o| {
            set(o, R2, 0);
            begin_loop(o);
            mov(o, R4, R2);
            gt_assign(o, R4, R1);
            begin_if(o, R4);
            break_loop(o);
            puts(o, "never");
            end_if(o);
            putint(o, R2);
            inc(o, R2);
            end_loop(o);
            puts(o, ",");
            inc(o, R1);
        });
    });
    assert_eq!(out, "135|0,01,012,");
}

#[test]
fn early_return() {
    let out = run(|o| {
        // the first divisor of arg 0 above 1, returning from inside a loop
        begin_func(o, "divisor", 0);
        set(o, R1, 2);
        begin_loop(o);
        mov(o, R2, &arg(0));
        rem_assign(o, R2, R1);
        lnot_assign(o, R2);
        begin_if(o, R2);
        mov(o, R0, R1);
        ret(o);
        end_if(o);
        inc(o, R1);
        end_loop(o);
        puts(o, "unreachable");
        end_func(o);

        // recursive, returning early from the base case
        begin_func(o, "fact", 1);
        mov(o, R1, &arg(0));
        le_const(o, R1, 1);
        begin_if(o, R1);
        set(o, R0, 1);
        ret(o);
        end_if(o);
        mov(o, &local(0), &arg(0));
        dec(o, &local(0));
        call(o, "fact", &[&local(0)]);
        mul_assign(o, R0, &arg(0));
        end_func(o);

        init(o);
        for n in [15, 49, 97] {
            set(o, R5, n);
            call(o, "divisor", &[R5]);
            putint(o, R0);
            puts(o, " ");
        }
        set(o, R5, 10);
        call(o, "fact", &[R5]);
        putint(o, R0);
        puts(o, " ");

        // a callee that breaks out of and returns from its own loops doesn't
        // disturb the caller's loop
        set(o, R6, 0);
        begin_loop(o);
        mov(o, R5, R6);
        add_const(o, R5, 20);
        call(o, "divisor", &[R5]);
        putint(o, R0);
        inc(o, R6);
        mov(o, R7, R6);
        eq_const(o, R7, 3);
        break_if(o, R7);
        puts(o, ",");
        end_loop(o);
    });
    assert_eq!(out, "3 7 97 3628800 2,3,2");
}

#[test]
#[should_panic(expected = "break_loop outside a loop")]
fn break_outside_a_loop() {
    build(|o| break_loop(o));
}

#[test]
#[should_panic(expected = "can't leave a begin_while loop")]
fn break_through_a_raw_loop() {
    build(|o| {
        begin_loop(o);
        begin_while(o, R1);
        break_loop(o);
    });
}

#[test]
#[should_panic(expected = "ret outside a function")]
fn ret_outside_a_function() {
    build(|o| ret(o));
}

#[test]
fn routines_first_used_inside_an_if_dont_run_it() {
    // the routine's definition is hoisted out of the `if`, and must not land
    // between loading the condition and testing it
    let out = run(|o| {
        set(o, R1, 0);
        begin_if(o, R1);
        putint(o, R1);
        end_if(o);
        puts(o, "|");
    });
    assert_eq!(out, "|");
}

#[test]
fn comparisons_and_multiplication_for_small_values() {
    let vals = [-32000, -100, -1, 0, 1, 2, 77, 32000];
    for a in vals {
        for b in vals {
            if (a - b as i64).abs() > 32767 {
                continue;
            }
            assert_eq!(binop(lt_small, a, b), (a < b) as i64, "{a} < {b}");
            assert_eq!(binop(le_small, a, b), (a <= b) as i64, "{a} <= {b}");
            assert_eq!(binop(gt_small, a, b), (a > b) as i64, "{a} > {b}");
            assert_eq!(binop(ge_small, a, b), (a >= b) as i64, "{a} >= {b}");
            let with_const = |f: fn(&mut dyn Program, &Location, i64)| {
                let (_, value) = run_with(b"", |o| {
                    set_int(o, R1, a);
                    f(o, R1, b);
                });
                value(R1)
            };
            assert_eq!(with_const(lt_const_small), (a < b) as i64, "{a} < {b}");
            assert_eq!(with_const(le_const_small), (a <= b) as i64, "{a} <= {b}");
            assert_eq!(with_const(gt_const_small), (a > b) as i64, "{a} > {b}");
            assert_eq!(with_const(ge_const_small), (a >= b) as i64, "{a} >= {b}");
        }
    }
    for a in [i64::MIN, -5, 0, 7, i64::MAX] {
        for n in [0, 1, 2, 9] {
            assert_eq!(binop(mul_small_assign, a, n), a.wrapping_mul(n), "{a} * {n}");
        }
    }
}

type ConstOp = fn(&mut dyn Program, &Location, i64);

/// `R1 = x; f(R1, k)` on a CPU with `xlen`-bit cells.
fn const_op_xlen(f: ConstOp, x: i64, k: i64, xlen: u32) -> i64 {
    let mut ops = vec![];
    set_int(&mut ops, R1, x);
    f(&mut ops, R1, k);
    let halted = Machine::cpu_xlen(xlen).run(&ops, b"").unwrap();
    let Location::Static(StaticLocation(r1)) = R1 else { unreachable!() };
    halted.tape[*r1 as usize]
}

#[test]
fn constant_forms_match_rust() {
    let ks: [i64; 16] = [1, 2, 3, 7, 8, 10, 255, 1000, 16383, 16384, 32767, -1, -8, -255, 1 << 20, i64::MIN];
    let xs: [i64; 10] = [0, 1, -1, 5, -77, 12345, -32768, 1 << 40, i64::MAX, i64::MIN];
    for &k in &ks {
        for &x in &xs {
            let unop = |f: ConstOp| {
                let (_, value) = run_with(b"", |o| {
                    set_int(o, R1, x);
                    f(o, R1, k);
                });
                value(R1)
            };
            assert_eq!(unop(and_const), x & k, "{x} & {k}");
            assert_eq!(unop(or_const), x | k, "{x} | {k}");
            assert_eq!(unop(xor_const), x ^ k, "{x} ^ {k}");
            assert_eq!(unop(div_const), x.wrapping_div(k), "{x} / {k}");
            assert_eq!(unop(rem_const), x.wrapping_rem(k), "{x} % {k}");
            let (ux, uk) = (x as u64, k as u64);
            assert_eq!(unop(divu_const) as u64, ux / uk, "{x} /u {k}");
            assert_eq!(unop(remu_const) as u64, ux % uk, "{x} %u {k}");
        }
    }
    for x in xs {
        for s in [0, 1, 3, 8, 9, 15, 63, 64, 100] {
            let unop = |f: ConstOp| {
                let (_, value) = run_with(b"", |o| {
                    set_int(o, R1, x);
                    f(o, R1, s);
                });
                value(R1)
            };
            assert_eq!(unop(lsh_const), x.checked_shl(s as u32).unwrap_or(0), "{x} << {s}");
            assert_eq!(unop(rsh_const), x.checked_shr(s as u32).unwrap_or(if x < 0 { -1 } else { 0 }), "{x} >> {s}");
            assert_eq!(unop(rshu_const) as u64, (x as u64).checked_shr(s as u32).unwrap_or(0), "{x} >>u {s}");
        }
    }
    // narrower cells, where the shifts move bits a different distance
    let wrap = |v: i64| v as i16 as i64;
    for &k in &[1i64, 3, 8, 10, 255, 1000, -8] {
        for &x in &[0i64, 1, -1, 5, -77, 12345, -32768, 32767] {
            assert_eq!(const_op_xlen(and_const, x, k, 16), wrap(x & k));
            assert_eq!(const_op_xlen(or_const, x, k, 16), wrap(x | k));
            assert_eq!(const_op_xlen(xor_const, x, k, 16), wrap(x ^ k));
            assert_eq!(const_op_xlen(div_const, x, k, 16), wrap((x as i16).wrapping_div(k as i16) as i64), "{x} / {k}");
            assert_eq!(const_op_xlen(rem_const, x, k, 16), wrap((x as i16).wrapping_rem(k as i16) as i64), "{x} % {k}");
            if k > 0 {
                assert_eq!(const_op_xlen(divu_const, x, k, 16), wrap(((x as u16) / k as u16) as i64), "{x} /u {k}");
                assert_eq!(const_op_xlen(remu_const, x, k, 16), wrap(((x as u16) % k as u16) as i64), "{x} %u {k}");
            }
        }
        for s in [1, 7, 15, 16, 20] {
            let x = -12345i64;
            assert_eq!(const_op_xlen(rsh_const, x, s, 16), wrap(((x as i16) >> s.min(15)) as i64), ">> {s}");
            let shifted = (x as u16).checked_shr(s as u32).unwrap_or(0);
            assert_eq!(const_op_xlen(rshu_const, x, s, 16), wrap(shifted as i64), ">>u {s}");
        }
    }
}

#[test]
fn division_by_small_variables() {
    for x in [0, 1, -1, 7, -7, 12345, -12345, i64::MAX, i64::MIN] {
        for d in [1, 2, 3, 10, 360, 16383] {
            assert_eq!(binop(div_small_assign, x, d), x.wrapping_div(d), "{x} / {d}");
            assert_eq!(binop(rem_small_assign, x, d), x.wrapping_rem(d), "{x} % {d}");
            assert_eq!(binop(divu_small_assign, x, d) as u64, x as u64 / d as u64, "{x} /u {d}");
            assert_eq!(binop(remu_small_assign, x, d) as u64, x as u64 % d as u64, "{x} %u {d}");
        }
    }
}

#[test]
fn comparisons_with_constants_are_exact() {
    for x in [i64::MIN, i64::MIN + 1, -40000, -32768, -5, -1, 0, 1, 5, 32767, 40000, i64::MAX - 1, i64::MAX] {
        for k in [-32768, -32767, -5, -1, 0, 1, 5, 32766, 32767, -40000, 40000, i64::MAX] {
            let unop = |f: ConstOp| {
                let (_, value) = run_with(b"", |o| {
                    set_int(o, R1, x);
                    f(o, R1, k);
                });
                value(R1)
            };
            assert_eq!(unop(lt_const), (x < k) as i64, "{x} < {k}");
            assert_eq!(unop(le_const), (x <= k) as i64, "{x} <= {k}");
            assert_eq!(unop(gt_const), (x > k) as i64, "{x} > {k}");
            assert_eq!(unop(ge_const), (x >= k) as i64, "{x} >= {k}");
        }
    }
}
