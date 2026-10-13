use super::*;
use crate::interp::Machine;

/// `machine`, checking that lowered programs keep lowering's promise that
/// no pointer leads to the registers.
fn guard(machine: Machine) -> Machine {
    Machine { guarded: 0..48, ..machine }
}

/// Runs `module` with the IR interpreter, and lowered with the asm interpreter
/// under both address models, before and after optimizing it, and checks that
/// every run prints `expected`.
fn check(module: &Module, input: &[u8], expected: &str) {
    let mut optimized = module.clone();
    optimize(&mut optimized);
    for (what, m) in [("unoptimized", module), ("optimized", &optimized)] {
        let out = run(m, input, 64).unwrap_or_else(|e| panic!("{what}: {e}\n{m}"));
        assert_eq!(String::from_utf8(out).unwrap(), expected, "{what} IR\n{m}");
        let ops = lower(m).unwrap();
        crate::cpu::assemble(&ops, 64).expect("the CPU backend rejected the program");
        for (model, machine) in [("CPU", Machine::cpu()), ("C", Machine::c())] {
            let out = guard(machine).run(&ops, input).unwrap_or_else(|e| panic!("{what}, {model}: {e}"));
            assert_eq!(String::from_utf8(out.output).unwrap(), expected, "{what}, lowered, {model} addresses\n{m}");
        }
    }
}

/// The lowered program's output on an `xlen`-bit CPU.
fn run_lowered(module: &Module, input: &[u8], xlen: u32) -> String {
    let ops = lower(module).unwrap();
    String::from_utf8(guard(Machine::cpu_xlen(xlen)).run(&ops, input).unwrap().output).unwrap()
}

struct Rng(u64);

impl Rng {
    fn next(&mut self) -> u64 {
        self.0 ^= self.0 << 13;
        self.0 ^= self.0 >> 7;
        self.0 ^= self.0 << 17;
        self.0
    }

    fn below(&mut self, n: usize) -> usize {
        (self.next() % n as u64) as usize
    }

    /// A value from the interesting edges of the cell widths, or a random one.
    fn interesting(&mut self) -> i64 {
        const EDGES: [i64; 16] =
            [0, 1, -1, 2, 7, 15, 16, 63, 64, 100, 32767, 32768, -32768, 65536, i64::MIN, i64::MAX];
        match self.below(3) {
            0 => EDGES[self.below(EDGES.len())],
            1 => self.next() as i64 % 1000,
            _ => self.next() as i64,
        }
    }
}

/// A loop that runs `body` for i = 0, 1, .. while i < n, in a fresh block,
/// leaving the builder in the block after the loop.
fn counted_loop(f: &mut Function, n: Value, body: impl FnOnce(&mut Function, Value)) {
    let head = f.new_block(1);
    let inside = f.new_block(0);
    let after = f.new_block(0);
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

fn fib_module() -> Module {
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
    let n = f.int(16);
    counted_loop(f, n, |f, i| {
        let r = f.call("fib", &[i]);
        f.put_int(r);
        f.puts(" ");
    });
    f.ret_void();
    m
}

#[test]
fn recursion() {
    check(&fib_module(), b"", "0 1 1 2 3 5 8 13 21 34 55 89 144 233 377 610 ");
}

#[test]
fn block_parameters_take_the_place_of_phis() {
    let mut m = Module::new();
    let f = m.main();
    // fibonacci with (a, b) = (b, a + b) passed around the loop
    let head = f.new_block(3);
    let (body, swaps, done) = (f.new_block(0), f.new_block(3), f.new_block(0));
    let (zero, one, two, ten) = (f.int(0), f.int(1), f.int(2), f.int(10));
    f.jump(head, &[zero, zero, one]);
    f.switch_to(head);
    let [i, a, b] = [0, 1, 2].map(|k| f.block_param(head, k));
    let more = f.lt(i, ten);
    f.branch(more, body, &[], swaps, &[zero, one, two]);
    f.switch_to(body);
    f.put_int(a);
    f.puts(",");
    let next = f.add(i, one);
    let sum = f.add(a, b);
    f.jump(head, &[next, b, sum]);

    // a loop that swaps its parameters every time, which needs a cycle of
    // copies broken through a scratch cell
    f.switch_to(swaps);
    let [j, x, y] = [0, 1, 2].map(|k| f.block_param(swaps, k));
    let more = f.lt(j, ten);
    let print = f.new_block(0);
    f.branch(more, print, &[], done, &[]);
    f.switch_to(print);
    f.put_int(x);
    f.put_int(y);
    f.puts(" ");
    let next = f.add(j, one);
    f.jump(swaps, &[next, y, x]);
    f.switch_to(done);
    f.ret_void();
    check(&m, b"", "0,1,1,2,3,5,8,13,21,34,12 21 12 21 12 21 12 21 12 21 ");
}

#[test]
fn nested_loops() {
    let mut m = Module::new();
    let f = m.main();
    let four = f.int(4);
    counted_loop(f, four, |f, i| {
        let one = f.int(1);
        let row = f.add(i, one);
        counted_loop(f, four, |f, j| {
            let col = f.add(j, one);
            let product = f.mul(row, col);
            f.put_int(product);
            f.puts(" ");
        });
        f.puts("\n");
    });
    f.ret_void();
    check(&m, b"", "1 2 3 4 \n2 4 6 8 \n3 6 9 12 \n4 8 12 16 \n");
}

#[test]
fn memory() {
    let mut m = Module::new();
    let f = m.main();
    // squares into a stack array, read back through constant and computed
    // indexes
    let squares = f.alloca(10);
    let ten = f.int(10);
    counted_loop(f, ten, |f, i| {
        let at = f.index(squares, i);
        let square = f.mul(i, i);
        f.store(at, square);
    });
    let seven = f.int(7);
    let at = f.index(squares, seven);
    let x = f.load(at);
    f.put_int(x);
    f.puts(" ");
    let three = f.int(3);
    let at = f.index(squares, three);
    let x = f.load(at);
    f.put_int(x);
    f.puts(" ");

    // numbers from the input into a heap array, printed backwards with their
    // maximum
    let n = f.get_int();
    let numbers = f.heap_alloc(n);
    counted_loop(f, n, |f, i| {
        let x = f.get_int();
        let at = f.index(numbers, i);
        f.store(at, x);
    });
    let head = f.new_block(2);
    let (body, done) = (f.new_block(0), f.new_block(0));
    let low = f.int(-1_000_000);
    f.jump(head, &[n, low]);
    f.switch_to(head);
    let (i, best) = (f.block_param(head, 0), f.block_param(head, 1));
    let zero = f.int(0);
    let more = f.gt(i, zero);
    f.branch(more, body, &[], done, &[]);
    f.switch_to(body);
    let one = f.int(1);
    let prev = f.sub(i, one);
    let at = f.index(numbers, prev);
    let x = f.load(at);
    f.put_int(x);
    f.puts(",");
    let best2 = f.max(best, x);
    f.jump(head, &[prev, best2]);
    f.switch_to(done);
    f.puts(" max ");
    f.put_int(best);
    f.ret_void();
    check(&m, b"5 3 -9 27 4 0", "49 9 0,4,27,-9,3, max 27");
}

#[test]
fn mutual_recursion() {
    let mut m = Module::new();
    for (name, other, at_zero) in [("even", "odd", 1), ("odd", "even", 0)] {
        let f = m.function(name, 1);
        let n = f.param(0);
        let (zero_case, other_case) = (f.new_block(0), f.new_block(0));
        let zero = f.int(0);
        let is_zero = f.eq(n, zero);
        f.branch(is_zero, zero_case, &[], other_case, &[]);
        f.switch_to(zero_case);
        let k = f.int(at_zero);
        f.ret(k);
        f.switch_to(other_case);
        let one = f.int(1);
        let less = f.sub(n, one);
        let r = f.call(other, &[less]);
        f.ret(r);
    }
    let f = m.main();
    let nine = f.int(9);
    counted_loop(f, nine, |f, i| {
        let r = f.call("even", &[i]);
        f.put_int(r);
    });
    f.ret_void();
    check(&m, b"", "101010101");
}

#[test]
fn returning_from_inside_a_loop() {
    let mut m = Module::new();
    let f = m.function("divisor", 1);
    let n = f.param(0);
    let head = f.new_block(1);
    let (found, next) = (f.new_block(0), f.new_block(0));
    let two = f.int(2);
    f.jump(head, &[two]);
    f.switch_to(head);
    let d = f.block_param(head, 0);
    let r = f.rem(n, d);
    let zero = f.int(0);
    let divides = f.eq(r, zero);
    f.branch(divides, found, &[], next, &[]);
    f.switch_to(found);
    f.ret(d);
    f.switch_to(next);
    let one = f.int(1);
    let d2 = f.add(d, one);
    f.jump(head, &[d2]);

    let f = m.main();
    for n in [15, 49, 97, 1000] {
        let n = f.int(n);
        let r = f.call("divisor", &[n]);
        f.put_int(r);
        f.puts(" ");
    }
    f.ret_void();
    check(&m, b"", "3 7 97 2 ");
}

#[test]
fn calls_with_constant_arguments() {
    let mut m = Module::new();
    let f = m.function("digits", 4);
    let ten = f.int(10);
    let mut acc = f.param(0);
    for i in 1..4 {
        let scaled = f.mul(acc, ten);
        let p = f.param(i);
        acc = f.add(scaled, p);
    }
    f.ret(acc);
    let f = m.main();
    let (one, two, three, four) = (f.int(1), f.int(2), f.int(3), f.int(4));
    let r = f.call("digits", &[one, two, three, four]);
    f.put_int(r);
    f.puts(" ");
    let x = f.get_int();
    let r = f.call("digits", &[x, x, four, x]);
    f.put_int(r);
    f.ret_void();
    check(&m, b"9", "1234 9949");
}

#[test]
fn characters_in_and_out() {
    let mut m = Module::new();
    let f = m.main();
    let head = f.new_block(0);
    let (echo, done) = (f.new_block(0), f.new_block(0));
    f.jump(head, &[]);
    f.switch_to(head);
    let c = f.get_char();
    let zero = f.int(0);
    let end = f.lt(c, zero);
    f.branch(end, done, &[], echo, &[]);
    f.switch_to(echo);
    let upper_bit = f.int(32);
    let lower = f.xor(c, upper_bit);
    f.put_char(lower);
    f.jump(head, &[]);
    f.switch_to(done);
    let minus = f.int(-5);
    f.put_uint(minus);
    f.ret_void();
    check(&m, b"Hello", "hELLO18446744073709551611");
}

/// What each op computes on 64-bit cells, written out independently of `fold`.
fn reference(op: BinOp, a: i64, b: i64) -> i64 {
    use BinOp::*;
    let (ua, ub) = (a as u64, b as u64);
    match op {
        Add => a.wrapping_add(b),
        Sub => a.wrapping_sub(b),
        Mul => a.wrapping_mul(b),
        Div => a.checked_div(b).unwrap_or(if b == 0 { -1 } else { a }),
        Rem => a.checked_rem(b).unwrap_or(if b == 0 { a } else { 0 }),
        DivU => ua.checked_div(ub).map_or(-1, |q| q as i64),
        RemU => ua.checked_rem(ub).map_or(a, |r| r as i64),
        And => a & b,
        Or => a | b,
        Xor => a ^ b,
        Shl => match b {
            ..=0 => a,
            1..=63 => a << b,
            _ => 0,
        },
        Shr => if b <= 0 { a } else { a >> b.min(63) },
        ShrU => match b {
            ..=0 => a,
            1..=63 => (ua >> b) as i64,
            _ => 0,
        },
        Eq => (a == b) as i64,
        Ne => (a != b) as i64,
        Lt => (a < b) as i64,
        Le => (a <= b) as i64,
        Gt => (a > b) as i64,
        Ge => (a >= b) as i64,
        LtU => (ua < ub) as i64,
        LeU => (ua <= ub) as i64,
        GtU => (ua > ub) as i64,
        GeU => (ua >= ub) as i64,
        Min => a.min(b),
        Max => a.max(b),
        Index => unreachable!(),
    }
}

#[test]
fn every_operation_matches_rust() {
    let ops: Vec<BinOp> = BinOp::ALL.into_iter().filter(|&op| op != BinOp::Index).collect();
    let mut m = Module::new();
    let f = m.main();
    let (a, b) = (f.get_int(), f.get_int());
    for &op in &ops {
        let r = f.binary(op, a, b);
        f.put_int(r);
        f.puts(" ");
    }
    for op in [UnOp::Neg, UnOp::Not, UnOp::LNot, UnOp::Abs] {
        let r = f.unary(op, a);
        f.put_int(r);
        f.puts(" ");
    }
    f.ret_void();

    let mut rng = Rng(0x2545f4914f6cdd1d);
    for _ in 0..12 {
        let (a, b) = (rng.interesting(), rng.interesting());
        let mut expected: String = ops.iter().map(|&op| format!("{} ", reference(op, a, b))).collect();
        for r in [a.wrapping_neg(), !a, (a == 0) as i64, a.wrapping_abs()] {
            expected += &format!("{r} ");
        }
        check(&m, format!("{a} {b}").as_bytes(), &expected);
        // narrower cells agree between the IR and its lowered program too
        let input = format!("{a} {b}");
        let ir = String::from_utf8(run(&m, input.as_bytes(), 16).unwrap()).unwrap();
        assert_eq!(run_lowered(&m, input.as_bytes(), 16), ir, "16-bit, {a} {b}");
    }
}

/// A random expression over `leaves`.
fn random_expr(f: &mut Function, rng: &mut Rng, leaves: &[Value], depth: usize) -> Value {
    if depth == 0 || rng.below(4) == 0 {
        return leaves[rng.below(leaves.len())];
    }
    if rng.below(5) == 0 {
        let op = [UnOp::Neg, UnOp::Not, UnOp::LNot, UnOp::Abs][rng.below(4)];
        let a = random_expr(f, rng, leaves, depth - 1);
        return f.unary(op, a);
    }
    let op = BinOp::ALL[rng.below(BinOp::ALL.len() - 1)];
    let a = random_expr(f, rng, leaves, depth - 1);
    let b = random_expr(f, rng, leaves, depth - 1);
    f.binary(op, a, b)
}

#[test]
fn folding_means_the_same_on_every_width() {
    let mut rng = Rng(0x9e3779b97f4a7c15);
    for _ in 0..60 {
        let leaves: Vec<i64> = (0..3).map(|_| rng.interesting()).collect();
        let seed = rng.next();
        // the leaves as constants, so the builder folds what it can, or read
        // from the input, so nothing folds
        let build = |constants: bool| {
            let mut m = Module::new();
            let f = m.main();
            let values: Vec<Value> = leaves.iter().map(|&k| if constants { f.int(k) } else { f.get_int() }).collect();
            let e = random_expr(f, &mut Rng(seed), &values, 4);
            f.put_int(e);
            f.ret_void();
            m
        };
        let (folded, unfolded) = (build(true), build(false));
        let input = leaves.iter().map(|k| k.to_string()).collect::<Vec<_>>().join(" ");
        for xlen in [16, 32, 64] {
            let want = run(&unfolded, input.as_bytes(), xlen).unwrap();
            assert_eq!(run(&folded, b"", xlen).unwrap(), want, "{xlen}-bit\n{folded}");
            assert_eq!(run_lowered(&folded, b"", xlen).as_bytes(), want, "{xlen}-bit lowered\n{folded}");
        }
    }
}

#[test]
fn building_shares_and_folds_nodes() {
    let mut m = Module::new();
    let f = m.main();
    let (x, y) = (f.get_int(), f.get_int());
    // the same node twice is one value, whichever way round
    let sum = f.add(x, y);
    assert_eq!(f.add(y, x), sum);
    assert_eq!(f.add(x, y), sum);
    // a constant on the left of a comparison moves to the right
    let k = f.int(5);
    let lt = f.lt(k, x);
    assert_eq!(*f.node(lt), Node::Binary(BinOp::Gt, x, k));
    // identities
    let zero = f.int(0);
    let one = f.int(1);
    assert_eq!(f.sub(x, x), zero);
    assert_eq!(f.mul(x, one), x);
    assert_eq!(f.and(x, zero), zero);
    assert_eq!(f.add(zero, x), x);
    let neg = f.neg(x);
    assert_eq!(f.neg(neg), x);

    // folding, only where every width agrees
    let fold = |f: &mut Function, op: BinOp, a: i64, b: i64| {
        let (a, b) = (f.int(a), f.int(b));
        let r = f.binary(op, a, b);
        f.const_value(r)
    };
    assert_eq!(fold(f, BinOp::Add, 2, 3), Some(5));
    assert_eq!(fold(f, BinOp::Add, i64::MAX, 1), Some(i64::MIN));
    assert_eq!(fold(f, BinOp::Lt, 4, 5), Some(1));
    assert_eq!(fold(f, BinOp::Shl, 1, 70), Some(0));
    // 40000 is negative on 16-bit cells, and 65536 is 0
    assert_eq!(fold(f, BinOp::Lt, 40000, 0), None);
    assert_eq!(fold(f, BinOp::Eq, 65536, 0), None);
    assert_eq!(fold(f, BinOp::Div, -32768, -1), None);
    assert_eq!(fold(f, BinOp::Shl, 1, 1 << 20), None);
}

#[test]
fn unused_values_are_never_computed() {
    let build = |use_it: bool| {
        let mut m = Module::new();
        let f = m.main();
        let (x, y) = (f.get_int(), f.get_int());
        let product = f.mul(x, y);
        if use_it {
            f.put_int(product);
        }
        f.ret_void();
        source(&m)
    };
    assert!(!build(false).contains("@rt_mul"));
    assert!(build(true).contains("@rt_mul"));
}

#[test]
fn values_share_slots_when_they_can() {
    let mut m = Module::new();
    let f = m.main();
    let x = f.get_int();
    for i in 0..40 {
        let k = f.int(i);
        let t = f.add(x, k);
        f.put_int(t);
    }
    f.ret_void();
    // x, one temporary at a time, and the block number
    assert!(lower::frame_size(&m.functions()[0]) <= 3);
}

#[test]
fn verifier_catches_mistakes() {
    let fails = |build: &dyn Fn(&mut Module), message: &str| {
        let mut m = Module::new();
        build(&mut m);
        let err = verify(&m).unwrap_err();
        assert!(err.contains(message), "{err:?} doesn't mention {message:?}");
        assert!(lower(&m).is_err());
    };
    fails(&|m| {
        let f = m.main();
        let (a, b, join) = (f.new_block(0), f.new_block(0), f.new_block(0));
        let c = f.get_int();
        f.branch(c, a, &[], b, &[]);
        f.switch_to(a);
        let x = f.get_int();
        f.jump(join, &[]);
        f.switch_to(b);
        f.jump(join, &[]);
        f.switch_to(join);
        f.put_int(x);
        f.ret_void();
    }, "doesn't dominate");
    fails(&|m| {
        let f = m.main();
        let next = f.new_block(1);
        f.jump(next, &[]);
        f.switch_to(next);
        f.ret_void();
    }, "with 0 arguments, but it takes 1");
    fails(&|m| {
        let f = m.main();
        let next = f.new_block(0);
        f.jump(next, &[]);
    }, "has no terminator");
    fails(&|m| {
        let f = m.main();
        f.call("nope", &[]);
        f.ret_void();
    }, "doesn't exist");
    fails(&|m| {
        m.function("f", 0).ret_void();
        let f = m.main();
        f.call("main", &[]);
        f.ret_void();
    }, "calls main");
    fails(&|m| {
        m.function("way_too_long_a_name", 0).ret_void();
        m.main().ret_void();
    }, "function names");
}

#[test]
fn optimizing_merges_blocks_and_folds_branches() {
    let mut m = Module::new();
    let f = m.main();
    // a chain of blocks passing constants along, and a branch on one
    let (b1, b2, then, els) = (f.new_block(1), f.new_block(1), f.new_block(0), f.new_block(0));
    let three = f.int(3);
    f.jump(b1, &[three]);
    f.switch_to(b1);
    let p = f.block_param(b1, 0);
    let four = f.int(4);
    let sum = f.add(p, four);
    f.jump(b2, &[sum]);
    f.switch_to(b2);
    let q = f.block_param(b2, 0);
    let seven = f.int(7);
    let same = f.eq(q, seven);
    f.branch(same, then, &[], els, &[]);
    f.switch_to(then);
    f.put_int(q);
    f.ret_void();
    f.switch_to(els);
    f.puts("no");
    f.ret_void();

    let mut optimized = m.clone();
    optimize(&mut optimized);
    assert_eq!(optimized.functions()[0].reachable_blocks().len(), 1);
    assert_eq!(optimized.to_string(), "fn main() {\nb0:\n    put_int 7\n    ret\n}\n");
    check(&m, b"", "7");
}

#[test]
fn printing() {
    let m = fib_module();
    let text = m.functions()[1].to_string();
    assert_eq!(
        text,
        "fn fib(v0) {\n\
         b0(v0):\n    v2 = lt v0, 2\n    br v2, b1, b2\n\
         b1:\n    ret v0\n\
         b2:\n    v4 = sub v0, 1\n    v5 = call fib(v4)\n    v6 = sub v0, 2\n    v7 = call fib(v6)\n    v8 = add v5, v7\n    ret v8\n\
         }\n"
    );
}

fn optimized(m: &Module) -> Module {
    let mut m = m.clone();
    optimize(&mut m);
    m
}

/// The ops a module lowers to, before `asm::opt` (which inlines the
/// runtime's routines, so their names would be gone).
fn source(m: &Module) -> String {
    crate::asm::to_source(&lower_with(m, &Options { optimize: false, ..Options::default() }).unwrap())
}

#[test]
fn ranges_fold_values_and_pick_cheap_comparisons() {
    let mut m = Module::new();
    let f = m.main();
    let x = f.get_int();
    let ten = f.int(10);
    let digit = f.rem(x, ten);
    // digit is in -9..=9, so this is always true
    let hundred = f.int(100);
    let small = f.lt(digit, hundred);
    let (yes, no, rest) = (f.new_block(0), f.new_block(0), f.new_block(0));
    f.branch(small, yes, &[], no, &[]);
    f.switch_to(no);
    f.puts("never");
    f.jump(rest, &[]);
    f.switch_to(yes);
    f.jump(rest, &[]);
    f.switch_to(rest);
    // inside `if x == 5`, x is 5
    let five = f.int(5);
    let is_five = f.eq(x, five);
    let (then, after) = (f.new_block(0), f.new_block(0));
    f.branch(is_five, then, &[], after, &[]);
    f.switch_to(then);
    f.put_int(x);
    f.jump(after, &[]);
    f.switch_to(after);
    let n = f.int(5);
    counted_loop(f, n, |f, i| {
        let more = f.gt(i, digit);
        f.put_int(more);
    });
    f.ret_void();

    check(&m, b"5", "500000");
    check(&m, b"-3", "11111");
    let o = optimized(&m);
    let text = o.to_string();
    assert!(!text.contains("never"), "{text}");
    assert!(text.contains("put_int 5"), "{text}");
    // the loop counter and the digit are both small, so no exact comparison
    assert!(!source(&o).contains("@rt_less"));
}

#[test]
fn gvn_and_hoisting() {
    let mut m = Module::new();
    let f = m.main();
    let (a, b) = (f.get_int(), f.get_int());
    let product = f.mul(a, b);
    f.put_int(product);
    let (then, after) = (f.new_block(0), f.new_block(0));
    f.branch(a, then, &[], after, &[]);
    f.switch_to(then);
    // the same product again, in a block the first one dominates
    let again = f.mul(a, b);
    f.put_int(again);
    f.jump(after, &[]);
    f.switch_to(after);
    // a count from the input, so the loop isn't unrolled
    let n = f.get_int();
    let mut invariant = None;
    counted_loop(f, n, |f, i| {
        let sum = f.add(a, b);
        invariant = Some(sum);
        let x = f.add(sum, i);
        f.put_int(x);
    });
    f.ret_void();

    check(&m, b"2 3 3", "66567");
    let o = optimized(&m);
    let text = o.to_string();
    assert_eq!(text.matches(" mul ").count(), 1, "{text}");
    // a + b moved out of the loop, into the block before it
    let main = &o.functions()[0];
    let block = main.block_of(invariant.unwrap()).unwrap();
    assert!(main.terminator(block).is_some_and(|t| matches!(t, Terminator::Jump(_))), "{text}");
}

#[test]
fn parameters_that_always_get_one_value_disappear() {
    let mut m = Module::new();
    let f = m.main();
    let x = f.get_int();
    let head = f.new_block(2);
    let (body, done) = (f.new_block(0), f.new_block(0));
    let zero = f.int(0);
    // a count from the input, so the loop isn't unrolled
    let n = f.get_int();
    f.jump(head, &[zero, x]);
    f.switch_to(head);
    let (i, k) = (f.block_param(head, 0), f.block_param(head, 1));
    let more = f.lt(i, n);
    f.branch(more, body, &[], done, &[]);
    f.switch_to(body);
    f.put_int(k);
    let one = f.int(1);
    let next = f.add(i, one);
    f.jump(head, &[next, k]);
    f.switch_to(done);
    f.ret_void();

    check(&m, b"7 3", "777");
    let text = optimized(&m).to_string();
    // replaced everywhere, and then dropped as unused
    assert!(text.matches(&format!("{k}")).count() <= 1, "{text}");
}

#[test]
fn inlining_and_tail_calls() {
    let mut m = Module::new();
    let f = m.function("mix", 2);
    let (a, b) = (f.param(0), f.param(1));
    let r = f.sub(a, b);
    f.ret(r);
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
    let (x, y) = (f.get_int(), f.get_int());
    let g = f.call("gcd", &[x, y]);
    f.put_int(g);
    let d = f.call("mix", &[x, y]);
    f.put_int(d);
    f.ret_void();

    check(&m, b"84 36", "1248");
    let o = optimized(&m);
    // gcd became a loop, so it could be inlined like mix, and neither is
    // needed on its own any more
    let text = o.functions()[0].to_string();
    assert!(!text.contains("call"), "{text}");
    let source = source(&o);
    assert!(!source.contains("@f_gcd") && !source.contains("@f_mix"));
}

#[test]
fn memory_accesses_are_forwarded_and_dropped() {
    let mut m = Module::new();
    // changes memory behind its argument; recursive, so it isn't inlined
    let f = m.function("poke", 2);
    let (p, n) = (f.param(0), f.param(1));
    let (deeper, store) = (f.new_block(0), f.new_block(0));
    f.branch(n, deeper, &[], store, &[]);
    f.switch_to(deeper);
    let one = f.int(1);
    let less = f.sub(n, one);
    f.call("poke", &[p, less]);
    f.ret_void();
    f.switch_to(store);
    let k = f.int(42);
    f.store(p, k);
    f.ret_void();

    let f = m.main();
    let x = f.get_int();
    // stored and loaded back: the loads become the stored value
    let local = f.alloca(4);
    let zero = f.int(0);
    let at = f.index(local, zero);
    f.store(at, x);
    let a = f.load(at);
    let b = f.load(at);
    let sum = f.add(a, b);
    f.put_int(sum);
    f.puts(" ");
    // a call that can reach the cell means loading it again
    let shared = f.alloca(1);
    f.store(shared, x);
    let two = f.int(2);
    f.call("poke", &[shared, two]);
    let after = f.load(shared);
    f.put_int(after);
    f.ret_void();

    check(&m, b"5", "10 42");
    let text = optimized(&m).functions()[0].to_string();
    assert_eq!(text.matches("load").count(), 1, "{text}");
    // nothing reads `local` any more, so its store goes too
    assert_eq!(text.matches("store").count(), 1, "{text}");
}

#[test]
fn irreducible_control_flow() {
    // a loop between two blocks, entered at either one
    let mut m = Module::new();
    let f = m.main();
    let (a, b, done) = (f.new_block(1), f.new_block(1), f.new_block(0));
    let x = f.get_int();
    let zero = f.int(0);
    f.branch(x, a, &[zero], b, &[zero]);
    for (this, other, letter) in [(a, b, "a"), (b, a, "b")] {
        f.switch_to(this);
        let n = f.block_param(this, 0);
        f.puts(letter);
        let one = f.int(1);
        let next = f.add(n, one);
        let three = f.int(3);
        let more = f.lt(next, three);
        f.branch(more, other, &[next], done, &[]);
    }
    f.switch_to(done);
    f.ret_void();
    check(&m, b"1", "aba");
    check(&m, b"0", "bab");
}

#[test]
fn range_based_helpers_match_on_every_width() {
    let ops = [
        BinOp::Add,
        BinOp::Sub,
        BinOp::Mul,
        BinOp::Div,
        BinOp::Rem,
        BinOp::Lt,
        BinOp::Le,
        BinOp::Gt,
        BinOp::Ge,
        BinOp::Eq,
        BinOp::Min,
        BinOp::Max,
    ];
    let mut rng = Rng(0x853c49e6748fea9b);
    for _ in 0..40 {
        // values bounded by a remainder or a mask, so their ranges are known
        let bounds: Vec<i64> = (0..3).map(|_| [3, 33, 100, 1000, 20000, 40000][rng.below(6)]).collect();
        let seed = rng.next();
        let mut m = Module::new();
        let f = m.main();
        let mut leaves = vec![];
        for (i, &k) in bounds.iter().enumerate() {
            let x = f.get_int();
            let k = f.int(k);
            leaves.push(if i == 2 { f.and(x, k) } else { f.rem(x, k) });
        }
        let mut r = Rng(seed);
        for _ in 0..4 {
            let (a, b) = (leaves[r.below(3)], leaves[r.below(3)]);
            let op = ops[r.below(ops.len())];
            let v = f.binary(op, a, b);
            let w = f.binary(ops[r.below(ops.len())], v, leaves[r.below(3)]);
            f.put_int(w);
            f.puts(" ");
        }
        f.ret_void();
        let input: String = (0..3).map(|_| format!("{} ", rng.interesting())).collect();
        for m in [&m, &optimized(&m)] {
            for xlen in [16, 64] {
                let want = String::from_utf8(run(m, input.as_bytes(), xlen).unwrap()).unwrap();
                assert_eq!(run_lowered(m, input.as_bytes(), xlen), want, "{xlen}-bit, input {input}\n{m}");
            }
        }
    }
}

#[test]
fn stores_through_computed_addresses_can_alias() {
    let mut m = Module::new();
    let f = m.main();
    let cells = f.alloca(4);
    let (i, j) = (f.get_int(), f.get_int());
    let (at_i, at_j) = (f.index(cells, i), f.index(cells, j));
    let (one, two) = (f.int(1), f.int(2));
    f.store(at_i, one);
    // the same cell when i == j, so this load has to see the second store
    f.store(at_j, two);
    let x = f.load(at_i);
    f.put_int(x);
    f.ret_void();
    check(&m, b"1 1", "2");
    check(&m, b"1 2", "1");
}

#[test]
fn values_computed_from_an_inlined_result() {
    let mut m = Module::new();
    // two returns, so what follows the inlined call can't merge back into
    // the block before it
    let f = m.function("twice", 1);
    let x = f.param(0);
    let (negative, positive) = (f.new_block(0), f.new_block(0));
    let zero = f.int(0);
    let below = f.lt(x, zero);
    f.branch(below, negative, &[], positive, &[]);
    f.switch_to(negative);
    let r = f.sub(x, x);
    let r = f.sub(r, x);
    f.ret(r);
    f.switch_to(positive);
    let r = f.add(x, x);
    f.ret(r);
    let f = m.main();
    let x = f.get_int();
    let r = f.call("twice", &[x]);
    // pure nodes after the call that use its result
    let one = f.int(1);
    let y = f.add(r, one);
    let z = f.mul(y, x);
    f.put_int(z);
    f.ret_void();
    check(&m, b"5", "55");
    check(&m, b"-2", "-6");
    assert!(!source(&optimized(&m)).contains("@f_twice"));
}

#[test]
fn cheap_comparisons_only_where_they_cant_overflow() {
    // a and b are each within ±19999, so a - b can need 17 bits
    let mut m = Module::new();
    let f = m.main();
    let k = f.int(20000);
    let (x, y) = (f.get_int(), f.get_int());
    let (a, b) = (f.rem(x, k), f.rem(y, k));
    for op in [BinOp::Lt, BinOp::Le, BinOp::Gt, BinOp::Ge] {
        let r = f.binary(op, a, b);
        f.put_int(r);
    }
    f.ret_void();
    for input in [&b"19999 -19999"[..], b"-19999 19999", b"5 5"] {
        let want = String::from_utf8(run(&m, input, 16).unwrap()).unwrap();
        assert_eq!(run_lowered(&m, input, 16), want, "{}", String::from_utf8_lossy(input));
    }
}

#[test]
fn hoisting_from_blocks_that_run_on_some_iterations() {
    let mut m = Module::new();
    let f = m.main();
    let (a, b) = (f.get_int(), f.get_int());
    let n = f.int(6);
    let mut invariant = None;
    counted_loop(f, n, |f, i| {
        let one = f.int(1);
        let odd = f.and(i, one);
        let (then, after) = (f.new_block(0), f.new_block(0));
        f.branch(odd, then, &[], after, &[]);
        f.switch_to(then);
        // only runs on odd iterations, but doesn't change
        let product = f.mul(a, b);
        invariant = Some(product);
        f.put_int(product);
        f.jump(after, &[]);
        f.switch_to(after);
    });
    f.ret_void();
    check(&m, b"6 7", "424242");
    let o = optimized(&m);
    let main = &o.functions()[0];
    let block = main.block_of(invariant.unwrap()).unwrap();
    assert!(matches!(main.terminator(block), Some(Terminator::Jump(_))), "{o}");
}

#[test]
fn memory_facts_flow_through_merges_and_loops() {
    let mut m = Module::new();
    let f = m.main();
    let (x, c) = (f.get_int(), f.get_int());
    let cell = f.alloca(1);
    let other = f.alloca(1);
    let (then, els, join) = (f.new_block(0), f.new_block(0), f.new_block(0));
    f.store(other, x);
    f.branch(c, then, &[], els, &[]);
    // both ways store the same value in `cell`, and different ones in `other`
    f.switch_to(then);
    f.store(cell, x);
    let one = f.int(1);
    f.store(other, one);
    f.jump(join, &[]);
    f.switch_to(els);
    f.store(cell, x);
    f.jump(join, &[]);
    f.switch_to(join);
    let a = f.load(cell);
    let b = f.load(other);
    f.put_int(a);
    f.puts(" ");
    f.put_int(b);
    f.puts(" ");
    // a loop that only reads `cell`, and one that adds to `other` each time
    let three = f.int(3);
    counted_loop(f, three, |f, i| {
        let v = f.load(cell);
        f.put_int(v);
        let total = f.load(other);
        let more = f.add(total, i);
        f.store(other, more);
    });
    let total = f.load(other);
    f.puts(" ");
    f.put_int(total);
    f.ret_void();

    check(&m, b"5 1", "5 1 555 4");
    check(&m, b"5 0", "5 5 555 8");
    let text = optimized(&m).to_string();
    assert_eq!(text.matches("load").count(), 0, "{text}");
}

#[test]
fn a_wider_minimum_width_proves_more() {
    let build = |m: &mut Module| {
        let f = m.main();
        let x = f.get_int();
        let k = f.int(100_000);
        let a = f.rem(x, k);
        let y = f.get_int();
        let b = f.rem(y, k);
        let lt = f.lt(a, b);
        f.put_int(lt);
        // folds only when 40000 can't be negative
        let big = f.int(40_000);
        let zero = f.int(0);
        let positive = f.gt(big, zero);
        f.put_int(positive);
        f.ret_void();
    };
    let (mut narrow, mut wide) = (Module::new(), Module::with_min_width(32));
    build(&mut narrow);
    build(&mut wide);
    for input in [&b"99999 -99999"[..], b"-5 7"] {
        for xlen in [32, 64] {
            let want = String::from_utf8(run(&wide, input, xlen).unwrap()).unwrap();
            assert_eq!(run_lowered(&wide, input, xlen), want);
            assert_eq!(run_lowered(&optimized(&wide), input, xlen), want);
        }
    }
    assert!(run(&wide, b"1 2", 16).is_err());
    assert!(source(&narrow).contains("@rt_less"));
    assert!(!source(&wide).contains("@rt_less"));
    assert!(optimized(&wide).to_string().contains("put_int 1"));
}

#[test]
fn constant_operands_match_on_every_width() {
    let ops = [
        BinOp::And,
        BinOp::Or,
        BinOp::Xor,
        BinOp::Div,
        BinOp::Rem,
        BinOp::DivU,
        BinOp::RemU,
        BinOp::Shl,
        BinOp::Shr,
        BinOp::ShrU,
    ];
    let constants = [1, 2, 3, 7, 8, 10, 255, 1000, 16384, 32767, -1, -8, -255, 1 << 20, 64, 15];
    let mut m = Module::new();
    let f = m.main();
    let x = f.get_int();
    for op in ops {
        for k in constants {
            let k = f.int(k);
            let r = f.binary(op, x, k);
            f.put_int(r);
            f.puts(" ");
        }
    }
    f.ret_void();
    let mut rng = Rng(0xda942042e4dd58b5);
    for _ in 0..6 {
        let input = rng.interesting().to_string();
        for xlen in [16, 64] {
            let want = String::from_utf8(run(&m, input.as_bytes(), xlen).unwrap()).unwrap();
            assert_eq!(run_lowered(&m, input.as_bytes(), xlen), want, "{xlen}-bit, {input}");
        }
    }
}

#[test]
fn division_and_masks_by_constants_use_the_quick_routines() {
    let mut m = Module::new();
    let f = m.main();
    let n = f.get_int();
    let (one, two, ten) = (f.int(1), f.int(2), f.int(10));
    let odd = f.and(n, one);
    let half = f.div(n, two);
    let digit = f.rem(n, ten);
    for v in [odd, half, digit] {
        f.put_int(v);
        f.puts(" ");
    }
    f.ret_void();
    check(&m, b"-37", "1 -18 -7 ");
    let source = source(&m);
    assert!(source.contains("@rt_lowbits") && source.contains("@rt_divuk"));
    assert!(!source.contains("@rt_and") && !source.contains("@rt_divs"));
}

#[test]
fn recursion_keeps_what_calls_could_overwrite_in_frames() {
    // sum of a recursive walk with a loop around the call, an alloca per call,
    // and a value used after the call
    let mut m = Module::new();
    let f = m.function("walk", 1);
    let n = f.param(0);
    let cell = f.alloca(1);
    f.store(cell, n);
    let (base, recurse) = (f.new_block(0), f.new_block(0));
    let zero = f.int(0);
    let done = f.le(n, zero);
    f.branch(done, base, &[], recurse, &[]);
    f.switch_to(base);
    f.ret(zero);
    f.switch_to(recurse);
    let two = f.int(2);
    let head = f.new_block(2);
    let (body, after) = (f.new_block(0), f.new_block(0));
    f.jump(head, &[zero, zero]);
    f.switch_to(head);
    let (i, total) = (f.block_param(head, 0), f.block_param(head, 1));
    let more = f.lt(i, two);
    f.branch(more, body, &[], after, &[]);
    f.switch_to(body);
    let one = f.int(1);
    let less = f.sub(n, one);
    let r = f.call("walk", &[less]);
    let mine = f.load(cell);
    let both = f.add(r, mine);
    let total2 = f.add(total, both);
    let i2 = f.add(i, one);
    f.jump(head, &[i2, total2]);
    f.switch_to(after);
    f.ret(total);
    let f = m.main();
    let x = f.get_int();
    let r = f.call("walk", &[x]);
    f.put_int(r);
    f.ret_void();
    // walk(n) = 2 * (walk(n - 1) + n)
    check(&m, b"3", "22");
    check(&m, b"0", "0");
}

#[test]
fn division_by_a_small_variable_and_comparing_with_constants() {
    let mut m = Module::new();
    let f = m.main();
    let (x, y) = (f.get_int(), f.get_int());
    let k = f.int(100);
    let d = f.rem(y, k);
    let (then, after) = (f.new_block(0), f.new_block(0));
    let zero = f.int(0);
    let positive = f.gt(d, zero);
    f.branch(positive, then, &[], after, &[]);
    f.switch_to(then);
    // d is from 1 to 99 here, and x can be anything
    let q = f.div(x, d);
    let r = f.rem(x, d);
    f.put_int(q);
    f.puts(" ");
    f.put_int(r);
    f.puts(" ");
    let five = f.int(5);
    let small = f.lt(x, five);
    f.put_int(small);
    f.jump(after, &[]);
    f.switch_to(after);
    f.ret_void();
    check(&m, b"-1000 7", "-142 -6 1");
    check(&m, b"9223372036854775807 99", "93165374109644200 7 0");
    let source = source(&optimized(&m));
    assert!(source.contains("@rt_divuk"));
    assert!(!source.contains("@rt_divs") && !source.contains("@rt_less"));
}

#[test]
fn unused_parameters_and_results_go() {
    let mut m = Module::new();
    // big enough not to be inlined, and called twice
    let f = m.function("noisy", 2);
    let (a, _unused) = (f.param(0), f.param(1));
    for _ in 0..12 {
        f.put_int(a);
    }
    f.ret(a);
    let f = m.main();
    let x = f.get_int();
    f.call("noisy", &[x, x]);
    f.call("noisy", &[x, x]);
    f.ret_void();
    check(&m, b"3", &"3".repeat(24));
    let o = optimized(&m);
    let noisy = o.get("noisy").unwrap();
    assert_eq!(noisy.param_count(), 1);
    assert!(!noisy.to_string().contains("ret v"), "{noisy}");
}

#[test]
fn functions_specialized_for_constant_arguments() {
    let mut m = Module::new();
    let f = m.function("scale", 2);
    // big enough not to be inlined
    let (x, k) = (f.param(0), f.param(1));
    let mut r = f.mul(x, k);
    for _ in 0..20 {
        r = f.add(r, x);
        f.put_int(r);
    }
    f.ret(r);
    let f = m.main();
    let x = f.get_int();
    let (three, nine) = (f.int(3), f.int(9));
    for k in [three, nine, three, nine] {
        let r = f.call("scale", &[x, k]);
        f.put_int(r);
        f.puts(" ");
    }
    f.ret_void();
    let input = b"2";
    let want = String::from_utf8(run(&m, input, 64).unwrap()).unwrap();
    check(&m, input, &want);
    let o = optimized(&m);
    let copies: Vec<&Function> = o.functions().iter().filter(|f| f.name().starts_with("scale_")).collect();
    assert_eq!(copies.len(), 2);
    assert!(copies.iter().all(|f| f.param_count() == 1));
}

#[test]
fn calls_to_pure_functions() {
    let mut m = Module::new();
    // big enough not to be inlined
    let f = m.function("square", 1);
    let x = f.param(0);
    let mut r = f.mul(x, x);
    for _ in 0..40 {
        r = f.add(r, x);
    }
    f.ret(r);
    let f = m.main();
    let x = f.get_int();
    let a = f.call("square", &[x]);
    let b = f.call("square", &[x]);
    f.call("square", &[a]);
    let s = f.add(a, b);
    f.put_int(s);
    f.ret_void();
    check(&m, b"3", "258");
    // the repeated call reuses the first, the unused one goes, and then
    // square is called once, so it's inlined: its body appears once
    let text = optimized(&m).functions()[0].to_string();
    assert_eq!(text.matches("mul").count(), 1, "{text}");
}

#[test]
fn stores_overwritten_on_every_path_go() {
    let mut m = Module::new();
    let f = m.main();
    let (x, c) = (f.get_int(), f.get_int());
    let cell = f.alloca(1);
    let zero = f.int(0);
    f.store(cell, zero);
    let (a, b, join) = (f.new_block(0), f.new_block(0), f.new_block(0));
    f.branch(c, a, &[], b, &[]);
    for (block, add) in [(a, 1), (b, 2)] {
        f.switch_to(block);
        let k = f.int(add);
        let v = f.add(x, k);
        f.store(cell, v);
        f.put_int(v);
        f.jump(join, &[]);
    }
    f.switch_to(join);
    let v = f.load(cell);
    let p = f.get_int();
    let at = f.index(cell, p);
    let w = f.load(at);
    let s = f.add(v, w);
    f.put_int(s);
    f.ret_void();
    check(&m, b"5 1 0", "612");
    check(&m, b"5 0 0", "714");
    let text = optimized(&m).functions()[0].to_string();
    assert!(!text.contains("store v3, 0"), "{text}");
}

#[test]
fn loads_hoisted_out_of_loops() {
    let mut m = Module::new();
    let f = m.main();
    let (x, p) = (f.get_int(), f.get_int());
    let cells = f.alloca(4);
    let zero = f.int(0);
    let one = f.int(1);
    let first = f.index(cells, zero);
    let second = f.index(cells, one);
    f.store(second, zero);
    // a store through a computed index, so nothing's known about `first`
    let at = f.index(cells, p);
    f.store(at, x);
    let n = f.get_int();
    let mut hoisted = None;
    counted_loop(f, n, |f, i| {
        // first never changes in the loop; second does
        let a = f.load(first);
        hoisted = Some(a);
        let b = f.load(second);
        let s = f.add(a, b);
        f.store(second, s);
        f.put_int(i);
    });
    let b = f.load(second);
    f.put_int(b);
    f.ret_void();
    check(&m, b"3 0 4", "012312");
    check(&m, b"3 1 2", "013");
    let o = optimized(&m);
    let main = &o.functions()[0];
    let block = main.block_of(hoisted.unwrap()).unwrap();
    assert!(matches!(main.terminator(block), Some(Terminator::Jump(_))), "{o}");
}

#[test]
fn induction_variables_and_unrolling() {
    let mut m = Module::new();
    let f = m.main();
    let table = f.alloca(40);
    let n = f.get_int();
    counted_loop(f, n, |f, i| {
        let five = f.int(5);
        let j = f.mul(i, five);
        let at = f.index(table, i);
        f.store(at, j);
    });
    let four = f.int(4);
    counted_loop(f, four, |f, i| {
        let at = f.index(table, i);
        let v = f.load(at);
        f.put_int(v);
        f.puts(",");
    });
    f.ret_void();
    check(&m, b"8", "0,5,10,15,");
    let text = optimized(&m).to_string();
    // the multiply and the variable index became steps, and the second loop
    // is unrolled into straight-line code
    assert!(!text.contains("mul"), "{text}");
    assert_eq!(text.matches(" lt ").count() + text.matches(" gt ").count(), 1, "{text}");
}

#[test]
fn identical_tails_merge() {
    let mut m = Module::new();
    let f = m.main();
    let x = f.get_int();
    let (a, b, c, join) = (f.new_block(0), f.new_block(0), f.new_block(0), f.new_block(0));
    let one = f.int(1);
    let is_one = f.eq(x, one);
    f.branch(is_one, a, &[], c, &[]);
    f.switch_to(c);
    let two = f.int(2);
    let is_two = f.eq(x, two);
    f.branch(is_two, b, &[], join, &[]);
    for block in [a, b] {
        f.switch_to(block);
        f.puts("small ");
        f.put_int(x);
        f.jump(join, &[]);
    }
    f.switch_to(join);
    f.puts("!");
    f.ret_void();
    check(&m, b"2", "small 2!");
    check(&m, b"7", "!");
    let text = optimized(&m).to_string();
    assert_eq!(text.matches("small").count(), 1, "{text}");
}

#[test]
fn calls_that_cant_write_memory_keep_what_is_known() {
    let mut m = Module::new();
    // only reads its argument, and prints
    let f = m.function("show", 1);
    let p = f.param(0);
    let v = f.load(p);
    for _ in 0..10 {
        f.put_int(v);
    }
    f.ret_void();
    let f = m.main();
    let x = f.get_int();
    let cell = f.alloca(1);
    f.store(cell, x);
    f.call("show", &[cell]);
    f.call("show", &[cell]);
    let again = f.load(cell);
    f.put_int(again);
    f.ret_void();
    check(&m, b"4", &"4".repeat(21));
    let text = optimized(&m).functions()[0].to_string();
    assert!(!text.contains("load"), "{text}");
}

/// A closure record: the function's address, then one captured value.
fn closure(f: &mut Function, name: &str, captured: Value) -> Value {
    let two = f.int(2);
    let record = f.heap_alloc(two);
    let code = f.func_addr(name);
    f.store(record, code);
    let one = f.int(1);
    let slot = f.index(record, one);
    f.store(slot, captured);
    record
}

fn closures_module() -> Module {
    let mut m = Module::new();
    // add_k(env, x) = env.k + x, and times_k(env, x) = env.k * x
    for (name, op) in [("add_k", BinOp::Add), ("times_k", BinOp::Mul)] {
        let f = m.function(name, 2);
        let (env, x) = (f.param(0), f.param(1));
        let one = f.int(1);
        let slot = f.index(env, one);
        let k = f.load(slot);
        let r = f.binary(op, k, x);
        f.ret(r);
    }
    // apply(c, x) calls closure c on x, whatever it is
    let f = m.function("apply", 2);
    let (c, x) = (f.param(0), f.param(1));
    let code = f.load(c);
    let r = f.call_indirect(code, &[c, x]);
    f.ret(r);
    // a recursive function that's also called indirectly
    let f = m.function("countdown", 2);
    let (_env, n) = (f.param(0), f.param(1));
    let (done, more) = (f.new_block(0), f.new_block(0));
    let zero = f.int(0);
    let finished = f.le(n, zero);
    f.branch(finished, done, &[], more, &[]);
    f.switch_to(done);
    f.ret(zero);
    f.switch_to(more);
    f.put_int(n);
    let one = f.int(1);
    let less = f.sub(n, one);
    let self_addr = f.func_addr("countdown");
    let r = f.call_indirect(self_addr, &[zero, less]);
    let r = f.add(r, n);
    f.ret(r);

    let f = m.main();
    let x = f.get_int();
    let ten = f.int(10);
    let adder = closure(f, "add_k", ten);
    // called directly on a closure built here, so it can be devirtualized
    let code = f.load(adder);
    let r = f.call_indirect(code, &[adder, x]);
    f.put_int(r);
    f.puts(" ");
    let three = f.int(3);
    let tripler = closure(f, "times_k", three);
    for c in [adder, tripler] {
        let r = f.call("apply", &[c, x]);
        f.put_int(r);
        f.puts(" ");
    }
    let five = f.int(5);
    let zero = f.int(0);
    let code = f.func_addr("countdown");
    let r = f.call_indirect(code, &[zero, five]);
    f.puts(" ");
    f.put_int(r);
    f.ret_void();
    m
}

#[test]
fn indirect_calls_and_closures() {
    let m = closures_module();
    check(&m, b"4", "14 14 12 54321 15");
    // the closure called where it was built became a direct call
    let o = optimized(&m);
    let main = o.functions()[0].to_string();
    assert!(main.matches("call *").count() < m.functions()[0].to_string().matches("call *").count(), "{main}");
}

/// The lowered program's output on every machine, before and after
/// optimizing, which must all agree.
fn lowered_everywhere(module: &Module, input: &[u8]) -> String {
    let mut optimized = module.clone();
    optimize(&mut optimized);
    let mut outputs = vec![];
    for (what, m) in [("unoptimized", module), ("optimized", &optimized)] {
        let ops = lower(m).unwrap_or_else(|e| panic!("{what}: {e}"));
        for (model, machine) in [("CPU", Machine::cpu()), ("C", Machine::c()), ("16-bit CPU", Machine::cpu_xlen(16))] {
            let out = guard(machine).run(&ops, input).unwrap_or_else(|e| panic!("{what}, {model}: {e}"));
            outputs.push((format!("{what}, {model}"), String::from_utf8(out.output).unwrap()));
        }
    }
    for (what, out) in &outputs {
        assert_eq!(out, &outputs[0].1, "{what} differs from {}", outputs[0].0);
    }
    outputs.remove(0).1
}

/// cons(x, xs) = a cell pair from the garbage collector; build(n) = the list
/// n-1, ..., 0; sum(xs) adds a list up.
fn list_functions(m: &mut Module) {
    let f = m.function("cons", 2);
    let (x, xs) = (f.param(0), f.param(1));
    let two = f.int(2);
    let p = f.gc_alloc(two);
    f.store(p, x);
    let one = f.int(1);
    let next = f.index(p, one);
    f.store(next, xs);
    f.ret(p);

    let f = m.function("build", 1);
    let n = f.param(0);
    let head = f.new_block(2);
    let (more, done) = (f.new_block(0), f.new_block(0));
    let zero = f.int(0);
    f.jump(head, &[zero, zero]);
    f.switch_to(head);
    let (i, xs) = (f.block_param(head, 0), f.block_param(head, 1));
    let go = f.lt(i, n);
    f.branch(go, more, &[], done, &[]);
    f.switch_to(more);
    let ys = f.call("cons", &[i, xs]);
    let one = f.int(1);
    let next = f.add(i, one);
    f.jump(head, &[next, ys]);
    f.switch_to(done);
    f.ret(xs);

    let f = m.function("sum", 1);
    let xs = f.param(0);
    let head = f.new_block(2);
    let (more, done) = (f.new_block(0), f.new_block(0));
    let zero = f.int(0);
    f.jump(head, &[xs, zero]);
    f.switch_to(head);
    let (xs, total) = (f.block_param(head, 0), f.block_param(head, 1));
    let go = f.ne(xs, zero);
    f.branch(go, more, &[], done, &[]);
    f.switch_to(more);
    let x = f.load(xs);
    let added = f.add(total, x);
    let one = f.int(1);
    let next = f.index(xs, one);
    let next = f.load(next);
    f.jump(head, &[next, added]);
    f.switch_to(done);
    f.ret(total);
}

#[test]
fn the_garbage_collector_frees_what_nothing_points_to() {
    // 150 lists of 20 pairs need far more than the tape's 4096 cells, so
    // they only fit if the ones that are done with are freed, and the list
    // kept all along must survive every collection intact
    let mut m = Module::new();
    list_functions(&mut m);
    let f = m.main();
    let n = f.get_int();
    let keep = f.call("build", &[n]);
    let rounds = f.int(150);
    let head = f.new_block(2);
    let (more, done) = (f.new_block(0), f.new_block(0));
    let zero = f.int(0);
    f.jump(head, &[zero, zero]);
    f.switch_to(head);
    let (r, total) = (f.block_param(head, 0), f.block_param(head, 1));
    let go = f.lt(r, rounds);
    f.branch(go, more, &[], done, &[]);
    f.switch_to(more);
    let twenty = f.int(20);
    let tmp = f.call("build", &[twenty]);
    let s = f.call("sum", &[tmp]);
    let added = f.add(total, s);
    let one = f.int(1);
    let next = f.add(r, one);
    f.jump(head, &[next, added]);
    f.switch_to(done);
    f.put_int(total);
    f.puts(" ");
    let s = f.call("sum", &[keep]);
    f.put_int(s);
    f.ret_void();
    check(&m, b"50", "28500 1225");
}

#[test]
fn large_objects_and_rescanning_after_the_mark_stack_overflows() {
    // a 400-cell object pointing to 400 small ones: scanning it pushes more
    // than the free cells above the stack can hold, so the collector has to
    // rescan; and 60 large objects that are done with have to be freed
    let mut m = Module::new();
    list_functions(&mut m);
    let f = m.main();
    let n = f.int(400);
    let big = f.gc_alloc(n);
    // each points to another holding the value, so an object whose scan the
    // overflow dropped loses what it points to, unless it's rescanned
    counted_loop(f, n, |f, i| {
        let one = f.int(1);
        let holder = f.gc_alloc(one);
        let k = f.int(200);
        let x = f.sub(i, k);
        f.store(holder, x);
        let small = f.gc_alloc(one);
        f.store(small, holder);
        let at = f.index(big, i);
        f.store(at, small);
    });
    let rounds = f.int(60);
    counted_loop(f, rounds, |f, i| {
        let size = f.int(30);
        let junk = f.gc_alloc(size);
        let last = f.int(29);
        let at = f.index(junk, last);
        f.store(at, i);
        // and garbage the size of the holders, which reuses any freed by
        // mistake
        let ten = f.int(10);
        counted_loop(f, ten, |f, _| {
            let one = f.int(1);
            let g = f.gc_alloc(one);
            let x = f.int(9999);
            f.store(g, x);
        });
    });
    let zero = f.int(0);
    let head = f.new_block(2);
    let (more, done) = (f.new_block(0), f.new_block(0));
    f.jump(head, &[zero, zero]);
    f.switch_to(head);
    let (i, total) = (f.block_param(head, 0), f.block_param(head, 1));
    let go = f.lt(i, n);
    f.branch(go, more, &[], done, &[]);
    f.switch_to(more);
    let at = f.index(big, i);
    let small = f.load(at);
    let holder = f.load(small);
    let x = f.load(holder);
    let added = f.add(total, x);
    let one = f.int(1);
    let next = f.add(i, one);
    f.jump(head, &[next, added]);
    f.switch_to(done);
    f.put_int(total);
    f.ret_void();
    // the IR interpreter never frees, so it can't run out; the lowered
    // program has to collect
    assert_eq!(lowered_everywhere(&m, b""), "-200");
    assert_eq!(String::from_utf8(run(&m, b"", 64).unwrap()).unwrap(), "-200");
}

#[test]
fn running_out_of_memory_stops_the_program() {
    // a list too long for the tape, all of it live until it's summed
    let mut m = Module::new();
    list_functions(&mut m);
    let f = m.main();
    f.puts("start\n");
    let n = f.get_int();
    let xs = f.call("build", &[n]);
    let s = f.call("sum", &[xs]);
    f.put_int(s);
    f.ret_void();
    assert_eq!(lowered_everywhere(&m, b"100"), "start\n4950");
    assert_eq!(lowered_everywhere(&m, b"30000"), "start\nout of memory\n");
}

#[test]
fn abort_stops_the_program_from_inside_calls() {
    let mut m = Module::new();
    // down(n) aborts at the bottom, and prints on the way back up, which
    // never happens
    let f = m.function("down", 1);
    let n = f.param(0);
    let (bottom, deeper) = (f.new_block(0), f.new_block(0));
    let zero = f.int(0);
    let at_bottom = f.eq(n, zero);
    f.branch(at_bottom, bottom, &[], deeper, &[]);
    f.switch_to(bottom);
    f.puts("bye");
    f.abort();
    f.ret(zero);
    f.switch_to(deeper);
    let one = f.int(1);
    let less = f.sub(n, one);
    let r = f.call("down", &[less]);
    f.put_int(n);
    f.ret(r);
    let f = m.main();
    f.puts("a ");
    let n = f.get_int();
    f.call("down", &[n]);
    f.puts("b");
    f.ret_void();
    check(&m, b"5", "a bye");
}

#[test]
fn stack_overflow_stops_the_program() {
    // depth(n) = 1 + depth(n - 1) can't become a loop, so every level needs
    // a stack frame
    let mut m = Module::new();
    let f = m.function("depth", 1);
    let n = f.param(0);
    let (bottom, deeper) = (f.new_block(0), f.new_block(0));
    let zero = f.int(0);
    let at_bottom = f.le(n, zero);
    f.branch(at_bottom, bottom, &[], deeper, &[]);
    f.switch_to(bottom);
    f.ret(zero);
    f.switch_to(deeper);
    let one = f.int(1);
    let less = f.sub(n, one);
    let r = f.call("depth", &[less]);
    let r = f.add(r, one);
    f.put_int(n);
    f.puts(" ");
    f.ret(r);
    let f = m.main();
    let n = f.get_int();
    let r = f.call("depth", &[n]);
    f.puts("= ");
    f.put_int(r);
    f.ret_void();
    assert_eq!(lowered_everywhere(&m, b"3"), "1 2 3 = 3");
    assert_eq!(lowered_everywhere(&m, b"30000"), "stack overflow\n");
    // without checks, the stack runs over the heap and the tape
    let ops = lower_with(&m, &Options { checks: false, ..Options::default() }).unwrap();
    assert!(Machine::cpu().run(&ops, b"30000").map_or(true, |h| !String::from_utf8_lossy(&h.output).contains("overflow")));
}



#[test]
fn reused_memory_is_zeroed() {
    // fill objects with 7s and drop them, thousands of times, so their
    // cells are reused; every object must still start out all 0
    let mut m = Module::new();
    let f = m.main();
    let n = f.int(3000);
    let head = f.new_block(2);
    let (more, done) = (f.new_block(0), f.new_block(0));
    let zero = f.int(0);
    f.jump(head, &[zero, zero]);
    f.switch_to(head);
    let (i, dirty) = (f.block_param(head, 0), f.block_param(head, 1));
    let go = f.lt(i, n);
    f.branch(go, more, &[], done, &[]);
    f.switch_to(more);
    let three = f.int(3);
    let p = f.gc_alloc(three);
    let mut sum = zero;
    for k in 0..3 {
        let k = f.int(k);
        let at = f.index(p, k);
        let x = f.load(at);
        sum = f.add(sum, x);
        let seven = f.int(7);
        f.store(at, seven);
    }
    let nonzero = f.ne(sum, zero);
    let counted = f.add(dirty, nonzero);
    let one = f.int(1);
    let next = f.add(i, one);
    f.jump(head, &[next, counted]);
    f.switch_to(done);
    f.put_int(dirty);
    f.ret_void();
    assert_eq!(lowered_everywhere(&m, b""), "0");
}

#[test]
fn dead_objects_next_to_live_ones_are_reused() {
    // every 20th object is kept, in a list, so every chunk holds something
    // live, and the dead objects around them have to be reused one by one
    let mut m = Module::new();
    list_functions(&mut m);
    let f = m.main();
    let n = f.int(3000);
    let head = f.new_block(2);
    let (more, keep, next_block, done) = (f.new_block(0), f.new_block(0), f.new_block(1), f.new_block(0));
    let zero = f.int(0);
    f.jump(head, &[zero, zero]);
    f.switch_to(head);
    let (i, kept) = (f.block_param(head, 0), f.block_param(head, 1));
    let go = f.lt(i, n);
    f.branch(go, more, &[], done, &[]);
    f.switch_to(more);
    let two = f.int(2);
    let junk = f.gc_alloc(two);
    f.store(junk, i);
    let twenty = f.int(20);
    let r = f.rem(i, twenty);
    let is_kept = f.eq(r, zero);
    f.branch(is_kept, keep, &[], next_block, &[kept]);
    f.switch_to(keep);
    let x = f.div(i, twenty);
    let longer = f.call("cons", &[x, kept]);
    f.jump(next_block, &[longer]);
    f.switch_to(next_block);
    let kept_now = f.block_param(next_block, 0);
    let one = f.int(1);
    let after = f.add(i, one);
    f.jump(head, &[after, kept_now]);
    f.switch_to(done);
    let s = f.call("sum", &[kept]);
    f.put_int(s);
    f.ret_void();
    assert_eq!(lowered_everywhere(&m, b""), "11175");
}



/// Compiles LLVM IR natively and runs it, if LLVM's `clang` is installed.
fn run_native(ll: &str, input: &[u8], name: &str) -> Option<String> {
    let clang = ["/opt/homebrew/opt/llvm/bin/clang", "/usr/local/opt/llvm/bin/clang", "clang"]
        .into_iter()
        .find(|c| std::process::Command::new(c).arg("--version").output().is_ok_and(|o| o.status.success()))?;
    let dir = std::env::temp_dir().join(format!("bf-llvm-test-{}", std::process::id()));
    std::fs::create_dir_all(&dir).unwrap();
    let (src, exe, runtime) = (dir.join(format!("{name}.ll")), dir.join(name), dir.join("runtime.c"));
    std::fs::write(&src, ll).unwrap();
    std::fs::write(&runtime, llvm::RUNTIME).unwrap();
    let built = std::process::Command::new(clang).args(["-O2", "-w", "-o"]).arg(&exe).arg(&src).arg(&runtime).output().unwrap();
    assert!(built.status.success(), "{name}: {}", String::from_utf8_lossy(&built.stderr));
    use std::io::Write;
    let mut child = std::process::Command::new(&exe)
        .stdin(std::process::Stdio::piped())
        .stdout(std::process::Stdio::piped())
        .spawn()
        .unwrap();
    child.stdin.take().unwrap().write_all(input).unwrap();
    Some(String::from_utf8(child.wait_with_output().unwrap().stdout).unwrap())
}

#[test]
fn the_llvm_backends_mean_the_same() {
    // every operation on the edges of 64-bit cells, where LLVM's own
    // instructions are undefined (dividing by 0, overflowing, shifting far)
    let ops: Vec<BinOp> = BinOp::ALL.into_iter().filter(|&op| op != BinOp::Index).collect();
    let mut m = Module::new();
    let f = m.main();
    let (a, b) = (f.get_int(), f.get_int());
    for &op in &ops {
        let r = f.binary(op, a, b);
        f.put_int(r);
        f.puts(" ");
    }
    for op in [UnOp::Neg, UnOp::Not, UnOp::LNot, UnOp::Abs] {
        let r = f.unary(op, a);
        f.put_int(r);
        f.puts(" ");
    }
    f.ret_void();
    let ll = llvm::emit(&m).unwrap();
    for (a, b) in [(7, 0), (i64::MIN, -1), (-9, 70), (5, -3), (-1, 64), (i64::MAX, 63), (12345, 3)] {
        let input = format!("{a} {b}");
        let want = String::from_utf8(run(&m, input.as_bytes(), 64).unwrap()).unwrap();
        match run_native(&ll, input.as_bytes(), "ops") {
            Some(got) => assert_eq!(got, want, "{a} {b}"),
            None => return eprintln!("skipped: no clang"),
        }
    }
    // with constant operands, LLVM folds what its instructions would do,
    // so an unguarded overflow becomes poison, whatever the machine does
    let mut m = Module::new();
    let f = m.main();
    let (min, minus_one, zero, seven) = (f.int(i64::MIN), f.int(-1), f.int(0), f.int(7));
    for (a, b) in [(min, minus_one), (seven, zero)] {
        for op in [BinOp::Div, BinOp::Rem, BinOp::DivU, BinOp::RemU] {
            let r = f.binary(op, a, b);
            f.put_int(r);
            f.puts(" ");
        }
    }
    f.ret_void();
    let want = String::from_utf8(run(&m, b"", 64).unwrap()).unwrap();
    assert_eq!(run_native(&llvm::emit(&m).unwrap(), b"", "constants").unwrap(), want);
    // and whole programs: calls, closures, memory, the heap, aborting; each
    // through the IR backend, and lowered to the VM and through its backend
    let mut list = Module::new();
    list_functions(&mut list);
    let f = list.main();
    let n = f.get_int();
    let xs = f.call("build", &[n]);
    let s = f.call("sum", &[xs]);
    f.put_int(s);
    f.ret_void();
    for (name, m, input) in [
        ("fib", fib_module(), b"".as_slice()),
        ("closures", closures_module(), b"5".as_slice()),
        ("list", list, b"40".as_slice()),
    ] {
        let want = String::from_utf8(run(&m, input, 64).unwrap()).unwrap();
        let mut optimized = m.clone();
        optimize(&mut optimized);
        for (how, ll) in [
            ("ir", llvm::emit(&m).unwrap()),
            ("optimized ir", llvm::emit(&optimized).unwrap()),
            ("vm", crate::asm::llvm::emit(&lower(&optimized).unwrap(), 1 << 16)),
        ] {
            assert_eq!(run_native(&ll, input, &format!("{name}_{}", how.replace(' ', "_"))).unwrap(), want, "{name}, {how}");
        }
    }
}

#[test]
fn external_functions() {
    use crate::interp::HostFn;
    // `scale(x, k)` and `total(p)` (which reads memory) are outside the
    // module, called as the VM calls any function the program doesn't
    // define: the arguments in the cells from the pointer on, the result
    // left in acc
    let mut m = Module::new();
    m.external("scale");
    m.external("total");
    let f = m.main();
    let x = f.get_int();
    let three = f.int(3);
    let r = f.call_extern("scale", &[x, three]);
    f.put_int(r);
    f.puts(" ");
    // a record of two cells for C to read
    let two = f.int(2);
    let p = f.heap_alloc(two);
    f.store(p, x);
    let one = f.int(1);
    let q = f.index(p, one);
    f.store(q, r);
    let t = f.call_extern("total", &[p]);
    f.put_int(t);
    f.ret_void();
    let want = "21 28";
    // in the interpreters, as Rust
    let hosts: HashMap<String, HostFn> = [
        (
            "scale".to_string(),
            HostFn::new(|c| {
                c.acc = c.arg(0)? * c.arg(1)?;
                Ok(())
            }),
        ),
        (
            "total".to_string(),
            HostFn::new(|c| {
                let p = c.arg(0)?;
                c.acc = c.tape.load(p)? + c.tape.load(c.tape.index(p, 1))?;
                Ok(())
            }),
        ),
    ]
    .into();
    assert_eq!(String::from_utf8(run_with(&m, b"7", 64, &hosts).unwrap()).unwrap(), want);
    let ops = lower(&m).unwrap();
    for machine in [Machine::cpu(), Machine::c(), Machine::cpu_xlen(16)] {
        let machine = hosts.iter().fold(machine, |mm, (n, h)| mm.host(n, h.clone()));
        assert_eq!(String::from_utf8(machine.run(&ops, b"7").unwrap().output).unwrap(), want);
    }
    // natively, as C: through the C backend, the VM program through LLVM,
    // and the IR straight through LLVM, all calling the same C functions
    // (written with bf.h's macros)
    let c = "#include \"bf.h\"\n\
             BF_EXTERN(Int, scale, (Int, x), (Int, k)) { return x * k; }\n\
             BF_EXTERN(Int, total, (Cells, c)) { return c[0] + c[1]; }\n";
    let Some(clang) = ["/opt/homebrew/opt/llvm/bin/clang", "clang"]
        .into_iter()
        .find(|c| std::process::Command::new(c).arg("--version").output().is_ok_and(|o| o.status.success()))
    else {
        return eprintln!("skipped: no clang");
    };
    let dir = std::env::temp_dir().join(format!("bf-extern-{}", std::process::id()));
    std::fs::create_dir_all(&dir).unwrap();
    std::fs::write(dir.join("lib.c"), c).unwrap();
    std::fs::write(dir.join("bf.h"), crate::asm::C_HEADER).unwrap();
    std::fs::write(dir.join("runtime.c"), llvm::RUNTIME).unwrap();
    let ops = lower_with(&m, &Options { cells: 100_000, ..Options::default() }).unwrap();
    for (name, file, code) in [
        ("via_c", "p.c", crate::compile(&ops)),
        ("via_vm_llvm", "p_vm.ll", crate::asm::llvm::emit(&ops, 100_000) + "\n"),
        ("via_llvm", "p_ir.ll", llvm::emit(&m).unwrap()),
    ] {
        std::fs::write(dir.join(file), &code).unwrap();
        let mut cmd = std::process::Command::new(clang);
        cmd.args(["-O2", "-fwrapv", "-w", "-I"]).arg(&dir).arg("-o").arg(dir.join(name)).arg(dir.join(file)).arg(dir.join("lib.c"));
        if name == "via_llvm" {
            cmd.arg(dir.join("runtime.c"));
        }
        let built = cmd.output().unwrap();
        assert!(built.status.success(), "{name}: {}", String::from_utf8_lossy(&built.stderr));
        use std::io::Write;
        let mut child =
            std::process::Command::new(dir.join(name)).stdin(std::process::Stdio::piped()).stdout(std::process::Stdio::piped()).spawn().unwrap();
        child.stdin.take().unwrap().write_all(b"7").unwrap();
        assert_eq!(String::from_utf8(child.wait_with_output().unwrap().stdout).unwrap(), want, "{name}");
    }
}
