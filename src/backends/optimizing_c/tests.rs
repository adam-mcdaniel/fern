use super::OptimizingC;
use crate::asm::*;
use crate::interp::Machine;
use crate::{Op, Target};
use std::path::PathBuf;
use std::process::{Command, Stdio};

/// A C compiler, and whether it does OpenMP (the code runs either way: on
/// one thread without it). Found out once.
fn compiler() -> Option<(PathBuf, bool)> {
    static FOUND: std::sync::OnceLock<Option<(PathBuf, bool)>> = std::sync::OnceLock::new();
    FOUND
        .get_or_init(|| {
            let dir = Scratch::new("parallel-probe");
            let probe = dir.join("probe.c");
            std::fs::write(&probe, "#include <omp.h>\nint main(void) { return omp_get_max_threads() > 0 ? 0 : 1; }\n").ok()?;
            for cc in ["/opt/homebrew/opt/llvm/bin/clang", "clang", "cc"] {
                let ok = Command::new(cc).arg("-fopenmp").arg(&probe).arg("-o").arg(dir.join("probe")).output();
                if ok.is_ok_and(|o| o.status.success()) {
                    return Some((cc.into(), true));
                }
            }
            for cc in ["clang", "cc"] {
                if Command::new(cc).arg("--version").output().is_ok_and(|o| o.status.success()) {
                    return Some((cc.into(), false));
                }
            }
            None
        })
        .clone()
}

/// A directory for a test's files, gone when the test's done with it, unless
/// it failed: then they're left, for its message to point at.
struct Scratch(PathBuf);

impl Scratch {
    fn new(name: &str) -> Scratch {
        let dir = std::env::temp_dir().join(format!("bf-{name}-{}", std::process::id()));
        std::fs::create_dir_all(&dir).unwrap();
        Scratch(dir)
    }
}

impl std::ops::Deref for Scratch {
    type Target = PathBuf;
    fn deref(&self) -> &PathBuf {
        &self.0
    }
}

impl Drop for Scratch {
    fn drop(&mut self) {
        if !std::thread::panicking() {
            let _ = std::fs::remove_dir_all(&self.0);
        }
    }
}

/// What the program prints compiled with `OptimizingC` (going parallel for
/// any number of iterations), with OpenMP and without, checked against the
/// interpreter; gives the stats the OpenMP build reported (each loop's
/// decision, and how many iterations it ran in parallel).
fn check(name: &str, ops: &[Op], input: &[u8]) -> Vec<(usize, bool, i64)> {
    let want = Machine { cells: 100_064, ..Machine::c() }.run(ops, input).unwrap_or_else(|e| panic!("{name}: {e}")).output;
    let Some((cc, omp)) = compiler() else {
        eprintln!("skipped {name}: no C compiler");
        return vec![];
    };
    let dir = Scratch::new(&format!("parallel-{name}"));
    let mut stats = vec![];
    // (going parallel straight away, on one thread and on several, and
    // after timing the loop a little, which may decide it's not worth it
    // and look again later)
    for (parallel, min_time) in [(false, 0), (true, 0), (true, 2_000)].into_iter().filter(|&(p, _)| !p || omp) {
        let src = dir.join(format!("p{min_time}.c"));
        std::fs::write(&src, OptimizingC { min_iterations: 1, min_time, parallel: true, ..OptimizingC::default() }.compile(ops)).unwrap();
        let exe = dir.join(if parallel { format!("par{min_time}") } else { "seq".into() });
        let mut cmd = Command::new(&cc);
        cmd.args(["-O2", "-fwrapv", "-w", "-DBF_STATS", "-o"]).arg(&exe).arg(&src);
        if parallel {
            cmd.arg("-fopenmp");
        }
        let built = cmd.output().unwrap();
        assert!(built.status.success(), "{name}: {}", String::from_utf8_lossy(&built.stderr));
        let mut child = Command::new(&exe).stdin(Stdio::piped()).stdout(Stdio::piped()).stderr(Stdio::piped()).spawn().unwrap();
        use std::io::Write;
        child.stdin.take().unwrap().write_all(input).unwrap();
        let out = child.wait_with_output().unwrap();
        assert_eq!(String::from_utf8_lossy(&out.stdout), String::from_utf8_lossy(&want), "{name}, {}, min_time {min_time}", if parallel { "OpenMP" } else { "one thread" });
        if parallel && min_time == 0 {
            for line in String::from_utf8_lossy(&out.stderr).lines() {
                // "loop 12: checks pass, 99 iterations before the last"
                let id = line.strip_prefix("loop ").and_then(|l| l.split(':').next()).and_then(|n| n.parse().ok());
                let n = line.split(", ").nth(1).and_then(|l| l.split(' ').next()).and_then(|n| n.parse().ok());
                if let (Some(id), Some(n)) = (id, n) {
                    stats.push((id, line.contains("checks pass"), n));
                }
            }
        }
    }
    stats
}

/// How many iterations ran in parallel, in all.
fn parallel_iterations(stats: &[(usize, bool, i64)]) -> i64 {
    stats.iter().filter(|s| s.1).map(|s| s.2).sum()
}

fn program(build: impl FnOnce(&mut Vec<Op>)) -> Vec<Op> {
    let mut o = vec![];
    init_with(&mut o, 100_000);
    build(&mut o);
    o
}

#[test]
fn a_sieve() {
    let ops = program(|o| {
        let (n, sieve, i, t, j, flag) = (R1, R2, R3, R4, R5, R6);
        getint(o, n);
        mov(o, t, n);
        inc(o, t);
        heap_alloc(o, sieve, t);
        set(o, i, 0);
        set(o, t, 0);
        while_loop(o, flag, |o| { mov(o, flag, i); le_assign(o, flag, n); }, |o| {
            store_index(o, sieve, i, t);
            inc(o, i);
        });
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
        set(o, j, 0);
        while_loop(o, flag, |o| { mov(o, flag, i); le_assign(o, flag, n); }, |o| {
            load_index(o, t, sieve, i);
            lnot_assign(o, t);
            add_assign(o, j, t);
            inc(o, i);
        });
        putint(o, j);
        puts(o, " primes\n");
    });
    let stats = check("sieve", &ops, b"5000");
    // clearing, crossing out, and counting all run in parallel
    assert!(parallel_iterations(&stats) > 10_000, "{stats:?}");
}

#[test]
fn a_reduction_over_computed_elements() {
    // a[i] = i * i % 1000, then their sum, and the count of even ones
    let ops = program(|o| {
        let (n, a, i, t, sum, evens, flag) = (R1, R2, R3, R4, R5, R7, R6);
        set(o, n, 3000);
        heap_alloc(o, a, n);
        set(o, i, 0);
        while_loop(o, flag, |o| { mov(o, flag, i); lt_assign(o, flag, n); }, |o| {
            mov(o, t, i);
            mul_assign(o, t, i);
            rem_const(o, t, 1000);
            store_index(o, a, i, t);
            inc(o, i);
        });
        set(o, i, 0);
        set(o, sum, 0);
        set(o, evens, 0);
        while_loop(o, flag, |o| { mov(o, flag, i); lt_assign(o, flag, n); }, |o| {
            load_index(o, t, a, i);
            add_assign(o, sum, t);
            and_const(o, t, 1);
            lnot_assign(o, t);
            add_assign(o, evens, t);
            inc(o, i);
        });
        putint(o, sum);
        puts(o, " ");
        putint(o, evens);
        puts(o, "\n");
    });
    let stats = check("reduction", &ops, b"");
    assert!(parallel_iterations(&stats) >= 2 * 2999, "{stats:?}");
}

#[test]
fn loops_that_carry_values_stay_in_order() {
    // a running sum, and an array that's read where it was just written
    let ops = program(|o| {
        let (n, a, i, t, u, flag) = (R1, R2, R3, R4, R5, R6);
        set(o, n, 500);
        heap_alloc(o, a, n);
        set(o, i, 0);
        set(o, t, 1);
        store_index(o, a, i, t);
        set(o, i, 1);
        while_loop(o, flag, |o| { mov(o, flag, i); lt_assign(o, flag, n); }, |o| {
            mov(o, u, i);
            dec(o, u);
            load_index(o, t, a, u);
            add_assign(o, t, i);
            store_index(o, a, i, t);
            inc(o, i);
        });
        sub_const(o, i, 1);
        load_index(o, t, a, i);
        putint(o, t);
        puts(o, "\n");
    });
    let stats = check("carried", &ops, b"");
    // the loop of 499 iterations doesn't go parallel (small loops in the
    // routine that prints a number may)
    assert!(stats.iter().all(|s| s.2 < 100 || !s.1), "{stats:?}");
}

#[test]
fn cells_only_some_iterations_write() {
    // `last` is written by the iterations where i % 7 == 3 (not the last
    // ones), `seen` only when an inner loop that sometimes doesn't run
    // does, and `total` sums what the inner loop adds
    let ops = program(|o| {
        let (n, a, i, t, last, seen, j, total, flag) = (R1, R2, R3, R4, R5, R6, R7, R8, R9);
        set(o, n, 1000);
        heap_alloc(o, a, n);
        set(o, i, 0);
        set(o, last, 12345);
        set(o, seen, 777);
        set(o, total, 0);
        while_loop(o, flag, |o| { mov(o, flag, i); lt_assign(o, flag, n); }, |o| {
            mov(o, t, i);
            rem_const(o, t, 7);
            eq_const(o, t, 3);
            begin_if(o, t);
            mov(o, last, i);
            add_assign(o, last, last);
            end_if(o);
            mov(o, j, i);
            rem_const(o, j, 5);
            while_loop(o, R0, |o| { mov(o, R0, j); }, |o| {
                mov(o, seen, i);
                add_assign(o, total, j);
                dec(o, j);
            });
            store_index(o, a, i, t);
            inc(o, i);
        });
        for x in [last, seen, total] {
            putint(o, x);
            puts(o, "\n");
        }
    });
    let stats = check("some_write", &ops, b"");
    assert!(parallel_iterations(&stats) > 500, "{stats:?}");
}

#[test]
fn reads_where_only_the_iteration_knows() {
    // b[i] = a[i * 7 % n] reads a where only the iteration knows, which no
    // iteration writes: in parallel. a[i] = a[i * 7 % n] + 1 reads what other
    // iterations write: the checks see it as it happens, what was written is
    // put back, and the loop runs in order
    let ops = program(|o| {
        let (n, a, b, i, t, u, flag) = (R1, R2, R3, R4, R5, R6, R7);
        set(o, n, 2000);
        heap_alloc(o, a, n);
        heap_alloc(o, b, n);
        set(o, i, 0);
        while_loop(o, flag, |o| { mov(o, flag, i); lt_assign(o, flag, n); }, |o| {
            mov(o, t, i);
            mul_const(o, t, 3);
            store_index(o, a, i, t);
            inc(o, i);
        });
        for (dst, plus) in [(b, 0), (a, 1)] {
            set(o, i, 0);
            while_loop(o, flag, |o| { mov(o, flag, i); lt_assign(o, flag, n); }, |o| {
                mov(o, t, i);
                mul_const(o, t, 7);
                rem_const(o, t, 2000);
                load_index(o, u, a, t);
                add_const(o, u, plus);
                store_index(o, dst, i, u);
                inc(o, i);
            });
        }
        set(o, i, 0);
        set(o, u, 0);
        while_loop(o, flag, |o| { mov(o, flag, i); lt_assign(o, flag, n); }, |o| {
            load_index(o, t, a, i);
            add_assign(o, u, t);
            load_index(o, t, b, i);
            mul_const(o, t, 3);
            add_assign(o, u, t);
            inc(o, i);
        });
        putint(o, u);
        puts(o, "\n");
    });
    let stats = check("gathers", &ops, b"");
    assert!(parallel_iterations(&stats) > 1000, "{stats:?}");
}

#[test]
fn arrays_that_overlap_are_checked() {
    // b is a + 1, so b[i] = a[i] + 1 reads what the iteration before wrote:
    // the checks find that, and it runs in order
    let ops = program(|o| {
        let (n, a, b, i, t, flag) = (R1, R2, R7, R3, R4, R6);
        set(o, n, 400);
        heap_alloc(o, a, n);
        mov(o, b, a);
        set(o, i, 1);
        index(o, b, a, i);
        set(o, i, 0);
        set(o, t, 7);
        store_index(o, a, i, t);
        set(o, i, 0);
        sub_const(o, n, 1);
        while_loop(o, flag, |o| { mov(o, flag, i); lt_assign(o, flag, n); }, |o| {
            load_index(o, t, a, i);
            inc(o, t);
            store_index(o, b, i, t);
            inc(o, i);
        });
        load_index(o, t, a, n);
        putint(o, t);
        puts(o, "\n");
    });
    let stats = check("overlap", &ops, b"");
    assert!(stats.iter().any(|s| !s.1), "{stats:?}");
}

#[test]
fn nested_loops() {
    // a 60 x 50 table of i * 50 + j, then its sum
    let ops = program(|o| {
        let (a, i, j, t, u, sum, flag) = (R1, R2, R3, R4, R5, R7, R6);
        set(o, t, 3000);
        heap_alloc(o, a, t);
        set(o, i, 0);
        while_loop(o, flag, |o| { mov(o, flag, i); lt_const(o, flag, 60); }, |o| {
            set(o, j, 0);
            while_loop(o, flag, |o| { mov(o, flag, j); lt_const(o, flag, 50); }, |o| {
                mov(o, t, i);
                mul_const(o, t, 50);
                add_assign(o, t, j);
                mov(o, u, t);
                store_index(o, a, u, t);
                inc(o, j);
            });
            inc(o, i);
        });
        set(o, i, 0);
        set(o, sum, 0);
        while_loop(o, flag, |o| { mov(o, flag, i); lt_const(o, flag, 3000); }, |o| {
            load_index(o, t, a, i);
            add_assign(o, sum, t);
            inc(o, i);
        });
        putint(o, sum);
        puts(o, "\n");
    });
    let stats = check("nested", &ops, b"");
    assert!(parallel_iterations(&stats) > 2000, "{stats:?}");
}

#[test]
fn calls_in_the_body() {
    // each element through a function that takes its argument on the stack
    let ops = program(|o| {
        let (n, a, i, t, flag) = (R1, R2, R3, R4, R6);
        begin_func(o, "cube", 1);
        mov(o, &local(0), &arg(0));
        mov(o, R0, &local(0));
        mul_assign(o, R0, &local(0));
        mul_assign(o, R0, &local(0));
        ret(o);
        end_func(o);
        set(o, n, 800);
        heap_alloc(o, a, n);
        set(o, i, 0);
        while_loop(o, flag, |o| { mov(o, flag, i); lt_assign(o, flag, n); }, |o| {
            call(o, "cube", &[i]);
            store_index(o, a, i, R0);
            inc(o, i);
        });
        set(o, i, 799);
        load_index(o, t, a, i);
        putint(o, t);
        puts(o, "\n");
    });
    let stats = check("calls", &ops, b"");
    assert!(parallel_iterations(&stats) >= 799, "{stats:?}");
}

#[test]
fn the_examples() {
    // whatever they do, they print the same
    let ops = program(|o| {
        let (x, y) = (R1, R2);
        getint(o, x);
        getint(o, y);
        mul_assign(o, x, y);
        putint(o, x);
        puts(o, "\n");
    });
    check("small", &ops, b"12 34");
}

/// A small random number generator (xorshift), so programs are the same
/// every run.
struct Rng(u64);

impl Rng {
    fn below(&mut self, n: u64) -> u64 {
        self.0 ^= self.0 << 13;
        self.0 ^= self.0 >> 7;
        self.0 ^= self.0 << 17;
        self.0 % n
    }
}

/// Random ops that come back to where they started (`at` cells past cell
/// 40, the pointer staying between cells 34 and 52): loads, stores and
/// arithmetic on the cells there, elements of the array whose address is in
/// cell 30 (chosen by the innermost loop's counter, at cell `counter`),
/// `if`s, and loops that count down a cell of their own (some deciding
/// whether to go on in a way that isn't linear).
fn random_body(rng: &mut Rng, out: &mut Vec<Op>, len: usize, depth: usize, start: i64, counter: Option<i64>) {
    let mut at = start;
    let go = |out: &mut Vec<Op>, at: &mut i64, to: i64| {
        out.push(Op::Move(to - *at));
        *at = to;
    };
    // (away from a loop's counter, which only the loop changes)
    if counter == Some(start) {
        go(out, &mut at, rng.below(19) as i64 - 6);
    }
    for _ in 0..len {
        match rng.below(16) {
            0..=2 => {
                let to = (at + rng.below(7) as i64 - 3).clamp(-6, 12);
                go(out, &mut at, to);
            }
            3 => out.push(Op::Set(rng.below(5))),
            4 | 5 => out.push(Op::Load),
            6 | 7 => out.push(Op::Store),
            8 => out.push(Op::Add),
            9 => out.push(Op::Neg),
            10 => out.push(Op::Positive),
            11 => {
                // an element of the array: the counter's, or a fixed one
                let back = at;
                go(out, &mut at, -10);
                out.push(Op::Load);
                if let Some(c) = counter.filter(|_| rng.below(4) != 0) {
                    go(out, &mut at, c);
                    for _ in 0..8 {
                        out.push(Op::Add);
                    }
                }
                go(out, &mut at, -7);
                out.extend([Op::Store, Op::Deref, Op::Move(rng.below(3) as i64)]);
                out.push([Op::Load, Op::Store, Op::Add, Op::Store][rng.below(4) as usize]);
                out.extend([Op::Refer]);
                go(out, &mut at, back);
            }
            12 | 13 if depth > 0 => {
                // a loop counting down its own cell from 1 to 30
                let c = 15 + depth as i64;
                out.push(Op::Set(rng.below(30) + 1));
                go(out, &mut at, c);
                out.extend([Op::Store, Op::While]);
                random_body(rng, out, 7, depth - 1, c, Some(c));
                out.extend([Op::Set(1), Op::Neg, Op::Add, Op::Store]);
                if rng.below(3) == 0 {
                    out.push(Op::Positive);
                }
                out.push(Op::EndWhile);
            }
            14 if depth > 0 => {
                out.push(Op::While);
                random_body(rng, out, 4, depth - 1, at, counter);
                out.push(Op::Set(0));
                out.push(Op::EndWhile);
            }
            _ => out.push(Op::Load),
        }
    }
    go(out, &mut at, start);
}

fn random_program(rng: &mut Rng) -> Vec<Op> {
    // an array of 100 cells at cell 300, its address in cell 30, and the
    // pointer at cell 40
    let mut ops = vec![Op::Move(300), Op::Where, Op::Move(-270), Op::Store, Op::Move(10)];
    // the cells the program uses start out as numbers, as do the array's
    for c in -6..20 {
        ops.extend([Op::Set(rng.below(9)), Op::Move(c), Op::Store, Op::Move(-c)]);
    }
    for c in 0..100 {
        ops.extend([Op::Set(c as u64 % 7), Op::Move(260 + c), Op::Store, Op::Move(-260 - c)]);
    }
    random_body(rng, &mut ops, 30, 3, 0, None);
    // print what's left near the pointer (all of it, or some, so that what
    // the loops leave in the rest doesn't matter), and in the array
    let all = rng.below(2) == 0;
    for c in (-6..20).chain(260..300) {
        if all || c >= 260 || rng.below(3) == 0 {
            ops.extend([Op::Move(c), Op::Load, Op::Write, Op::Move(-c)]);
        }
    }
    ops
}

/// The target the fuzzers try: going parallel straight away, or (with
/// `FUZZ_TIMED` set) after timing loops a little, as the default does.
fn fuzzed() -> OptimizingC {
    let min_time = if std::env::var("FUZZ_TIMED").is_ok() { 200 } else { 0 };
    OptimizingC { min_iterations: 1, min_time, parallel: true, ..OptimizingC::default() }
}

/// Random programs, raw ops and `asm`'s, built without parallel loops, so
/// that each function (or each loop) keeps its cells in variables (see
/// `promote`): each prints what it does on the interpreter.
#[test]
fn random_programs_with_cells_as_variables() {
    let Some((cc, _)) = compiler() else { return eprintln!("skipped: no C compiler") };
    let count: u64 = std::env::var("FUZZ").ok().and_then(|n| n.parse().ok()).unwrap_or(48);
    let dir = Scratch::new("parallel-promote-fuzz");
    let mut rng = Rng(0x2545f4914f6cdd1d);
    let programs: Vec<Vec<Op>> = (0..count).map(|i| if i % 2 == 0 { random_asm_program(&mut rng) } else { random_program(&mut rng) }).collect();
    std::thread::scope(|scope| {
        for chunk in programs.chunks(programs.len().div_ceil(8).max(1)).enumerate() {
            let (cc, dir) = (&cc, &dir);
            scope.spawn(move || {
                let machine = Machine { max_steps: 50_000_000, cells: 100_064, ..Machine::c() };
                for (j, ops) in chunk.1.iter().enumerate() {
                    let Ok(want) = machine.run(ops, b"") else { continue };
                    let name = format!("p{}_{j}", chunk.0);
                    let src = dir.join(format!("{name}.c"));
                    // (half done throughout functions, half loop by loop)
                    let promote_ops = if j % 2 == 0 { usize::MAX } else { 0 };
                    std::fs::write(&src, OptimizingC { parallel: false, promote_ops, ..OptimizingC::default() }.compile(ops)).unwrap();
                    let exe = dir.join(&name);
                    let built = Command::new(cc).args(["-O1", "-fwrapv", "-w", "-o"]).arg(&exe).arg(&src).output().unwrap();
                    assert!(built.status.success(), "{}", String::from_utf8_lossy(&built.stderr));
                    let out = Command::new(&exe).output().unwrap();
                    assert_eq!(String::from_utf8_lossy(&out.stdout), String::from_utf8_lossy(&want.output), "prints something else with cells as variables (see {})", src.display());
                }
            });
        }
    });
}

/// Whether `ops` runs on the interpreter and prints something else built
/// with `OptimizingC` (as `name`, in `dir`).
fn differs(ops: &[Op], cc: &PathBuf, omp: bool, dir: &std::path::Path, name: &str) -> bool {
    let machine = Machine { max_steps: 3_000_000, ..Machine::c() };
    let Ok(want) = machine.run(ops, b"") else { return false };
    let src = dir.join(format!("{name}.c"));
    std::fs::write(&src, fuzzed().compile(ops)).unwrap();
    let exe = dir.join(name);
    let mut cmd = Command::new(cc);
    cmd.args(["-O1", "-fwrapv", "-w", "-o"]).arg(&exe).arg(&src);
    if omp {
        cmd.arg("-fopenmp");
    }
    if !cmd.output().is_ok_and(|o| o.status.success()) {
        return false;
    }
    Command::new(&exe).output().is_ok_and(|o| o.stdout != want.output)
}

/// The smallest program found by removing ops from `ops` (keeping brackets
/// matched) that `differs` still.
fn shrink(mut ops: Vec<Op>, cc: &PathBuf, omp: bool, dir: &std::path::Path, name: &str) -> Vec<Op> {
    let matched = |ops: &[Op]| {
        let mut depth = 0i32;
        for op in ops {
            match op {
                Op::While => depth += 1,
                Op::EndWhile => depth -= 1,
                _ => {}
            }
            if depth < 0 {
                return false;
            }
        }
        depth == 0
    };
    loop {
        let mut smaller = false;
        for len in [32, 16, 8, 4, 2, 1] {
            let mut i = 0;
            while i + len <= ops.len() {
                let mut candidate = ops.clone();
                candidate.drain(i..i + len);
                if matched(&candidate) && differs(&candidate, cc, omp, dir, name) {
                    ops = candidate;
                    smaller = true;
                } else {
                    i += 1;
                }
            }
        }
        if !smaller {
            return ops;
        }
    }
}

#[test]
fn random_programs_print_the_same() {
    let Some((cc, omp)) = compiler() else { return eprintln!("skipped: no C compiler") };
    let count: u64 = std::env::var("FUZZ").ok().and_then(|n| n.parse().ok()).unwrap_or(48);
    let seed: u64 = std::env::var("FUZZ_SEED").ok().and_then(|n| n.parse().ok()).unwrap_or(7);
    let dir = Scratch::new("parallel-fuzz");
    let mut rng = Rng(seed.wrapping_mul(0x9e3779b97f4a7c15) | 1);
    let programs: Vec<Vec<Op>> = (0..count).map(|_| random_program(&mut rng)).collect();
    let ran = std::sync::atomic::AtomicUsize::new(0);
    let parallel = std::sync::atomic::AtomicUsize::new(0);
    std::thread::scope(|scope| {
        for chunk in programs.chunks(programs.len().div_ceil(8).max(1)).enumerate() {
            let (cc, dir, ran, parallel) = (&cc, &dir, &ran, &parallel);
            scope.spawn(move || {
                let machine = Machine { max_steps: 3_000_000, ..Machine::c() };
                for (j, ops) in chunk.1.iter().enumerate() {
                    let Ok(want) = machine.run(ops, b"") else { continue };
                    let name = format!("p{}_{j}", chunk.0);
                    let src = dir.join(format!("{name}.c"));
                    std::fs::write(&src, fuzzed().compile(ops)).unwrap();
                    let exe = dir.join(&name);
                    let mut cmd = Command::new(cc);
                    cmd.args(["-O1", "-fwrapv", "-w", "-DBF_STATS", "-o"]).arg(&exe).arg(&src);
                    if omp {
                        cmd.arg("-fopenmp");
                    }
                    let built = cmd.output().unwrap();
                    assert!(built.status.success(), "{}", String::from_utf8_lossy(&built.stderr));
                    let out = Command::new(&exe).output().unwrap();
                    if out.stdout != want.output {
                        let small = shrink(ops.clone(), cc, omp, dir, &format!("{name}_shrink"));
                        let small_src = dir.join(format!("{name}_shrunk.c"));
                        std::fs::write(&small_src, fuzzed().compile(&small)).unwrap();
                        let got = {
                            differs(&small, cc, omp, dir, &format!("{name}_shrunk"));
                            Command::new(dir.join(format!("{name}_shrunk"))).output().map(|o| o.stdout).unwrap_or_default()
                        };
                        panic!(
                            "\n{}\nprints {:?} built with OptimizingC (see {}), not {:?}",
                            to_source(&small),
                            got,
                            small_src.display(),
                            Machine { max_steps: 3_000_000, ..Machine::c() }.run(&small, b"").map(|h| h.output)
                        );
                    }
                    ran.fetch_add(1, std::sync::atomic::Ordering::Relaxed);
                    if String::from_utf8_lossy(&out.stderr).lines().any(|l| l.contains("checks pass") && !l.contains(" 0 iterations") && !l.contains("-1 iterations")) {
                        parallel.fetch_add(1, std::sync::atomic::Ordering::Relaxed);
                    }
                }
            });
        }
    });
    let (ran, parallel) = (ran.into_inner(), parallel.into_inner());
    eprintln!("{ran} programs ran the same, {parallel} with loops in parallel");
    assert!(ran > count as usize / 2, "only {ran} programs ran");
    assert!(parallel > ran / 4, "only {parallel} of {ran} ran loops in parallel");
}

/// Random statements made with `asm`'s helpers: arithmetic on registers,
/// loads and stores of an array's elements (at the loop counter, near it,
/// or anywhere), `if`s, calls, and `while_loop`s counting a register up.
fn random_asm(rng: &mut Rng, o: &mut dyn Program, len: usize, depth: usize, counter: Option<&'static Location>) {
    let regs: [&'static Location; 5] = [R3, R4, R5, R6, R7];
    let a = R2;
    let pick = |rng: &mut Rng| regs[rng.below(regs.len() as u64) as usize];
    for _ in 0..len {
        let (x, y) = (pick(rng), pick(rng));
        let kinds = if rng.below(2) == 0 { 14 } else { 31 };
        match rng.below(kinds) {
            0 => add_assign(o, x, y),
            1 => sub_assign(o, x, y),
            2 => mul_const(o, x, rng.below(5) as i64),
            3 => and_const(o, x, 7),
            4 => lnot_assign(o, x),
            5 => lt_assign(o, x, y),
            6 => set(o, x, rng.below(20)),
            7 | 8 => {
                // an element: the counter's (maybe plus one), or one chosen by
                // a register, kept in the array
                let i = R8;
                match counter.filter(|_| rng.below(3) != 0) {
                    Some(c) => {
                        mov(o, i, c);
                        if rng.below(2) == 0 {
                            inc(o, i);
                        }
                    }
                    None => {
                        mov(o, i, x);
                        and_const(o, i, 31);
                    }
                }
                if rng.below(2) == 0 {
                    load_index(o, y, a, i);
                } else {
                    store_index(o, a, i, y);
                }
            }
            9 if depth > 0 => {
                begin_if(o, x);
                random_asm(rng, o, 3, depth - 1, counter);
                if rng.below(2) == 0 {
                    begin_else(o);
                    random_asm(rng, o, 2, depth - 1, counter);
                }
                end_if(o);
            }
            10 | 11 if depth > 0 => {
                // a loop counting its own register up to a small number
                let c: &'static Location = if depth == 2 { R9 } else { R1 };
                set(o, c, 0);
                let n = rng.below(40) as i64 + 1;
                while_loop(o, R0, |o| { mov(o, R0, c); lt_const(o, R0, n); }, |o| {
                    random_asm(rng, o, 5, depth - 1, Some(c));
                    inc(o, c);
                });
            }
            12 => call(o, "twice", &[x]),
            // routines the target does natively
            14 => rem_const(o, x, 7),
            15 => div_const(o, x, 4),
            16 => rsh_const(o, x, 1 + rng.below(3) as i64),
            17 => lsh_const(o, x, 9 + rng.below(3) as i64),
            18 => xor_assign(o, x, y),
            19 => or_assign(o, x, y),
            20 => and_assign(o, x, y),
            21 => mul_assign(o, x, y),
            22 => rem_assign(o, x, y),
            23 | 24 if depth > 0 => {
                // a loop that runs as many times as a register's low bits
                // say (sometimes not at all)
                let c: &'static Location = if depth == 2 { R9 } else { R1 };
                mov(o, c, x);
                and_const(o, c, 3);
                while_loop(o, R0, |o| { mov(o, R0, c); }, |o| {
                    random_asm(rng, o, 3, depth - 1, None);
                    dec(o, c);
                });
            }
            // running maximums and minimums, and where they were
            25 => max_assign(o, x, y),
            26 => min_assign(o, x, y),
            27 | 28 => {
                let z = pick(rng);
                mov(o, R8, x);
                match rng.below(4) {
                    0 => lt_assign(o, R8, y),
                    1 => ge_assign(o, R8, y),
                    2 => ltu_assign(o, R8, y),
                    _ => gt_assign(o, R8, y),
                }
                begin_if(o, R8);
                mov(o, x, y);
                mov(o, z, counter.unwrap_or(y));
                end_if(o);
            }
            // one of a few elements at the end of the array, always the
            // same one: read, written, or added to
            29 | 30 => {
                let k = 44 + rng.below(4);
                set(o, R8, k);
                match rng.below(3) {
                    0 => load_index(o, x, a, R8),
                    1 => store_index(o, a, R8, y),
                    _ => {
                        load_index(o, x, a, R8);
                        add_assign(o, x, y);
                        store_index(o, a, R8, x);
                    }
                }
            }
            _ => mov(o, x, y),
        }
    }
}

fn random_asm_program(rng: &mut Rng) -> Vec<Op> {
    program(|o| {
        begin_func(o, "twice", 1);
        mov(o, R0, &arg(0));
        add_assign(o, R0, &arg(0));
        ret(o);
        end_func(o);
        set(o, R1, 48);
        heap_alloc(o, R2, R1);
        // the array, and the registers, start out as numbers
        for k in 0..48 {
            set(o, R8, k);
            set(o, R9, k * 3 % 11);
            store_index(o, R2, R8, R9);
        }
        for (k, r) in [R3, R4, R5, R6, R7].into_iter().enumerate() {
            set(o, r, k as u64 + 1);
        }
        random_asm(rng, o, 12, 2, None);
        // print what's in the registers and the array
        for r in [R3, R4, R5, R6, R7] {
            putint(o, r);
            puts(o, " ");
        }
        set(o, R8, 0);
        while_loop(o, R0, |o| { mov(o, R0, R8); lt_const(o, R0, 48); }, |o| {
            load_index(o, R9, R2, R8);
            putint(o, R9);
            puts(o, ",");
            inc(o, R8);
        });
    })
}

#[test]
fn random_asm_programs_print_the_same() {
    // (FUZZ_SUM sums up loops in loops that write memory as soon as it can)
    if std::env::var("FUZZ_SUM").is_ok() {
        super::analysis::SUM_UP_EARLY.store(true, std::sync::atomic::Ordering::Relaxed);
    }
    fuzz_asm("asm", random_asm_program, 32, 3);
}

#[test]
fn random_loops_in_loops_print_the_same() {
    // (loops in loops are summed up as soon as they can be)
    super::analysis::SUM_UP_EARLY.store(true, std::sync::atomic::Ordering::Relaxed);
    fuzz_asm("nests", random_nest_program, 24, 5);
}

/// Rows of an array, loops over them and over each one's cells: what a cell
/// gets is worked out from cells near it (in the row, and in the rows next
/// to it, as wide as `width` says, which may be less than the rows are
/// long), and kept in registers (sums, maximums) and in cells past the
/// rows.
fn random_nest_program(rng: &mut Rng) -> Vec<Op> {
    program(|o| {
        let (a, i, j, at, t, s, m) = (R2, R9, R1, R3, R4, R5, R6);
        set(o, R7, 600);
        heap_alloc(o, a, R7);
        set(o, i, 0);
        while_loop(o, R0, |o| { mov(o, R0, i); lt_const(o, R0, 600); }, |o| {
            mov(o, t, i);
            mul_const(o, t, 7);
            rem_const(o, t, 19);
            store_index(o, a, i, t);
            inc(o, i);
        });
        set(o, s, 0);
        set_int(o, m, -1);
        for _ in 0..1 + rng.below(2) {
            let rows = 2 + rng.below(18) as i64;
            let cols = 17 + rng.below(14) as i64;
            let width = [cols, cols, cols + 3, cols - 2, 16][rng.below(5) as usize];
            set(o, i, 0);
            while_loop(o, R8, |o| { mov(o, R8, i); lt_const(o, R8, rows); }, |o| {
                set(o, j, 0);
                while_loop(o, R0, |o| { mov(o, R0, j); lt_const(o, R0, cols); }, |o| {
                    // the cell (row i, column j), and one near it
                    mov(o, at, i);
                    mul_const(o, at, width);
                    add_assign(o, at, j);
                    add_const(o, at, 40);
                    for _ in 0..1 + rng.below(4) {
                        match rng.below(7) {
                            0 | 1 => {
                                // a[at] = a[at + d] * k + j
                                mov(o, t, at);
                                add_const(o, t, [0, 1, -1, width, -width][rng.below(5) as usize]);
                                load_index(o, t, a, t);
                                mul_const(o, t, 1 + rng.below(3) as i64);
                                add_assign(o, t, j);
                                and_const(o, t, 0xff);
                                store_index(o, a, at, t);
                            }
                            2 => {
                                load_index(o, t, a, at);
                                add_assign(o, s, t);
                            }
                            3 => {
                                load_index(o, t, a, at);
                                max_assign(o, m, t);
                            }
                            4 => {
                                // a cell past the rows, as a sum
                                load_index(o, t, a, at);
                                set(o, R7, 590 + rng.below(4));
                                load_index(o, R0, a, R7);
                                add_assign(o, R0, t);
                                store_index(o, a, R7, R0);
                            }
                            5 => {
                                // only some times round
                                load_index(o, t, a, at);
                                mov(o, R7, t);
                                rem_const(o, R7, 3);
                                begin_if(o, R7);
                                add_const(o, t, 5);
                                store_index(o, a, at, t);
                                end_if(o);
                            }
                            _ => {
                                mov(o, t, j);
                                add_assign(o, t, i);
                                store_index(o, a, at, t);
                            }
                        }
                    }
                    inc(o, j);
                });
                inc(o, i);
            });
        }
        putint(o, s);
        puts(o, " ");
        putint(o, m);
        puts(o, " ");
        set(o, i, 0);
        set(o, s, 0);
        while_loop(o, R0, |o| { mov(o, R0, i); lt_const(o, R0, 600); }, |o| {
            load_index(o, t, a, i);
            mov(o, R7, i);
            rem_const(o, R7, 7);
            inc(o, R7);
            mul_assign(o, t, R7);
            add_assign(o, s, t);
            inc(o, i);
        });
        putint(o, s);
        puts(o, "\n");
    })
}

/// Checks that programs `make` makes (FUZZ of them, `count` if that's not
/// set, from FUZZ_SEED or `seed`) print the same compiled as they do on the
/// interpreter.
fn fuzz_asm(name: &str, make: fn(&mut Rng) -> Vec<Op>, count: u64, seed: u64) {
    let Some((cc, omp)) = compiler() else { return eprintln!("skipped: no C compiler") };
    let count: u64 = std::env::var("FUZZ").ok().and_then(|n| n.parse().ok()).unwrap_or(count);
    let seed: u64 = std::env::var("FUZZ_SEED").ok().and_then(|n| n.parse().ok()).unwrap_or(seed);
    let dir = Scratch::new(&format!("parallel-{name}-fuzz"));
    let mut rng = Rng(seed.wrapping_mul(0x9e3779b97f4a7c15) | 1);
    let programs: Vec<Vec<Op>> = (0..count).map(|_| make(&mut rng)).collect();
    let ran = std::sync::atomic::AtomicUsize::new(0);
    let parallel = std::sync::atomic::AtomicUsize::new(0);
    std::thread::scope(|scope| {
        for chunk in programs.chunks(programs.len().div_ceil(8).max(1)).enumerate() {
            let (cc, dir, ran, parallel) = (&cc, &dir, &ran, &parallel);
            scope.spawn(move || {
                let machine = Machine { max_steps: 50_000_000, cells: 100_064, ..Machine::c() };
                for (j, ops) in chunk.1.iter().enumerate() {
                    let want = machine.run(ops, b"").unwrap_or_else(|e| panic!("{e}"));
                    let name = format!("a{}_{j}", chunk.0);
                    let src = dir.join(format!("{name}.c"));
                    std::fs::write(&src, fuzzed().compile(ops)).unwrap();
                    let exe = dir.join(&name);
                    let mut cmd = Command::new(cc);
                    cmd.args(["-O1", "-fwrapv", "-w", "-DBF_STATS", "-o"]).arg(&exe).arg(&src);
                    if omp {
                        cmd.arg("-fopenmp");
                    }
                    let built = cmd.output().unwrap();
                    assert!(built.status.success(), "{}", String::from_utf8_lossy(&built.stderr));
                    let out = Command::new(&exe).output().unwrap();
                    assert_eq!(
                        String::from_utf8_lossy(&out.stdout),
                        String::from_utf8_lossy(&want.output),
                        "prints something else built with OptimizingC (see {})",
                        src.display()
                    );
                    ran.fetch_add(1, std::sync::atomic::Ordering::Relaxed);
                    if String::from_utf8_lossy(&out.stderr).lines().any(|l| l.contains("checks pass") && !l.contains(" 0 iterations") && !l.contains("-1 iterations")) {
                        parallel.fetch_add(1, std::sync::atomic::Ordering::Relaxed);
                    }
                }
            });
        }
    });
    let (ran, parallel) = (ran.into_inner(), parallel.into_inner());
    eprintln!("{ran} programs ran the same, {parallel} with loops in parallel, {} loops in loops summed up", super::analysis::SUMMED.load(std::sync::atomic::Ordering::Relaxed));
    assert!(parallel > ran / 4, "only {parallel} of {ran} ran loops in parallel");
}

#[test]
fn the_same_program_compiles_the_same() {
    // (the analysis keeps things in hash maps, which iterate in a different
    // order each time)
    let mut rng = Rng(99);
    for _ in 0..8 {
        let ops = random_asm_program(&mut rng);
        assert_eq!(OptimizingC { parallel: true, ..OptimizingC::default() }.compile(&ops), OptimizingC { parallel: true, ..OptimizingC::default() }.compile(&ops));
    }
}

#[test]
fn idioms_do_what_the_routines_do() {
    // each routine the target knows, compiled as it is and done natively,
    // from the same cells (edge values, and random ones), must leave every
    // cell and acc the same
    let Some((cc, _)) = compiler() else { return eprintln!("skipped: no C compiler") };
    let dir = Scratch::new("idioms");
    let idioms = super::idioms::idioms();
    let labels: Vec<&str> = idioms.iter().map(|i| i.label.as_str()).collect();
    assert_eq!(
        labels,
        ["rt_mul", "rt_less", "rt_lessu", "rt_divu", "rt_divuk", "rt_lowbits", "rt_rsh", "rt_rshu", "rt_lsh", "rt_and", "rt_or", "rt_xor", "rt_andk", "rt_ork", "rt_xork", "rt_divs"]
    );
    // (with every routine defined, for those that call others)
    let mut all = vec![];
    for idiom in &idioms {
        all.extend([Op::Label(label_of(&idiom.label)), Op::Func]);
        all.extend(idiom.body.iter().copied());
        all.push(Op::EndFunc);
    }
    for idiom in idioms {
        let ops = all.clone();
        let plain = OptimizingC { idioms: false, linear: false, ..OptimizingC::default() }.compile(&ops).replace("int main(void)", "int bf_unused_main(void)");
        let native = idiom.native.replace("ORIGINAL", &format!("{{ bf_st bf_r = {}(ptr, acc); ptr = bf_r.ptr; acc = bf_r.acc; }}", idiom.label));
        let c = format!(
            r#"{plain}
static void bf_native(int64_t **bf_ptr, int64_t *bf_acc) {{
int64_t *ptr = *bf_ptr;
int64_t acc = *bf_acc;
{native}*bf_ptr = ptr;
*bf_acc = acc;
}}

static uint64_t bf_rand_state = 88172645463325252ull;
static uint64_t bf_rand(void) {{ bf_rand_state ^= bf_rand_state << 13; bf_rand_state ^= bf_rand_state >> 7; bf_rand_state ^= bf_rand_state << 17; return bf_rand_state; }}
static int64_t bf_value(void) {{
    static const int64_t edges[] = {{0, 1, -1, 2, -2, 3, 7, 8, 10, 63, 64, 1000003, INT64_MAX, INT64_MIN, INT64_MAX - 1, INT64_MIN + 1, 1ll << 32, -(1ll << 32), 1ll << 62, (1ll << 62) + 1, (1ll << 62) - 1, 16383, 16384}};
    switch (bf_rand() % 4) {{
    case 0: return edges[bf_rand() % (sizeof edges / sizeof edges[0])];
    case 1: return (int64_t)(bf_rand() % 2000) - 1000;
    case 2: return (int64_t)(bf_rand() >> (bf_rand() % 64));
    default: return (int64_t)bf_rand();
    }}
}}

int main(void) {{
    stack = malloc(1024 * sizeof(int64_t *));
    for (int round = 0; round < 200000; round++) {{
        int64_t a[64], b[64];
        for (int i = 0; i < 64; i++) a[i] = bf_value();
        {{ int64_t *c = a; {tame} (void)c; }}
        for (int i = 0; i < 64; i++) b[i] = a[i];
        int64_t acc0 = bf_value();
        int64_t *pa = a, *pb = b, acca = acc0, accb = acc0;
        {{ bf_st r = {name}(pa, acca); pa = r.ptr; acca = r.acc; }}
        bf_native(&pb, &accb);
        int same = pa - a == pb - b && acca == accb;
        for (int i = 0; i < 64; i++) same &= a[i] == b[i];
        if (!same) {{
            printf("round %d: acc %lld, native %lld\n", round, (long long)acca, (long long)accb);
            for (int i = 0; i < 64; i++) if (a[i] != b[i]) printf("  cell %d: %lld, native %lld\n", i, (long long)a[i], (long long)b[i]);
            return 1;
        }}
    }}
    return 0;
}}
"#,
            name = idiom.label,
            tame = if idiom.tame.is_empty() { String::new() } else { idiom.tame.to_string() }
        );
        let src = dir.join(format!("{}.c", idiom.label));
        std::fs::write(&src, c).unwrap();
        let exe = dir.join(&idiom.label);
        let built = Command::new(&cc).args(["-O2", "-fwrapv", "-w", "-o"]).arg(&exe).arg(&src).output().unwrap();
        assert!(built.status.success(), "{}: {}", idiom.label, String::from_utf8_lossy(&built.stderr));
        let run = Command::new(&exe).output().unwrap();
        assert!(run.status.success(), "{} differs (see {}):\n{}", idiom.label, src.display(), String::from_utf8_lossy(&run.stdout));
    }
}

fn label_of(name: &str) -> [u8; 16] {
    let mut l = [0; 16];
    l[..name.len()].copy_from_slice(name.as_bytes());
    l
}

/// Programs the fuzzer found printing something else once.
#[test]
fn programs_the_fuzzer_found() {
    for (i, code) in [
        ">{300}4=[<{14}>>>=>{10}<{27}>{28}1-+=#]<{28}> >{16}$.",
        ">{300}26[=[<{19}=>{18}>1-+=#]<{5}>{6}]<{18}<{6}<{10}>{14}$.",
        ">{300}18[=[<{10}=>> >{8}1-+=#]<{27}>>> >{24}>]<{28}> >{16}$.",
    ]
    .into_iter()
    .enumerate()
    {
        check(&format!("found{i}"), &crate::parse(code).unwrap(), b"");
    }
}

/// A loop that reaches a cell near the pointer through a pointer (its
/// address, from `?`): run with copies of the cells, it has to carry on
/// without them.
#[test]
fn cells_near_the_pointer_through_a_pointer() {
    use Op::*;
    let ops = vec![
        Set(5),
        Store,
        While,
        // c1 = &c2, then c2 += 3 through it
        Move(2),
        Where,
        Move(-1),
        Store,
        Deref,
        Set(3),
        Add,
        Store,
        Refer,
        // and c2 read where it is, so it's one of the copies
        Move(1),
        Load,
        Move(-1),
        // c0 -= 1
        Move(-1),
        Set(1),
        Neg,
        Add,
        Store,
        EndWhile,
        Move(2),
        Load,
        Write,
    ];
    check("through_a_pointer", &ops, b"");
    let code = OptimizingC { parallel: true, ..OptimizingC::default() }.compile(&ops);
    assert!(code.contains("with copies of the cells near the pointer"), "the loop doesn't run with copies");
}

/// Loops counted to a small constant (which `lt_const` tests by the sign
/// first): from 0 their count is solved; from below 0 the generated code
/// sees the counter would be, and they run in order.
#[test]
fn loops_counted_to_small_constants() {
    for from in [0, -500] {
        let ops = program(|o| {
            let (i, t, sum, flag) = (R1, R2, R3, R4);
            set(o, sum, 0);
            set_int(o, i, from);
            while_loop(o, flag, |o| { mov(o, flag, i); lt_const(o, flag, 1500); }, |o| {
                mov(o, t, i);
                mul_assign(o, t, i);
                rem_const(o, t, 1009);
                add_assign(o, sum, t);
                inc(o, i);
            });
            putint(o, sum);
            puts(o, "\n");
        });
        let stats = check(&format!("small_bound_{}", from.unsigned_abs()), &ops, b"");
        let code = OptimizingC { parallel: true, ..OptimizingC::default() }.compile(&ops);
        assert!(code.contains("solved from a comparison"), "the count isn't solved");
        if from == 0 {
            assert!(parallel_iterations(&stats) > 1000, "{stats:?}");
        }
    }
}

#[test]
fn maximums_and_minimums() {
    // over values with many ties (and some below the starting values): the
    // largest and the first place it's found (a tie leaves it), the
    // smallest and the last place it's found (a tie sets it); then an
    // unsigned largest, and a largest that starts above them all (so
    // nothing sets it)
    let ops = program(|o| {
        let (i, v, t, best, at, least, where_, flag) = (R1, R2, R3, R4, R5, R6, R7, R8);
        set_int(o, best, -1);
        set(o, at, 999_999);
        set_int(o, least, 50);
        set(o, where_, 888_888);
        set(o, i, 0);
        while_loop(o, flag, |o| { mov(o, flag, i); lt_const(o, flag, 3000); }, |o| {
            // v = (i * 37) % 101 - 20
            mov(o, v, i);
            mul_const(o, v, 37);
            rem_const(o, v, 101);
            sub_const(o, v, 20);
            mov(o, t, best);
            lt_assign(o, t, v);
            begin_if(o, t);
            mov(o, best, v);
            mov(o, at, i);
            end_if(o);
            mov(o, t, least);
            ge_assign(o, t, v);
            begin_if(o, t);
            mov(o, least, v);
            mov(o, where_, i);
            end_if(o);
            inc(o, i);
        });
        for x in [best, at, least, where_] {
            putint(o, x);
            puts(o, "\n");
        }
    });
    let stats = check("extremes", &ops, b"");
    assert!(parallel_iterations(&stats) > 2000, "{stats:?}");

    let ops = program(|o| {
        let (i, v, t, umax, big, flag) = (R1, R2, R3, R4, R5, R8);
        set(o, umax, 0);
        set_int(o, big, 1000);
        set(o, i, 0);
        while_loop(o, flag, |o| { mov(o, flag, i); lt_const(o, flag, 3000); }, |o| {
            // v = (i * 7919) % 211 - 100: below 0 is the most, unsigned
            mov(o, v, i);
            mul_const(o, v, 7919);
            rem_const(o, v, 211);
            sub_const(o, v, 100);
            mov(o, t, umax);
            ltu_assign(o, t, v);
            begin_if(o, t);
            mov(o, umax, v);
            end_if(o);
            max_assign(o, big, v);
            inc(o, i);
        });
        for x in [umax, big] {
            putint(o, x);
            puts(o, "\n");
        }
    });
    let stats = check("extremes_unsigned", &ops, b"");
    assert!(parallel_iterations(&stats) > 2000, "{stats:?}");
}

#[test]
fn memory_like_cells() {
    // a block of globals that R9 points to: a sum, the largest and where it
    // was, what the last iteration that wrote it left, and the loop's flag,
    // all in memory; the array the iterations write is elsewhere
    let ops = program(|o| {
        let (a, i, v, t) = (R1, R2, R3, R4);
        let g = |k: i64| R9.deref().offset(k);
        heap_alloc_const(o, a, 3000);
        heap_alloc_const(o, R9, 6);
        set(o, &g(0), 7);
        set_int(o, &g(1), -1000);
        set(o, &g(2), 123);
        set(o, &g(3), 456);
        set(o, i, 0);
        while_loop(o, &g(4), |o| { mov(o, &g(4), i); lt_const(o, &g(4), 3000); }, |o| {
            // v = (i * 37) % 101 - 50
            mov(o, v, i);
            mul_const(o, v, 37);
            rem_const(o, v, 101);
            sub_const(o, v, 50);
            store_index(o, a, i, v);
            add_assign(o, &g(0), v);
            mov(o, t, &g(1));
            lt_assign(o, t, v);
            begin_if(o, t);
            mov(o, &g(1), v);
            mov(o, &g(2), i);
            end_if(o);
            mov(o, t, i);
            rem_const(o, t, 7);
            eq_const(o, t, 2);
            begin_if(o, t);
            mov(o, &g(3), i);
            end_if(o);
            inc(o, i);
        });
        for k in 0..4 {
            putint(o, &g(k));
            puts(o, "\n");
        }
        set(o, v, 0);
        set(o, i, 0);
        while_loop(o, R0, |o| { mov(o, R0, i); lt_const(o, R0, 3000); }, |o| {
            load_index(o, t, a, i);
            add_assign(o, v, t);
            inc(o, i);
        });
        putint(o, v);
        puts(o, "\n");
    });
    let stats = check("memory_like_cells", &ops, b"");
    assert!(parallel_iterations(&stats) > 5000, "{stats:?}");
}

#[test]
fn reads_of_what_later_iterations_write() {
    // v[i] = v[i] + v[i + 1] reads what the next iteration writes, and
    // d[c] = max(d[c], d[c - w] + 1) going down reads what an iteration w
    // later writes: both can read a copy of how the memory was. But
    // u[i + 1] = u[i] + 1 and u[i + 20] = u[i] * 3 read what earlier
    // iterations write: those stay in order
    let ops = program(|o| {
        let (v, d, u, i, t, s, w) = (R1, R2, R3, R4, R5, R6, R7);
        for a in [v, d, u] {
            heap_alloc_const(o, a, 2100);
        }
        set(o, i, 0);
        while_loop(o, R0, |o| { mov(o, R0, i); lt_const(o, R0, 2100); }, |o| {
            mov(o, t, i);
            mul_const(o, t, 7);
            rem_const(o, t, 13);
            store_index(o, v, i, t);
            store_index(o, d, i, t);
            store_index(o, u, i, t);
            inc(o, i);
        });
        // in place, a copy of the next
        set(o, i, 0);
        while_loop(o, R0, |o| { mov(o, R0, i); lt_const(o, R0, 2000); }, |o| {
            load_index(o, t, v, i);
            mov(o, s, i);
            inc(o, s);
            load_index(o, s, v, s);
            add_assign(o, t, s);
            store_index(o, v, i, t);
            inc(o, i);
        });
        // down, a copy of one w back
        set(o, w, 37);
        set(o, i, 2000);
        while_loop(o, R0, |o| { mov(o, R0, i); ge_assign(o, R0, w); }, |o| {
            mov(o, t, i);
            sub_assign(o, t, w);
            load_index(o, t, d, t);
            inc(o, t);
            load_index(o, s, d, i);
            max_assign(o, t, s);
            store_index(o, d, i, t);
            dec(o, i);
        });
        // in order: what the one before wrote
        for gap in [1, 20] {
            set(o, i, 0);
            while_loop(o, R0, |o| { mov(o, R0, i); lt_const(o, R0, 2000); }, |o| {
                load_index(o, t, u, i);
                mul_const(o, t, 3);
                and_const(o, t, 0xffff);
                mov(o, s, i);
                add_const(o, s, gap);
                store_index(o, u, s, t);
                inc(o, i);
            });
        }
        for a in [v, d, u] {
            set(o, s, 0);
            set(o, i, 0);
            while_loop(o, R0, |o| { mov(o, R0, i); lt_const(o, R0, 2100); }, |o| {
                load_index(o, t, a, i);
                mov(o, w, i);
                rem_const(o, w, 5);
                inc(o, w);
                mul_assign(o, t, w);
                add_assign(o, s, t);
                inc(o, i);
            });
            putint(o, s);
            puts(o, "\n");
        }
    });
    let stats = check("later_writes", &ops, b"");
    assert!(parallel_iterations(&stats) > 3000, "{stats:?}");
}

#[test]
fn locals_and_pointers_to_them() {
    // a function's locals, which a loop in it uses as cells (copies of
    // them), and a pointer to one of them that the loop sometimes writes
    // through, and one to the frame of the function that called it
    let ops = program(|o| {
        begin_func(o, "f", 3);
        set(o, &local(0), 0);
        set(o, &local(1), 0);
        mov(o, &local(2), &arg(0));
        addr_of(o, R5, &local(1));
        while_loop(o, R0, |o| { mov(o, R0, &local(0)); lt_const(o, R0, 300); }, |o| {
            add_assign(o, &local(1), &local(0));
            mov(o, R1, &local(0));
            rem_const(o, R1, 10);
            eq_const(o, R1, 3);
            begin_if(o, R1);
            mov(o, R1, &R5.deref());
            mul_const(o, R1, 3);
            and_const(o, R1, 0xffff);
            mov(o, &R5.deref(), R1);
            end_if(o);
            // the caller's cell, through the pointer it gave
            mov(o, R2, &local(2));
            mov(o, R3, &R2.deref());
            inc(o, R3);
            mov(o, &R2.deref(), R3);
            inc(o, &local(0));
        });
        mov(o, R0, &local(1));
        end_func(o);
        heap_alloc_const(o, R6, 1);
        set(o, &R6.deref(), 1000);
        call(o, "f", &[R6]);
        putint(o, R0);
        puts(o, " ");
        putint(o, &R6.deref());
        puts(o, "\n");
        // and the pointer it gives is to its own frame (the caller's local)
        begin_func(o, "g", 1);
        set(o, &local(0), 5);
        addr_of(o, R6, &local(0));
        call(o, "f", &[R6]);
        mov(o, R1, R0);
        add_assign(o, R1, &local(0));
        mov(o, R0, R1);
        end_func(o);
        call(o, "g", &[]);
        putint(o, R0);
        puts(o, "\n");
    });
    check("locals", &ops, b"");
}

#[test]
fn loops_inside_loops_summed_up() {
    // rows of 50 (more than the analysis follows a time round at a time):
    // each row of b from the same row of a, in parallel, row by row; then
    // rows that overlap the next (which stay in order)
    let ops = program(|o| {
        let (a, b, i, j, t, at) = (R1, R2, R3, R4, R5, R6);
        heap_alloc_const(o, a, 3100);
        heap_alloc_const(o, b, 3100);
        set(o, i, 0);
        while_loop(o, R0, |o| { mov(o, R0, i); lt_const(o, R0, 3100); }, |o| {
            mov(o, t, i);
            mul_const(o, t, 7);
            rem_const(o, t, 23);
            store_index(o, a, i, t);
            store_index(o, b, i, t);
            inc(o, i);
        });
        for (width, row) in [(50, 50), (50, 40)] {
            set(o, i, 0);
            while_loop(o, R9, |o| { mov(o, R9, i); lt_const(o, R9, 60); }, |o| {
                set(o, j, 0);
                while_loop(o, R0, |o| { mov(o, R0, j); lt_const(o, R0, width); }, |o| {
                    mov(o, at, i);
                    mul_const(o, at, row);
                    add_assign(o, at, j);
                    load_index(o, t, a, at);
                    add_assign(o, t, t);
                    add_assign(o, t, j);
                    load_index(o, R7, b, at);
                    add_assign(o, t, R7);
                    and_const(o, t, 0xffff);
                    store_index(o, b, at, t);
                    inc(o, j);
                });
                inc(o, i);
            });
        }
        set(o, t, 0);
        set(o, i, 0);
        while_loop(o, R0, |o| { mov(o, R0, i); lt_const(o, R0, 3100); }, |o| {
            load_index(o, at, b, i);
            mov(o, j, i);
            rem_const(o, j, 9);
            inc(o, j);
            mul_assign(o, at, j);
            add_assign(o, t, at);
            inc(o, i);
        });
        putint(o, t);
        puts(o, "\n");
    });
    let stats = check("summed_up", &ops, b"");
    // (the outer loop, 60 rows, runs in parallel)
    assert!(stats.iter().any(|s| s.1 && s.2 >= 50 && s.2 < 70), "{stats:?}");
}

#[test]
fn sums_and_maximums_over_loops_inside_loops() {
    // over rows of 60 (summed up), a total, and the largest, in a register
    // and in memory: the rows' loop is a sum and a maximum of them
    let ops = program(|o| {
        let (a, i, j, t, at, total, best) = (R1, R2, R3, R4, R5, R6, R7);
        heap_alloc_const(o, a, 3000);
        heap_alloc_const(o, R9, 2);
        set(o, i, 0);
        while_loop(o, R0, |o| { mov(o, R0, i); lt_const(o, R0, 3000); }, |o| {
            mov(o, t, i);
            mul_const(o, t, 37);
            rem_const(o, t, 1009);
            store_index(o, a, i, t);
            inc(o, i);
        });
        set(o, total, 5);
        set_int(o, best, -1);
        set_int(o, &R9.deref(), -7);
        set(o, i, 0);
        while_loop(o, R8, |o| { mov(o, R8, i); lt_const(o, R8, 50); }, |o| {
            set(o, j, 0);
            while_loop(o, R0, |o| { mov(o, R0, j); lt_const(o, R0, 60); }, |o| {
                mov(o, at, i);
                mul_const(o, at, 60);
                add_assign(o, at, j);
                load_index(o, t, a, at);
                add_assign(o, total, t);
                max_assign(o, best, t);
                sub_assign(o, t, j);
                max_assign(o, &R9.deref(), t);
                inc(o, j);
            });
            inc(o, i);
        });
        for x in [total, best] {
            putint(o, x);
            puts(o, " ");
        }
        putint(o, &R9.deref());
        puts(o, "\n");
    });
    let stats = check("summed_sums", &ops, b"");
    // (the rows' loop, 50 of them, runs in parallel)
    assert!(stats.iter().any(|s| s.1 && s.2 >= 40 && s.2 < 60), "{stats:?}");
}
