//! What the workloads share: building a program, checking that `ParallelC`
//! makes it print what the same algorithm written in C by hand prints, and
//! how long each takes. With `BF_BENCH` set, the C backend is checked and
//! timed too; with `BF_OPT`, so are the program optimized for speed and for
//! size (`opt_fast`, `opt_size`), through the C backend, with how many ops
//! each has.
//!
//! The VM's cells are integers, so the workloads are in fixed point.

#![allow(dead_code)]

use bf::asm::*;
use bf::backends::{ParallelC, C};
use bf::{Op, Target};
use std::path::{Path, PathBuf};
use std::fmt::Write as _;
use std::process::Command;
use std::time::{Duration, Instant};

/// The cells the tape has (the C backend's).
pub const CELLS: u64 = 100_000;

/// A program: the stack and heap set up, then `build`.
pub fn program(build: impl FnOnce(&mut Vec<Op>)) -> Vec<Op> {
    let mut o = vec![];
    init_with(&mut o, CELLS);
    build(&mut o);
    o
}

/// clang, with OpenMP if it has it.
fn clang() -> Option<(PathBuf, bool)> {
    let dir = std::env::temp_dir().join(format!("bf-workloads-probe-{}", std::process::id()));
    std::fs::create_dir_all(&dir).ok()?;
    let probe = dir.join("probe.c");
    std::fs::write(&probe, "#include <omp.h>\nint main(void) { return omp_get_max_threads() > 0 ? 0 : 1; }\n").ok()?;
    for cc in ["/opt/homebrew/opt/llvm/bin/clang", "clang"] {
        if Command::new(cc).arg("-fopenmp").arg(&probe).arg("-o").arg(dir.join("probe")).output().is_ok_and(|o| o.status.success()) {
            return Some((cc.into(), true));
        }
    }
    Command::new("clang").arg("--version").output().ok().filter(|o| o.status.success()).map(|_| ("clang".into(), false))
}

/// Builds `code` (in `dir`, as `name`), and runs it: the best time of a few
/// runs (fewer if they take long), and what it printed.
fn build_and_run(cc: &Path, dir: &Path, name: &str, code: &str, flags: &[&str]) -> (Duration, String) {
    let src = dir.join(format!("{name}.c"));
    std::fs::write(&src, code).unwrap();
    let exe = dir.join(name);
    let built = Command::new(cc).args(["-O2", "-fwrapv", "-w"]).args(flags).arg("-o").arg(&exe).arg(&src).output().unwrap();
    assert!(built.status.success(), "{name}: {}", String::from_utf8_lossy(&built.stderr));
    let mut best = (Duration::MAX, String::new());
    let mut spent = Duration::ZERO;
    for _ in 0..3 {
        if spent > Duration::from_secs(2) {
            break;
        }
        let start = Instant::now();
        let out = Command::new(&exe).output().unwrap();
        let t = start.elapsed();
        spent += t;
        assert!(out.status.success(), "{name} failed: {}", String::from_utf8_lossy(&out.stderr));
        if t < best.0 {
            best = (t, String::from_utf8_lossy(&out.stdout).into());
        }
    }
    best
}

/// Checks that `ops`, compiled with `ParallelC`, prints what `by_hand` (C)
/// prints, and says how long each took.
pub fn check(name: &str, ops: &[Op], by_hand: &str) {
    let Some((cc, omp)) = clang() else {
        eprintln!("skipped {name}: no C compiler");
        return;
    };
    let dir = std::env::temp_dir().join("bf-workloads").join(name);
    std::fs::create_dir_all(&dir).unwrap();
    std::fs::write(dir.join(format!("{name}.bf")), to_source(ops)).unwrap();
    let start = Instant::now();
    let code = ParallelC::default().compile(ops);
    let compiling = start.elapsed();
    let flags: &[&str] = if omp { &["-fopenmp"] } else { &[] };
    let (par, got) = build_and_run(&cc, &dir, "parallel", &code, flags);
    let (hand, want) = build_and_run(&cc, &dir, "hand", by_hand, &[]);
    assert_eq!(got, want, "{name}: ParallelC prints something else than the C written by hand (see {})", dir.display());
    let ms = |t: Duration| t.as_secs_f64() * 1000.0;
    let mut line = format!("{name}: ParallelC {:.1}ms, by hand {:.1}ms ({:.2}x), compiled in {:.0}ms", ms(par), ms(hand), par.as_secs_f64() / hand.as_secs_f64(), ms(compiling));
    if std::env::var("BF_OPT").is_ok() {
        let (seq, out) = build_and_run(&cc, &dir, "c_backend", &C.compile(ops), &[]);
        assert_eq!(out, want, "{name}: the C backend prints something else");
        let _ = write!(line, "\n  as it is: {} ops, {:.1}ms with the C backend", ops.len(), ms(seq));
        for (goal, optimize) in [("fast", opt_fast as fn(Vec<Op>) -> Vec<Op>), ("size", opt_size)] {
            let start = Instant::now();
            let optimized = optimize(ops.to_vec());
            let took = start.elapsed();
            let (t, out) = build_and_run(&cc, &dir, &format!("opt_{goal}"), &C.compile(&optimized), &[]);
            assert_eq!(out, want, "{name}: optimized for {goal}, it prints something else");
            let (pt, pout) = build_and_run(&cc, &dir, &format!("opt_{goal}_parallel"), &ParallelC::default().compile(&optimized), flags);
            assert_eq!(pout, want, "{name}: optimized for {goal}, with ParallelC, it prints something else");
            let _ = write!(line, "\n  opt_{goal}: {} ops ({:.0}%), {:.1}ms with the C backend, {:.1}ms with ParallelC, optimized in {:.0}ms", optimized.len(), 100.0 * optimized.len() as f64 / ops.len() as f64, ms(t), ms(pt), ms(took));
        }
    }
    if std::env::var("BF_BENCH").is_ok() {
        let (seq, out) = build_and_run(&cc, &dir, "c_backend", &C.compile(ops), &[]);
        assert_eq!(out, want, "{name}: the C backend prints something else");
        line += &format!(", C backend {:.1}ms ({:.1}x faster)", ms(seq), seq.as_secs_f64() / par.as_secs_f64());
    }
    eprintln!("{line}");
}

// Helpers for writing the programs.

/// A cell of the block of globals that `R9` points to.
pub fn g(k: i64) -> Location {
    R9.deref().offset(k)
}

/// `dst = (array k of the globals)[i]`.
pub fn get(o: &mut dyn Program, dst: &Location, array: i64, i: &Location) {
    load_index(o, dst, &g(array), i);
}

/// `(array k of the globals)[i] = src`.
pub fn put(o: &mut dyn Program, array: i64, i: &Location, src: &Location) {
    store_index(o, &g(array), i, src);
}

/// Local `i` of the current function.
pub fn l(i: i64) -> Location {
    local(i)
}

/// Defines `isqrt(n)`: the integer square root of `n >= 0`, into `R0`, a bit
/// at a time.
pub fn isqrt_func(o: &mut dyn Program) {
    begin_func(o, "isqrt", 5);
    mov(o, &l(0), &arg(0));
    set(o, &l(1), 0);
    set_int(o, &l(2), 1 << 62);
    while_loop(o, R0, |o| { mov(o, R0, &l(2)); gt_assign(o, R0, &l(0)); }, |o| rshu_const(o, &l(2), 2));
    while_loop(o, R0, |o| mov(o, R0, &l(2)), |o| {
        mov(o, &l(3), &l(1));
        add_assign(o, &l(3), &l(2));
        mov(o, &l(4), &l(0));
        ge_assign(o, &l(4), &l(3));
        rshu_const(o, &l(1), 1);
        begin_if(o, &l(4));
        sub_assign(o, &l(0), &l(3));
        add_assign(o, &l(1), &l(2));
        end_if(o);
        rshu_const(o, &l(2), 2);
    });
    mov(o, R0, &l(1));
    end_func(o);
}

/// `isqrt` in C.
pub const ISQRT_C: &str = r#"
static int64_t isqrt(int64_t n) {
    int64_t res = 0, bit = (int64_t)1 << 62;
    while (bit > n) bit = (int64_t)((uint64_t)bit >> 2);
    while (bit) {
        int64_t t = res + bit;
        int f = n >= t;
        res = (int64_t)((uint64_t)res >> 1);
        if (f) { n -= t; res += bit; }
        bit = (int64_t)((uint64_t)bit >> 2);
    }
    return res;
}
"#;

/// `x = isqrt(x)`, without functions (uses R5 to R8 and R0).
pub fn isqrt_inline(o: &mut dyn Program, x: &Location) {
    let (res, bit, t) = (R5, R6, R7);
    set(o, res, 0);
    set_int(o, bit, 1 << 62);
    while_loop(o, R0, |o| { mov(o, R0, bit); gt_assign(o, R0, x); }, |o| rshu_const(o, bit, 2));
    while_loop(o, R0, |o| mov(o, R0, bit), |o| {
        mov(o, t, res);
        add_assign(o, t, bit);
        mov(o, R8, x);
        ge_assign(o, R8, t);
        rshu_const(o, res, 1);
        begin_if(o, R8);
        sub_assign(o, x, t);
        add_assign(o, res, bit);
        end_if(o);
        rshu_const(o, bit, 2);
    });
    mov(o, x, res);
}

/// The C programs' common start.
pub const C_HEAD: &str = "#include <stdio.h>\n#include <stdint.h>\n#include <string.h>\n";

/// `x = (x * 1103515245 + 12345) & 0x7fffffff`: a small random number
/// generator.
pub fn lcg(o: &mut dyn Program, x: &Location) {
    mul_const(o, x, 1_103_515_245);
    add_const(o, x, 12345);
    and_const(o, x, 0x7fff_ffff);
}

/// `lcg` in C.
pub const LCG_C: &str = "#define LCG(x) ((x) = ((x) * 1103515245 + 12345) & 0x7fffffff)\n";

/// `while (i < n) { body; i += 1 }`, with `i` set to `from` first, `flag` for
/// the condition.
pub fn for_range(o: &mut dyn Program, i: &Location, from: i64, n: &Location, flag: &Location, body: impl FnOnce(&mut dyn Program)) {
    set_int(o, i, from);
    while_loop(o, flag, |o| { mov(o, flag, i); lt_assign(o, flag, n); }, |o| {
        body(o);
        inc(o, i);
    });
}

/// `for_range` to a constant.
pub fn for_const(o: &mut dyn Program, i: &Location, from: i64, n: i64, flag: &Location, body: impl FnOnce(&mut dyn Program)) {
    set_int(o, i, from);
    while_loop(o, flag, |o| { mov(o, flag, i); lt_const(o, flag, n); }, |o| {
        body(o);
        inc(o, i);
    });
}
