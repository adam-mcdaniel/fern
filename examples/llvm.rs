//! What LLVM's optimizer makes of these compilers' output.
//!
//! Each program (the IR benchmarks, and the DOT examples) goes to LLVM IR
//! three ways:
//!
//! - **vm**: optimized by the IR's optimizer, lowered to VM ops, and the VM
//!   program translated to LLVM IR (`asm::llvm`), so LLVM sees what the VM
//!   would run;
//! - **ir**: the IR as built, translated directly (`asm::ir::llvm`), so LLVM
//!   does all the optimizing;
//! - **ir+opt**: the IR after the IR's own optimizer, translated directly.
//!
//! Native code from the IR uses the garbage collector in `llvm::RUNTIME`, as
//! the VM program uses the IR's own, so both free what they're done with.
//!
//! For each, it reports the LLVM instructions before and after `opt -O3`,
//! the size of the native code `llc -O3` makes of it, and how long the
//! program takes to run natively (built with `llvm::OPTIMIZE`'s flags),
//! after checking that it prints the same as the IR interpreter. Needs LLVM's tools (`opt`, `llc`, `clang`,
//! `llvm-size`) on the PATH, or in `$LLVM_BIN`.
//!
//! ```text
//! cargo run --release --example llvm
//! ```

#[path = "common/programs.rs"]
mod programs;

use bf::asm::ir::{dot, llvm, lower, lower_with, optimize, run, Module, Options};
use bf::interp::Machine;
use std::path::{Path, PathBuf};
use std::process::{Command, Stdio};
use std::time::{Duration, Instant};

fn tool(name: &str) -> PathBuf {
    if let Ok(dir) = std::env::var("LLVM_BIN") {
        return Path::new(&dir).join(name);
    }
    for dir in ["/opt/homebrew/opt/llvm/bin", "/usr/local/opt/llvm/bin"] {
        let p = Path::new(dir).join(name);
        if p.exists() {
            return p;
        }
    }
    PathBuf::from(name)
}

fn sh(cmd: &mut Command) -> String {
    let out = cmd.output().unwrap_or_else(|e| panic!("{cmd:?}: {e}"));
    if !out.status.success() {
        panic!("{cmd:?} failed:\n{}", String::from_utf8_lossy(&out.stderr));
    }
    String::from_utf8_lossy(&out.stdout).to_string()
}

/// How many instructions an LLVM IR file has.
fn instructions(ll: &str) -> usize {
    let mut inside = false;
    let mut count = 0;
    for line in ll.lines() {
        if line.starts_with("define") {
            inside = true;
        } else if line.starts_with('}') {
            inside = false;
        } else if inside && line.starts_with("  ") && !line.trim_start().starts_with(';') {
            count += 1;
        }
    }
    count
}

struct Measured {
    before: usize,
    after: usize,
    bytes: usize,
    time: Duration,
}

/// Optimizes, compiles and runs one LLVM IR file, checking its output.
fn measure(dir: &Path, name: &str, ll: &str, input: &[u8], want: &[u8]) -> Measured {
    measure_runs(dir, name, ll, input, want, 5)
}

fn measure_runs(dir: &Path, name: &str, ll: &str, input: &[u8], want: &[u8], runs: usize) -> Measured {
    let src = dir.join(format!("{name}.ll"));
    std::fs::write(&src, ll).unwrap();
    let opt = dir.join(format!("{name}.opt.ll"));
    sh(Command::new(tool("opt")).args(["-O3", "-S", "-o"]).arg(&opt).arg(&src));
    let optimized = std::fs::read_to_string(&opt).unwrap();
    let obj = dir.join(format!("{name}.o"));
    sh(Command::new(tool("llc")).args(["-O3", "-filetype=obj", "-o"]).arg(&obj).arg(&opt));
    let sizes = sh(Command::new(tool("llvm-size")).arg(&obj));
    let bytes = sizes.lines().nth(1).and_then(|l| l.split_whitespace().next()).and_then(|n| n.parse().ok()).unwrap_or(0);
    let exe = dir.join(name);
    let runtime = dir.join("runtime.c");
    std::fs::write(&runtime, llvm::RUNTIME).unwrap();
    sh(Command::new(tool("clang")).args(llvm::OPTIMIZE).args(["-w", "-o"]).arg(&exe).arg(&opt).arg(&runtime));
    let mut best = Duration::MAX;
    for _ in 0..runs {
        let start = Instant::now();
        let mut child = Command::new(&exe).stdin(Stdio::piped()).stdout(Stdio::piped()).spawn().unwrap();
        use std::io::Write;
        child.stdin.take().unwrap().write_all(input).unwrap();
        let out = child.wait_with_output().unwrap();
        best = best.min(start.elapsed());
        assert_eq!(String::from_utf8_lossy(&out.stdout), String::from_utf8_lossy(want), "{name} printed something else");
    }
    Measured { before: instructions(ll), after: instructions(&optimized), bytes, time: best }
}

fn main() {
    let dir = std::env::temp_dir().join("bf-llvm");
    std::fs::create_dir_all(&dir).unwrap();
    let mut all: Vec<(String, Module, Vec<u8>)> =
        programs::all().into_iter().map(|(n, m, i)| (n.to_string(), m, i.to_vec())).collect();
    let mut compiler = dot::Compiler::new();
    compiler.dir("examples/dot");
    for (name, input) in [("hello", ""), ("lists", ""), ("strings", "hello world\nthe quick brown fox\n\n"), ("trees", "")] {
        let src = std::fs::read_to_string(format!("examples/dot/{name}.dot")).unwrap();
        let m = compiler.compile(&src).unwrap_or_else(|e| panic!("{name}: {e}"));
        all.push((format!("dot:{name}"), m, input.as_bytes().to_vec()));
    }

    println!("{:13} {:>9} {:>9} | {:>27} | {:>27} | {:>27}", "", "VM", "", "vm -> LLVM", "ir -> LLVM", "ir+opt -> LLVM");
    println!(
        "{:13} {:>9} {:>9} | {:>6} {:>6} {:>6} {:>7} | {:>6} {:>6} {:>6} {:>7} | {:>6} {:>6} {:>6} {:>7}",
        "program", "ops", "steps", "insts", "-O3", "bytes", "time", "insts", "-O3", "bytes", "time", "insts", "-O3", "bytes", "time"
    );
    for (name, m, input) in all {
        let want = run(&m, &input, 64).unwrap();
        let mut optimized = m.clone();
        optimize(&mut optimized);
        let ops = lower(&optimized).unwrap();
        let halted = Machine::c().run(&ops, &input).unwrap();
        assert_eq!(halted.output, want, "{name} on the VM");
        let file = name.replace(':', "_");
        let vm = measure(&dir, &format!("{file}.vm"), &bf::asm::llvm::emit(&ops, 1 << 16), &input, &want);
        let ir = measure(&dir, &format!("{file}.ir"), &llvm::emit(&m).unwrap(), &input, &want);
        let iro = measure(&dir, &format!("{file}.iro"), &llvm::emit(&optimized).unwrap(), &input, &want);
        let row = |r: &Measured| format!("{:>6} {:>6} {:>6} {:>5}us", r.before, r.after, r.bytes, r.time.as_micros());
        println!("{name:13} {:>9} {:>9} | {} | {} | {}", ops.len(), halted.steps, row(&vm), row(&ir), row(&iro));
    }

    // programs that run long enough for the time natively to mean something
    // (the ones above mostly measure starting a process): each is checked
    // against the same program compiled the other way
    println!("\nrunning time, natively, of longer programs (best of 3)");
    println!("{:24} {:>12} {:>12} {:>12} {:>12}", "program", "vm, no opt", "vm -> LLVM", "ir -> LLVM", "ir+opt");
    let trees = std::fs::read_to_string("examples/dot/trees.dot").unwrap().replace("rounds(12, 0)", "rounds(3000, 0)");
    let heavy: Vec<(&str, Module)> = vec![
        ("fib(0..32)", programs::fib_upto(32)),
        ("dot:trees, 3000 rounds", compiler.compile(&trees).unwrap()),
    ];
    for (name, m) in heavy {
        let mut optimized = m.clone();
        optimize(&mut optimized);
        let file = name.replace([':', ' ', ',', '(', ')', '.'], "_");
        // the reference output: the IR compiled directly
        let ll = llvm::emit(&m).unwrap();
        let src = dir.join(format!("{file}.ref.ll"));
        std::fs::write(&src, &ll).unwrap();
        let exe = dir.join(format!("{file}.ref"));
        sh(Command::new(tool("clang")).args(llvm::OPTIMIZE).args(["-w", "-o"]).arg(&exe).arg(&src).arg(dir.join("runtime.c")));
        let want = Command::new(&exe).output().unwrap().stdout;
        let ops = lower(&optimized).unwrap();
        // the VM program without `asm::opt`, for comparison
        let plain = lower_with(&optimized, &Options { optimize: false, ..Options::default() }).unwrap();
        let raw = measure_runs(&dir, &format!("{file}.raw"), &bf::asm::llvm::emit(&plain, 1 << 16), b"", &want, 3);
        let vm = measure_runs(&dir, &format!("{file}.vm"), &bf::asm::llvm::emit(&ops, 1 << 16), b"", &want, 3);
        let ir = measure_runs(&dir, &format!("{file}.ir"), &ll, b"", &want, 3);
        let iro = measure_runs(&dir, &format!("{file}.iro"), &llvm::emit(&optimized).unwrap(), b"", &want, 3);
        let ms = |r: &Measured| format!("{:.1} ms", r.time.as_secs_f64() * 1000.0);
        println!("{name:24} {:>12} {:>12} {:>12} {:>12}", ms(&raw), ms(&vm), ms(&ir), ms(&iro));
    }
}
