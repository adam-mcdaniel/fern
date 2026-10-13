//! Compiles a program in the DOT language (see `bf::asm::ir::dot`).
//!
//! ```text
//! cargo run --example dot -- FILE.dot [--run] [--check] [--ir] [--raw]
//!                                     [--xlen BITS] [--cells N] [--no-checks]
//!                                     [--c] [--llvm] [--build EXE [FILE.c...] [--via-c]
//!                                     [--pgo [--train INPUT]]]
//! ```
//!
//! By default prints the compiled program as source for the VM. `--run` runs
//! it instead, on standard input, with the CPU's addresses and `--xlen`-bit
//! cells (64 by default); `--check` only prints the program's type; `--ir`
//! prints the optimized IR, and `--raw` the IR as generated. `--no-checks`
//! leaves out the checks that stop the program when the stack runs into the
//! heap.
//!
//! To call C (`extern def`: C functions `void name(int64_t **tape,
//! int64_t **ptr, int64_t *acc)`, as the VM calls them), build natively:
//! `--build EXE` compiles the program with clang, linking in the C files
//! given, through the IR's LLVM backend, or with `--via-c`, as the VM
//! program through the C backend.
//! `--c` and `--llvm` print what those compile. C files can include
//! `dot.h` (with `DOT_EXTERN`, which writes such a function around a plain
//! C one) and `bf.h`, which are put where clang finds them. Builds are optimized with
//! LTO across the program, its runtime and the C files, for the machine
//! they're built on, with more inlining and LLVM's optional passes on; with
//! `--pgo`, they're also optimized for a profile of a run on `--train`'s
//! input (or none).

use bf::asm::ir::{dot, llvm, lower_with, optimize, Options};
use bf::asm::to_source;
use bf::interp::Machine;
use std::io::Read;
use std::process::exit;

fn main() {
    let args: Vec<String> = std::env::args().skip(1).collect();
    let flag = |f: &str| args.iter().any(|a| a == f);
    let value = |f: &str| args.iter().position(|a| a == f).and_then(|i| args.get(i + 1)).map(|v| v.parse::<u64>().expect("expected a number"));
    let Some(path) = args.iter().find(|a| a.ends_with(".dot")) else {
        eprintln!("usage: dot FILE.dot [--run] [--check] [--ir] [--raw] [--xlen BITS] [--cells N] [--no-checks]");
        exit(2);
    };
    let src = std::fs::read_to_string(path).unwrap_or_else(|e| {
        eprintln!("{path}: {e}");
        exit(1);
    });
    // modules are looked for next to the program, as well as in the
    // standard library
    let mut compiler = dot::Compiler::new();
    if let Some(dir) = std::path::Path::new(path).parent() {
        compiler.dir(dir);
    }
    let checked = compiler.check(&src).unwrap_or_else(|e| {
        eprintln!("{path}:{e}");
        exit(1);
    });
    if flag("--check") {
        println!("{}", checked.type_string());
        return;
    }
    let mut module = checked.compile(16);
    if flag("--llvm") || (flag("--build") && !flag("--via-c")) {
        optimize(&mut module);
        let ll = llvm::emit(&module).unwrap_or_else(|e| {
            eprintln!("{path}: {e}");
            exit(1);
        });
        if flag("--llvm") {
            print!("{ll}");
        } else {
            build(&args, "program.ll", &ll, true);
        }
        return;
    }
    if flag("--raw") {
        print!("{module}");
        return;
    }
    optimize(&mut module);
    if flag("--ir") {
        print!("{module}");
        return;
    }
    // the C backend's tape has 100000 cells
    let tape = if flag("--c") || flag("--build") { 100_000 } else { Options::default().cells };
    let options = Options {
        cells: value("--cells").unwrap_or(tape),
        checks: !flag("--no-checks"),
        optimize: !flag("--no-opt"),
    };
    let ops = lower_with(&module, &options).unwrap_or_else(|e| {
        eprintln!("{path}: {e}");
        exit(1);
    });
    if flag("--c") || flag("--build") {
        let c = bf::compile(&ops);
        if flag("--c") {
            print!("{c}");
        } else {
            build(&args, "program.c", &c, false);
        }
        return;
    }
    if !flag("--run") {
        print!("{}", to_source(&ops));
        return;
    }
    let mut input = vec![];
    std::io::stdin().read_to_end(&mut input).unwrap();
    let mut machine = Machine::cpu_xlen(value("--xlen").unwrap_or(64) as u32);
    machine.cells = machine.cells.max(options.cells as usize);
    match machine.run(&ops, &input) {
        Ok(halted) => {
            use std::io::Write;
            std::io::stdout().write_all(&halted.output).unwrap();
            eprintln!("({} steps)", halted.steps);
        }
        Err(e) => {
            eprintln!("{e}");
            exit(1);
        }
    }
}

/// Compiles `code` (saved as `file`) natively with clang, linking in the C
/// files on the command line, to the executable after `--build`.
fn build(args: &[String], file: &str, code: &str, runtime: bool) {
    let exe = args.iter().position(|a| a == "--build").and_then(|i| args.get(i + 1)).unwrap_or_else(|| {
        eprintln!("--build needs the executable's name");
        exit(2);
    });
    let dir = std::env::temp_dir().join(format!("dot-build-{}", std::process::id()));
    std::fs::create_dir_all(&dir).unwrap();
    std::fs::write(dir.join(file), code).unwrap();
    std::fs::write(dir.join("dot.h"), dot::C_HEADER).unwrap();
    std::fs::write(dir.join("bf.h"), bf::asm::C_HEADER).unwrap();
    if runtime {
        std::fs::write(dir.join("runtime.c"), llvm::RUNTIME).unwrap();
    }
    let compile = |extra: &[String]| {
        let mut cmd = std::process::Command::new(clang());
        cmd.args(llvm::OPTIMIZE).args(extra).args(["-w", "-o", exe.as_str(), "-I"]).arg(&dir).arg(dir.join(file));
        if runtime {
            cmd.arg(dir.join("runtime.c"));
        }
        cmd.args(args.iter().filter(|a| a.ends_with(".c")));
        let status = cmd.status().unwrap_or_else(|e| {
            eprintln!("couldn't run clang: {e}");
            exit(1);
        });
        if !status.success() {
            exit(1);
        }
    };
    if !args.iter().any(|a| a == "--pgo") {
        return compile(&[]);
    }
    // build it to profile itself, run it, and build it again for the profile
    let profiles = dir.join("profiles");
    compile(&[format!("-fprofile-generate={}", profiles.display())]);
    let input = match args.iter().position(|a| a == "--train").and_then(|i| args.get(i + 1)) {
        Some(f) => std::fs::read(f).unwrap_or_else(|e| {
            eprintln!("{f}: {e}");
            exit(1);
        }),
        None => vec![],
    };
    use std::io::Write;
    let mut run = std::process::Command::new(std::path::Path::new(".").join(exe))
        .stdin(std::process::Stdio::piped())
        .stdout(std::process::Stdio::null())
        .env("LLVM_PROFILE_FILE", profiles.join("run.profraw"))
        .spawn()
        .unwrap_or_else(|e| {
            eprintln!("couldn't run {exe} to profile it: {e}");
            exit(1);
        });
    run.stdin.take().unwrap().write_all(&input).unwrap();
    run.wait().unwrap();
    let data = dir.join("run.profdata");
    let merged = std::process::Command::new(clang().replace("clang", "llvm-profdata"))
        .arg("merge")
        .arg("-o")
        .arg(&data)
        .arg(&profiles)
        .status()
        .is_ok_and(|s| s.success());
    if !merged {
        eprintln!("couldn't merge the profile (llvm-profdata)");
        exit(1);
    }
    compile(&[format!("-fprofile-use={}", data.display())]);
}

/// LLVM's clang, which reads LLVM IR, or else whichever is on the PATH.
fn clang() -> String {
    for dir in ["/opt/homebrew/opt/llvm/bin", "/usr/local/opt/llvm/bin"] {
        let p = format!("{dir}/clang");
        if std::path::Path::new(&p).exists() {
            return p;
        }
    }
    "clang".to_string()
}
