//! The `bf` command: the VM's ops (a program in the VM's language) as C, as
//! machine code for the CPU in hw/, or run on the VM's interpreter.
//!
//! ```text
//! bf FILE.bf > FILE.c                      # C, the optimizing backend's
//! bf FILE.bf --backend literal > FILE.c    # each op as C, to check against
//! bf FILE.bf --parallel > FILE.c           # loops in parallel (cc -fopenmp)
//! bf FILE.bf --units 8 -o parts/           # in 8 files, to compile at once
//! bf FILE.bf --emit hex --xlen 16          # machine code for a 16-bit CPU
//! bf FILE.bf --interpret < input           # run it on the VM's interpreter
//! ```

use bf::backends::cli::{c_files, passes_help, Options};
use bf::interp::Machine;
use bf::{asm, cpu, parse};
use clap::{Parser, ValueEnum};
use std::io::Read;
use std::path::PathBuf;
use std::process::exit;

/// Compiles the VM's ops to C (or machine code), or runs them
#[derive(Parser)]
#[command(name = "bf", version)]
struct Cli {
    /// The program: the VM's ops
    file: Option<PathBuf>,
    /// What to make of it, on stdout
    #[arg(long, value_enum, default_value_t = Emit::C)]
    emit: Emit,
    /// The CPU's cell width in bits, 16 to 64, for --emit hex
    #[arg(long, default_value_t = 64, value_name = "BITS")]
    xlen: u32,
    /// Run it on the VM's interpreter instead (input from stdin)
    #[arg(long)]
    interpret: bool,
    /// Where to write it [default: stdout]; with --units, a folder for the files
    #[arg(short, long, value_name = "PATH")]
    output: Option<PathBuf>,
    #[command(flatten)]
    options: Options,
}

#[derive(Clone, Copy, PartialEq, Eq, ValueEnum)]
enum Emit {
    /// C, with the backend --backend says
    C,
    /// Machine code for the CPU in hw/ ($readmemh format)
    Hex,
}

fn main() {
    let cli = Cli::parse();
    cli.options.log();
    if cli.options.passes {
        print!("{}", passes_help(false));
        return;
    }
    let Some(path) = &cli.file else {
        eprintln!("bf: no program given (see bf --help)");
        exit(2);
    };
    let fail = |e: String| -> ! {
        eprintln!("bf: {e}");
        exit(1)
    };
    let text = std::fs::read_to_string(path).unwrap_or_else(|e| fail(format!("{}: {e}", path.display())));
    let mut p = asm::log::phase(asm::log::INFO, "parse");
    let ops = parse(&text).unwrap_or_else(|()| fail(format!("{}: not the VM's ops", path.display())));
    p.done(format!("{} ops", ops.len()));
    drop(p);
    // (the ops' own optimizer, only if asked: the input is ops already made;
    // the IR optimizer's passes are for what makes ops, like fern)
    let ir_pass = |n: &String| n == "ir" || bf::ir::PASSES.iter().any(|(p, _)| p == n && *p != "asm-opt");
    if let Some(n) = cli.options.enable.iter().chain(&cli.options.disable).find(|n| ir_pass(n)) {
        fail(format!("`{n}` is one of the IR optimizer's passes, and bf takes ops (see bf --passes)"));
    }
    let passes = cli.options.ir_passes(bf::ir::Passes::none()).unwrap_or_else(|e| fail(e));
    let ops = if passes.on("asm-opt") { asm::opt_fast(ops) } else { ops };
    if cli.interpret {
        let mut input = vec![];
        let _ = std::io::stdin().read_to_end(&mut input);
        let machine = Machine { cells: cli.options.cells() as usize + 64, max_steps: u64::MAX, ..Machine::c() };
        let out = machine.run(&ops, &input).unwrap_or_else(|e| fail(e.to_string()));
        print!("{}", String::from_utf8_lossy(&out.output));
        return;
    }
    match cli.emit {
        Emit::Hex => match cpu::assemble(&ops, cli.xlen) {
            Ok(code) => print!("{}", cpu::to_hex(&code)),
            Err(e) => fail(e.to_string()),
        },
        Emit::C => {
            let c = cli.options.c().unwrap_or_else(|e| fail(e));
            // (with the tape as big as the program was made for: see --memory)
            let files = c_files(&c.source(&ops), cli.options.cells(), cli.options.units, c.parallel());
            match (&cli.output, files.as_slice()) {
                (None, [one]) => print!("{one}"),
                (Some(file), [one]) => std::fs::write(file, one).unwrap_or_else(|e| fail(format!("{}: {e}", file.display()))),
                (None, _) => fail("--units needs -o, a folder for the files".into()),
                (Some(dir), many) => {
                    std::fs::create_dir_all(dir).unwrap_or_else(|e| fail(format!("{}: {e}", dir.display())));
                    for (k, file) in many.iter().enumerate() {
                        let path = dir.join(format!("part{k}.c"));
                        std::fs::write(&path, file).unwrap_or_else(|e| fail(format!("{}: {e}", path.display())));
                    }
                    eprintln!("wrote {} files to {} (compile them at once, and link them together)", many.len(), dir.display());
                }
            }
        }
    }
}
