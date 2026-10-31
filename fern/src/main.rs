//! The `fern` command: compiles a program to a C file and a binary (or
//! prints it in some form, or tests the samples). See lib.rs for the
//! compiler. The options for the C, the memory and the passes are `bf`'s
//! too, meaning the same (`bf::backends::cli`).
//!
//! ```text
//! fern FILE.fern                    # FILE.c, and the binary FILE (debug: quick to build)
//! fern FILE.fern --release          # optimized
//! fern FILE.fern --run              # and run it
//! fern FILE.fern --emit ops         # the VM's ops, for `bf`
//! fern FILE.fern --emit c           # just the C
//! fern FILE.fern --interpret        # run it on the VM's interpreter
//! fern FILE.fern --release --disable inline,promote   # without those passes (see --passes)
//! fern FILE.fern -vv                # what compiling spends its time on
//! fern --test [DIR]                 # each DIR/*.fern (the samples) against its `// expect:`s
//! ```

use bf::backends::cli::{passes_help, Options};
use bf::backends::CBackend;
use bf::ir::{Mode, Passes};
use clap::{Parser, ValueEnum};
use fern::{build, compile};
use std::io::Read;
use std::path::{Path, PathBuf};
use std::process::exit;

/// Compiles fern programs to native code: to the bf VM's ops, then C
#[derive(Parser)]
#[command(name = "fern", version)]
struct Cli {
    /// The program (FILE.fern); with --test, a folder of them [default: the samples]
    file: Option<PathBuf>,
    /// Optimize: every pass (and the C compiler's -O3)
    #[arg(long, conflicts_with = "debug")]
    release: bool,
    /// Don't optimize: quicker to build (the default; with --test, test only this way)
    #[arg(long)]
    debug: bool,
    /// The binary's name [default: FILE's]; with --emit c, the file (or with --units, the folder)
    #[arg(short, long, value_name = "NAME")]
    output: Option<PathBuf>,
    /// Run it once it's built
    #[arg(long)]
    run: bool,
    /// Print the program in this form, instead of building it
    #[arg(long, value_enum, conflicts_with_all = ["run", "test"])]
    emit: Option<Emit>,
    /// Run it on the VM's interpreter, instead of building it (it can't call C)
    #[arg(long, conflicts_with_all = ["run", "emit"])]
    interpret: bool,
    /// Test each .fern file in the folder against its `// expect:` lines (built both ways, unless --release or --debug says)
    #[arg(long)]
    test: bool,
    #[command(flatten)]
    options: Options,
    /// For the C compiler: the C of `extern fn`s, libraries, ... (a program's own C, it names in `// links: FILE.c` lines)
    #[arg(last = true, value_name = "CC ARGS")]
    cc_args: Vec<String>,
}

#[derive(Clone, Copy, PartialEq, Eq, ValueEnum)]
enum Emit {
    /// The C that's built
    C,
    /// The VM's ops (for `bf`)
    Ops,
    /// The IR, after the optimizer's passes
    Ir,
    /// The program after type checking
    Core,
}

fn fail(e: impl std::fmt::Display) -> ! {
    eprintln!("{e}");
    exit(1)
}

fn main() {
    let cli = Cli::parse();
    cli.options.log();
    if cli.options.passes {
        print!("{}", passes_help(true));
        return;
    }
    let c = fern::backend(cli.options.c().unwrap_or_else(|e| fail(e)));
    if cli.test {
        let dir = cli.file.clone().unwrap_or_else(|| PathBuf::from(concat!(env!("CARGO_MANIFEST_DIR"), "/samples")));
        // (both ways, unless one's asked for: a program has to print the
        // same either way)
        let modes = match (cli.release, cli.debug) {
            (true, _) => vec![Mode::Release],
            (_, true) => vec![Mode::Debug],
            _ => vec![Mode::Debug, Mode::Release],
        };
        exit(run_tests(&dir, &modes, &cli, &c));
    }
    let Some(path) = &cli.file else { fail("fern: no program given (see fern --help)") };
    let path = path.to_string_lossy().to_string();
    let mode = if cli.release { Mode::Release } else { Mode::Debug };
    let (mut program, core) = compile(&path).unwrap_or_else(|e| fail(e));
    for w in fern::warnings(&core) {
        eprintln!("{w}");
    }
    // (`asm-opt` is for ops the VM runs: here, only when interpreting; ops
    // printed are the ones fern makes C of, which is better without it)
    program.set_mode(mode);
    program.set_passes(passes(&cli.options, mode, !cli.interpret));
    // (a failed check, or `panic`, stops it with a status of 1)
    program.set_exits(true);
    // (the memory: as the program has it on the interpreter, unless
    // --memory says; natively, as --memory says)
    if !cli.interpret || cli.options.memory.is_some() {
        program.set_cells(cli.options.cells());
    }
    match cli.emit {
        Some(Emit::Ir) => println!("{}", program.ir().1),
        Some(Emit::C) => {
            // (in one file, to stdout or -o; or with --units, in that many,
            // in the folder -o says)
            let files = bf::backends::cli::c_files(&c.source(&program.compile()), program.cells(), cli.options.units, c.parallel());
            match (&cli.output, files.as_slice()) {
                (None, [one]) => print!("{one}"),
                (Some(file), [one]) => std::fs::write(file, one).unwrap_or_else(|e| fail(format!("{}: {e}", file.display()))),
                (None, _) => fail("--units needs -o, a folder for the files"),
                (Some(dir), many) => {
                    std::fs::create_dir_all(dir).unwrap_or_else(|e| fail(format!("{}: {e}", dir.display())));
                    for (k, file) in many.iter().enumerate() {
                        std::fs::write(dir.join(format!("part{k}.c")), file).unwrap_or_else(|e| fail(e));
                    }
                    eprintln!("wrote {} files to {} (compile them at once, and link them together)", many.len(), dir.display());
                }
            }
        }
        Some(Emit::Ops) => println!("{}", bf::asm::to_source(&program.compile())),
        Some(Emit::Core) => {
            for f in &core.funcs {
                println!("fn {}({}) =\n  {:?}\n", f.name, f.params.join(", "), f.body);
            }
        }
        None if cli.interpret => {
            // (on the VM's own interpreter, which can't call C)
            if let Some((name, _)) = core.externs.first() {
                fail(format!("this program calls C (extern fn {name}), which the interpreter can't"));
            }
            let mut input = vec![];
            if core.reads_input {
                std::io::stdin().read_to_end(&mut input).unwrap();
            }
            let (out, status) = program.run_status(&input);
            print!("{out}");
            if status != 0 {
                exit(status as i32);
            }
        }
        None => {
            // a C file and a binary, named for the program (or -o)
            let binary = cli.output.clone().unwrap_or_else(|| PathBuf::from(Path::new(&path).file_stem().unwrap()));
            let c_file = binary.with_extension("c");
            // (with the program's own C, which it names in `// links: FILE.c`
            // lines, relative to its folder: unless that's given already)
            let mut cc_args = cli.cc_args.clone();
            let same = |a: &Path, b: &str| a.canonicalize().ok().is_some_and(|a| Path::new(b).canonicalize().ok() == Some(a));
            for file in fern::links(&path) {
                if !cc_args.iter().any(|a| same(&file, a)) {
                    cc_args.push(file.display().to_string());
                }
            }
            build(&program, mode, &c, cli.options.units, &c_file, &binary, &cc_args).unwrap_or_else(|e| fail(e));
            if cli.run {
                let target = if binary.is_absolute() || binary.components().count() > 1 { binary.clone() } else { Path::new(".").join(&binary) };
                let status = std::process::Command::new(&target).status().unwrap_or_else(|e| fail(format!("{}: {e}", target.display())));
                exit(status.code().unwrap_or(1));
            }
            eprintln!("built {} (and {})", binary.display(), c_file.display());
        }
    }
}

/// The passes, as the mode has them (all, or none), less `asm-opt` unless
/// the VM runs the ops (C is better without it), with what --enable and
/// --disable say.
fn passes(options: &Options, mode: Mode, not_run: bool) -> Passes {
    let mut preset = if mode == Mode::Release { Passes::all() } else { Passes::none() };
    if not_run {
        let _ = preset.set("asm-opt", false);
    }
    options.ir_passes(preset).unwrap_or_else(|e| fail(e))
}

/// Runs every `.fern` file in `dir`, each on a thread of its own: each
/// prints what its `// expect: ...` lines say (in order), or fails to
/// compile with an error containing its `// error: ...`. The number of
/// failures.
fn run_tests(dir: &Path, modes: &[Mode], cli: &Cli, c: &CBackend) -> i32 {
    let mut paths: Vec<_> = std::fs::read_dir(dir).unwrap_or_else(|e| fail(format!("{}: {e}", dir.display()))).filter_map(|e| e.ok()).map(|e| e.path()).filter(|p| p.extension().is_some_and(|x| x == "fern")).collect();
    paths.sort();
    let results: Vec<(String, Result<(), String>, std::time::Duration)> = std::thread::scope(|s| {
        let handles: Vec<_> = paths.iter().flat_map(|path| modes.iter().map(move |&m| (path, m))).map(|(path, m)| s.spawn(move || test_one(path, m, cli, c))).collect();
        handles.into_iter().map(|h| h.join().unwrap()).collect()
    });
    let mut failures = 0;
    for (name, outcome, time) in results {
        match outcome {
            Ok(()) => println!("ok   {name} ({:.1}s)", time.as_secs_f64()),
            Err(why) => {
                failures += 1;
                println!("FAIL {name}\n{why}");
            }
        }
    }
    println!("{} failed", failures);
    failures
}

/// One sample, built and run (as a binary, or with --interpret, on the
/// VM's interpreter).
fn test_one(path: &Path, mode: Mode, cli: &Cli, c: &CBackend) -> (String, Result<(), String>, std::time::Duration) {
    let vm = cli.interpret;
    let src = std::fs::read_to_string(path).unwrap();
    let expect: Vec<&str> = src.lines().filter_map(|l| l.trim_start().strip_prefix("// expect: ")).collect();
    let error = src.lines().find_map(|l| l.trim().strip_prefix("// error: "));
    let file = path.display().to_string();
    let name = format!("{file} ({})", if mode == Mode::Release { "release" } else { "debug" });
    let start = std::time::Instant::now();
    let outcome = match compile(&file) {
        Ok((mut program, _)) => {
            program.set_mode(mode);
            program.set_passes(passes(&cli.options, mode, !vm));
            program.set_exits(true);
            if !vm || cli.options.memory.is_some() {
                program.set_cells(cli.options.cells());
            }
            if let Some(e) = error {
                Err(format!("compiled, but should fail with: {e}"))
            } else {
                let got = if vm { Ok(program.run(b"")) } else { run_native(&program, mode, c, path) };
                let got = match got {
                    Ok(g) => g,
                    Err(e) => return (name, Err(e), start.elapsed()),
                };
                let want = expect.iter().map(|l| format!("{l}\n")).collect::<String>();
                if got == want { Ok(()) } else { Err(format!("printed:\n{got}\nexpected:\n{want}")) }
            }
        }
        Err(msg) => match error {
            Some(e) if msg.contains(e) => Ok(()),
            _ => Err(msg),
        },
    };
    (name, outcome, start.elapsed())
}

/// What a program prints, built and run as a binary (in a directory of its
/// own, gone after).
fn run_native(program: &bf::ir::Program, mode: Mode, c: &CBackend, path: &Path) -> Result<String, String> {
    static RUNS: std::sync::atomic::AtomicUsize = std::sync::atomic::AtomicUsize::new(0);
    let n = RUNS.fetch_add(1, std::sync::atomic::Ordering::Relaxed);
    let dir = std::env::temp_dir().join(format!("fern-test-{}-{n}", std::process::id()));
    std::fs::create_dir_all(&dir).map_err(|e| e.to_string())?;
    let stem = path.file_stem().unwrap().to_string_lossy().to_string();
    let binary = dir.join(&stem);
    let result = build(program, mode, c, None, &dir.join(format!("{stem}.c")), &binary, &[]).and_then(|()| {
        let out = std::process::Command::new(&binary).stdin(std::process::Stdio::null()).output().map_err(|e| e.to_string())?;
        Ok(String::from_utf8_lossy(&out.stdout).into_owned())
    });
    let _ = std::fs::remove_dir_all(&dir);
    result
}
