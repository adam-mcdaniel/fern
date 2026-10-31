//! fern: a language with Rust's syntax and an ML's type system, compiled to
//! native code through `bf::ir` (and C). A whole compiler, written to be
//! read. `compile` makes a program's IR; `build` makes it a C file and a
//! binary; the `fern` binary (main.rs) is the command line.
//!
//! The language: `fn`, `struct`, `enum`, `match`, closures, `let mut`,
//! loops, as in Rust; types inferred (Hindley-Milner), with type
//! parameters and annotations where wanted; anonymous records with row
//! polymorphism (`fn get_x(r) { r.x }` takes any record with an `x`);
//! traits, with supertraits, default methods, impls for type
//! constructors and `#[derive(Eq, Ord, Show)]`; algebraic effects and
//! handlers, tracked in types; modules (`mod`, `use`, `pub`), all resolved
//! at compile time. See `samples/` and `std/std.fern`.
//!
//! The stages, a file each:
//!
//! 1. `lexer.rs`, `parser.rs`: text into the syntax tree (`ast.rs`).
//! 2. `modules.rs`: files into modules, and names into what they mean;
//!    `derive.rs` writes `#[derive]`'s impls.
//! 3. `checker.rs`, `expr.rs`, `traits.rs`, `exhaust.rs` (with `types.rs`):
//!    type inference, turning the program into `core.rs`'s language: no
//!    types, traits as dictionaries passed to functions.
//! 4. `cps.rs`: into continuation-passing style, which is what lets effect
//!    handlers capture "the rest of the computation" as `resume`; but only
//!    code that may perform operations, as its types say (see `direct.rs`):
//!    the rest is compiled as ordinary functions.
//! 5. `codegen.rs`: closures into blocks, and the whole into a `bf::ir::Program`,
//!    which the IR's optimizer and lowering make into VM ops.

mod ast;
mod checker;
mod codegen;
pub mod core;
mod cps;
mod derive;
mod direct;
mod exhaust;
mod expr;
mod lexer;
mod modules;
mod parser;
mod traits;
mod types;
mod wrappers;

use lexer::Pos;

use bf::backends::CBackend;
use bf::ir::Mode;
use bf::asm::fx::HashMap;

/// The memory a native program may use, its stack and heap, in cells (8
/// bytes each): 1 GB, about as much as the collector can keep track of. It's
/// a ceiling, not what's used: the heap collects when it's grown to twice
/// what was alive after the last collection (8 MB at least), so a program
/// uses about what it keeps (pages it never touches cost nothing).
pub const NATIVE_CELLS: u64 = bf::backends::cli::MEMORY_MB << 17;

/// The standard library, every module's prelude.
pub const STD: &str = include_str!("../std/std.fern");

/// Compiles the program whose root module is the file `path`: its IR, and
/// its core form (see `core`), or an error message.
pub fn compile(path: &str) -> Result<(bf::ir::Program, core::Program), String> {
    use bf::asm::log::{self, INFO};
    let phase = log::phase(INFO, "fern to IR");
    let mut p = log::phase(INFO, "parse, and modules");
    let prog = modules::load(path, STD).map_err(|((pos, msg), files)| diagnostic(&files, pos, &msg))?;
    p.done(format!("{} files, {} modules, {} items", prog.files.len(), prog.modules.len(), prog.items.len()));
    drop(p);
    let mut p = log::phase(INFO, "type check");
    let mut core = checker::check(&prog).map_err(|errors| {
        // (the first few, and how many)
        const SHOWN: usize = 10;
        let mut out: Vec<String> = errors.iter().take(SHOWN).map(|(pos, msg)| diagnostic(&prog.files, *pos, msg)).collect();
        if errors.len() > 1 {
            out.push(format!("{} errors{}", errors.len(), if errors.len() > SHOWN { format!(" (the first {SHOWN} shown)") } else { String::new() }));
        }
        out.join("\n\n")
    })?;
    wrappers::inline(&mut core.funcs);
    p.done(format!("{} functions", core.funcs.len()));
    drop(p);
    let effects: HashMap<i64, String> = prog
        .items
        .iter()
        .enumerate()
        .filter(|(_, it)| matches!(it.kind, modules::ItemKind::Effect(_)))
        .map(|(i, it)| (i as i64, it.name.clone()))
        .collect();
    let p = log::phase(INFO, "selective CPS, and code generation");
    let program = codegen::generate(&core.funcs, &core.main, &effects, core.externs.clone(), &prog.files);
    drop(p);
    drop(phase);
    Ok((program, core))
}

/// An error at `pos` (in one of `files`, by number) as the compiler says
/// it: where, what, and the line it's in, marked where.
///
/// ```text
/// game.fern:4:13: error: {x: Int, y: Int} has no field z
///   |
/// 4 |     println(p.z.show());
///   |             ^
/// ```
fn diagnostic(files: &[String], pos: Pos, msg: &str) -> String {
    report(files, pos, "error", msg)
}

/// The program's warnings (see `core::Program::warnings`), as `diagnostic`
/// says errors.
pub fn warnings(core: &core::Program) -> Vec<String> {
    core.warnings.iter().map(|(pos, msg)| report(&core.files, *pos, "warning", msg)).collect()
}

/// An error or a warning (`kind`), as `diagnostic` says.
fn report(files: &[String], pos: Pos, kind: &str, msg: &str) -> String {
    if pos.line == 0 {
        // (one that isn't in a file: a file it couldn't read, say)
        return format!("{kind}: {msg}");
    }
    let name = files.get(pos.file).map_or("?", |n| n.as_str());
    let source = if pos.file == 0 { Some(STD.to_string()) } else { std::fs::read_to_string(name).ok() };
    let line = source.as_deref().and_then(|s| s.lines().nth(pos.line.wrapping_sub(1)));
    let place = if pos.col > 0 { format!("{name}:{}:{}", pos.line, pos.col) } else { format!("{name}:{}", pos.line) };
    let mut out = format!("{place}: {kind}: {msg}");
    if let Some(line) = line {
        let number = pos.line.to_string();
        let gutter = " ".repeat(number.len());
        // (the mark under the column, with tabs where the line has them)
        let lead: String = line.chars().take(pos.col.saturating_sub(1)).map(|c| if c == '\t' { '\t' } else { ' ' }).collect();
        out += &format!("\n{gutter} |\n{number} | {line}");
        if pos.col > 0 {
            out += &format!("\n{gutter} | {lead}^");
        }
    }
    out
}

/// The C backend `c`, as fern uses it: running loops in parallel only if
/// the C compiler can (OpenMP: see `openmp`; saying so if not).
pub fn backend(c: CBackend) -> CBackend {
    if c.parallel() && !openmp() {
        eprintln!("--parallel: the C compiler ({}) has no OpenMP (-fopenmp), so the loops won't be", cc());
        return c.without_parallel();
    }
    c
}

/// The C files a program names in `// links: FILE.c` lines in its file (C
/// it calls with `extern fn`s), relative to the file's folder.
pub fn links(path: &str) -> Vec<std::path::PathBuf> {
    let dir = std::path::Path::new(path).parent().unwrap_or(std::path::Path::new(""));
    let source = std::fs::read_to_string(path).unwrap_or_default();
    source.lines().filter_map(|l| l.strip_prefix("// links: ")).map(|f| dir.join(f.trim())).collect()
}

/// The C compiler (`$CC`, or `cc`).
fn cc() -> String {
    std::env::var("CC").unwrap_or_else(|_| "cc".into())
}

/// Whether the C compiler can run loops in parallel (OpenMP, with
/// -fopenmp), found out once by compiling a program that uses it. Without
/// it, a parallel loop is all the work of deciding whether to run in
/// parallel and none of the running (Apple's clang, macOS's `cc`, has no
/// OpenMP; Homebrew's LLVM does).
fn openmp() -> bool {
    static FOUND: std::sync::OnceLock<bool> = std::sync::OnceLock::new();
    *FOUND.get_or_init(|| {
        let dir = std::env::temp_dir().join(format!("fern-openmp-{}", std::process::id()));
        let probe = dir.join("probe.c");
        let ok = std::fs::create_dir_all(&dir).is_ok()
            && std::fs::write(&probe, "#include <omp.h>\nint main(void) { return omp_get_max_threads() > 0 ? 0 : 1; }\n").is_ok()
            && std::process::Command::new(cc()).arg("-fopenmp").arg(&probe).arg("-o").arg(dir.join("probe")).output().is_ok_and(|o| o.status.success());
        let _ = std::fs::remove_dir_all(&dir);
        ok
    })
}

// (the tape as big as the program was compiled for)
fn cells_define(program: &bf::ir::Program) -> String {
    format!("#define BF_CELLS {}\n", program.cells())
}

/// The program as C, with the C backend `c` (see `backend`), in `c_file`
/// (one file), compiled by `cc` (or `$CC`) into `binary`: -O2 in debug
/// (fast code of plain C, quickly), -O3 in release. `extra` goes to the
/// C compiler too: the C of extern fns, libraries. (`bf.h` is on the include path, for that C.) The C compiler
/// works on the program in parts, one for each core, all at once: a big
/// program's C would otherwise take it most of a minute, on one.
pub fn build(program: &bf::ir::Program, mode: Mode, c: &CBackend, units: Option<u64>, c_file: &std::path::Path, binary: &std::path::Path, extra: &[String]) -> Result<(), String> {
    let source = c.source(&program.compile());
    let define = cells_define(program);
    std::fs::write(c_file, source.single_with(&define)).map_err(|e| format!("{}: {e}", c_file.display()))?;
    static BUILDS: std::sync::atomic::AtomicUsize = std::sync::atomic::AtomicUsize::new(0);
    let n = BUILDS.fetch_add(1, std::sync::atomic::Ordering::Relaxed);
    let dir = std::env::temp_dir().join(format!("fern-{}-{n}", std::process::id()));
    std::fs::create_dir_all(&dir).map_err(|e| e.to_string())?;
    let result = build_in(&source, &define, mode, c.parallel(), units, &dir, binary, extra);
    let _ = std::fs::remove_dir_all(&dir);
    result
}

fn build_in(source: &bf::backends::CSource, define: &str, mode: Mode, parallel: bool, units: Option<u64>, dir: &std::path::Path, binary: &std::path::Path, extra: &[String]) -> Result<(), String> {
    use bf::asm::log::{phase, INFO};
    std::fs::write(dir.join("bf.h"), bf::ir::C_HEADER).map_err(|e| e.to_string())?;
    let cc = cc();
    let opt = if mode == Mode::Release { "-O3" } else { "-O2" };
    // (OpenMP's flag, for parallel loops: see `openmp`)
    let omp: &[&str] = if parallel { &["-fopenmp"] } else { &[] };
    // (a part for each core, but none smaller than about 200 KB of C: each
    // costs its own start, and its own copy of what they all share)
    let size: usize = source.chunks.iter().map(String::len).sum();
    let cores = std::thread::available_parallelism().map_or(1, |n| n.get());
    let parts = units.map_or(cores.min(size / 200_000).clamp(1, 16), |n| n as usize);
    let mut p = phase(INFO, format!("{cc} {opt}, {parts} parts at once"));
    let units = source.units(parts);
    let objects: Vec<std::path::PathBuf> = (0..units.len()).map(|k| dir.join(format!("part{k}.o"))).collect();
    for (k, unit) in units.iter().enumerate() {
        std::fs::write(dir.join(format!("part{k}.c")), format!("{define}{unit}")).map_err(|e| e.to_string())?;
    }
    // (and the flags that go with this C: see `cli::CC_FLAGS`)
    let flags: Vec<&str> = bf::backends::cli::CC_FLAGS.split_whitespace().collect();
    let compiled: Vec<Result<std::process::Output, std::io::Error>> = std::thread::scope(|s| {
        let jobs: Vec<_> = (0..units.len())
            .map(|k| {
                let (cc, dir, flags) = (&cc, dir, &flags);
                s.spawn(move || std::process::Command::new(cc).args(omp).arg(opt).args(flags).args(["-w", "-c", "-I"]).arg(dir).arg(dir.join(format!("part{k}.c"))).arg("-o").arg(dir.join(format!("part{k}.o"))).output())
            })
            .collect();
        jobs.into_iter().map(|j| j.join().unwrap()).collect()
    });
    for out in compiled {
        let out = out.map_err(|e| format!("{cc}: {e}"))?;
        if !out.status.success() {
            return Err(format!("{cc} failed on the program's C:\n{}", String::from_utf8_lossy(&out.stderr)));
        }
    }
    p.done(String::new());
    drop(p);
    let mut p = phase(INFO, format!("{cc} {opt}: the rest, and linking {}", binary.display()));
    let output = std::process::Command::new(&cc).args(omp).arg(opt).args(&flags).args(["-w", "-I"]).arg(dir).args(&objects).arg("-o").arg(binary).args(extra).output();
    let output = output.map_err(|e| format!("{cc}: {e}"))?;
    if !output.status.success() {
        return Err(format!("{cc} failed linking {}:\n{}", binary.display(), String::from_utf8_lossy(&output.stderr)));
    }
    p.done(String::new());
    Ok(())
}

