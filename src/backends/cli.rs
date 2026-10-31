//! The options `bf` and `fern` share, for what they make of a program: which
//! C, run how, with how much memory, and which passes. Both take them the
//! same way, meaning the same thing (each tool's own options are in its
//! `main.rs`).

use super::{CBackend, LiteralC, OptimizingC};
use crate::ir::{Passes, PASSES};
use clap::{Args, ValueEnum};

/// Which C the VM's ops become.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq, ValueEnum)]
pub enum Backend {
    /// C a compiler makes fast code of: routines done with the machine's
    /// instructions, a function's cells kept in variables, ...
    #[default]
    Optimizing,
    /// Each op as the C that does what it does, one after the other.
    Literal,
}

/// The optimizing backend's passes, by name, with what each does.
pub const BACKEND_PASSES: &[(&str, &str)] = &[
    ("idioms", "functions that are `asm`'s routines (multiplying, comparing, ...) done with the machine's instructions"),
    ("linear", "functions whose effect is linear in what they're given done as straight-line code"),
    ("promote", "each function's cells kept in variables (the C compiler's registers), not memory"),
];

/// The tape's size when nothing says (in MB): what fern makes programs for,
/// so ops from fern fit; a tape bigger than a program needs is never a
/// problem (pages it never touches cost nothing).
pub const MEMORY_MB: u64 = 1024;

#[derive(Args, Clone, Debug, Default)]
pub struct Options {
    /// Which C to make of the VM's ops
    #[arg(long, value_enum, default_value_t = Backend::Optimizing)]
    pub backend: Backend,
    /// Run loops on all the cores, where they can and it pays (the optimizing
    /// backend, with a C compiler that has OpenMP: -fopenmp)
    #[arg(long)]
    pub parallel: bool,
    /// The program's memory, its stack and heap, in MB [default: 1024]
    #[arg(long, value_name = "MB")]
    pub memory: Option<u64>,
    /// Turn passes on (see --passes); `ir` is all the IR optimizer's
    #[arg(long, value_delimiter = ',', value_name = "PASS,...")]
    pub enable: Vec<String>,
    /// Turn passes off (see --passes); `ir` is all the IR optimizer's
    #[arg(long, value_delimiter = ',', value_name = "PASS,...")]
    pub disable: Vec<String>,
    /// List the passes --enable and --disable take, and stop
    #[arg(long)]
    pub passes: bool,
    /// Inline a function at every call while it comes to no more than this
    /// many ops (the optimizing backend; more makes more C, which the C
    /// compiler takes longer over)
    #[arg(long, value_name = "OPS", default_value_t = 0)]
    pub inline_ops: usize,
    /// Split the C into this many files, to compile at once [fern, building:
    /// one for each core, as the C's size allows; otherwise one]
    #[arg(long, value_name = "N", value_parser = clap::value_parser!(u64).range(1..=256))]
    pub units: Option<u64>,
    /// Say what the compiler's doing, and how long it takes (-v, -vv, -vvv;
    /// or BF_LOG=1, 2 or 3)
    #[arg(short, long, action = clap::ArgAction::Count)]
    pub verbose: u8,
}

impl Options {
    /// The tape's size, in cells.
    pub fn cells(&self) -> u64 {
        self.memory.unwrap_or(MEMORY_MB) << 17
    }

    /// Sets the log level, if `-v` says.
    pub fn log(&self) {
        if self.verbose > 0 {
            crate::asm::log::set_level(self.verbose);
        }
    }

    /// The IR's passes: `preset`, with what `--enable` and `--disable` say
    /// (the backend's are for `c`).
    pub fn ir_passes(&self, mut preset: Passes) -> Result<Passes, String> {
        for (names, on) in [(&self.enable, true), (&self.disable, false)] {
            for name in names.iter().filter(|n| !is_backend_pass(n)) {
                preset.set(name, on)?;
            }
        }
        Ok(preset)
    }

    /// The C backend these options choose, with its passes (all on, unless
    /// `--disable` says).
    pub fn c(&self) -> Result<CBackend, String> {
        let on = |name: &str| !self.disable.iter().any(|n| n == name);
        match self.backend {
            Backend::Optimizing => Ok(CBackend::Optimizing(OptimizingC { parallel: self.parallel, idioms: on("idioms"), linear: on("linear"), promote: on("promote"), inline_ops: self.inline_ops, ..OptimizingC::default() })),
            Backend::Literal => {
                if self.parallel {
                    return Err("--parallel needs the optimizing backend".into());
                }
                if let Some(n) = self.enable.iter().chain(&self.disable).find(|n| is_backend_pass(n)) {
                    return Err(format!("`{n}` is the optimizing backend's (the literal backend has no passes)"));
                }
                Ok(CBackend::Literal(LiteralC))
            }
        }
    }
}

/// The flags fern gives the C compiler, besides -O2 or -O3 (and -fopenmp,
/// with --parallel): the SLP vectorizer, which looks for scalar operations
/// it can do several at once, takes longer than anything else on this C,
/// which has hundreds of variables to a function, and finds nothing.
pub const CC_FLAGS: &str = "-fwrapv -fno-slp-vectorize";

/// The C, `source`, as `units` files (one, unless --units says), each
/// complete with the tape's size, and how fern would compile them: for
/// writing out.
pub fn c_files(source: &super::CSource, cells: u64, units: Option<u64>, parallel: bool) -> Vec<String> {
    let note = format!("/* fern compiles this with: cc -O3 {CC_FLAGS}{} */\n#define BF_CELLS {cells}\n", if parallel { " -fopenmp" } else { "" });
    let parts = units.unwrap_or(1) as usize;
    if parts == 1 {
        return vec![source.single_with(&note)];
    }
    source.units(parts).into_iter().map(|u| format!("{note}{u}")).collect()
}

fn is_backend_pass(name: &str) -> bool {
    BACKEND_PASSES.iter().any(|(n, _)| *n == name)
}

/// The passes, as `--passes` lists them: with the IR optimizer's, if the
/// tool has an IR (`ir`), and what's on by default.
pub fn passes_help(ir: bool) -> String {
    let mut out = String::new();
    let width = PASSES.iter().chain(BACKEND_PASSES).map(|(n, _)| n.len()).max().unwrap_or(0) + 2;
    let mut group = |title: &str, passes: &[(&str, &str)]| {
        out += title;
        out.push('\n');
        for (name, what) in passes {
            out += &format!("  {name:width$}{what}\n");
        }
    };
    let (ir_passes, ops_passes) = PASSES.split_at(PASSES.len() - 1);
    if ir {
        group("The IR optimizer's (all on with --release, all off without; `ir` is all of them):", ir_passes);
    }
    group("The VM ops' optimizer (off, unless the VM runs them: with fern's --release --interpret; C is better without it):", ops_passes);
    group("The optimizing backend's (all on):", BACKEND_PASSES);
    out
}
