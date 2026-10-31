//! Which of the optimizer's passes run: each can be turned off (or on) by
//! its name, which is also what `-vv` reports its time under.

use std::collections::BTreeSet;

/// The passes, by name, each with what it does: the IR optimizer's (see
/// `optimize`), in the order a round runs them, and then the VM ops' own
/// optimizer.
pub const PASSES: &[(&str, &str)] = &[
    ("tail-calls", "a function's calls to itself just before it returns become jumps back to its start"),
    ("inline", "calls to small functions, and to functions called once, replaced by their bodies"),
    ("specialize", "copies of functions for calls that pass constants they can make cheaper"),
    ("dead-arguments", "parameters a function never uses dropped, and results its callers all ignore"),
    ("ranges", "what range analysis finds out about each value used to simplify what uses it"),
    ("simplify", "each operation folded and simplified again, as its operands are replaced"),
    ("gvn", "an operation the same as one that dominates it replaced by that one (global value numbering)"),
    ("trivial-params", "a block parameter that's always given the same value replaced by it"),
    ("variables", "a local variable only loaded and stored becomes a value (a parameter where ways in meet), even across loops in loops"),
    ("memory", "loads whose value is known, and stores nothing can read, removed"),
    ("pure-calls", "calls to functions that are only their result reused or removed like operations"),
    ("licm", "what doesn't change in a loop moved out of it (loop-invariant code motion)"),
    ("strength-reduce", "multiplying and indexing by a loop's counter turned into adding, each time round"),
    ("unroll", "loops that run a small, constant number of times unrolled"),
    ("fold-branches", "branches on constants turned into jumps"),
    ("thread-jumps", "jumps to a block that only jumps on sent straight to where it goes"),
    ("merge-blocks", "a block merged into its only predecessor, when that jumps to it"),
    ("merge-tails", "blocks that do the same and go to the same place merged"),
    ("dead-params", "block parameters nothing needs removed, with what jumps pass them"),
    ("devirtualize", "calls through a known function's address made direct"),
    ("asm-opt", "the VM ops' own optimizer (`asm::opt`): fewer of the VM's steps"),
];

/// The IR optimizer's passes: all of `PASSES` but the last.
pub(in crate::ir) fn ir_passes() -> impl Iterator<Item = &'static str> {
    PASSES.iter().map(|(name, _)| *name).filter(|&n| n != "asm-opt")
}

/// Which passes run: all of them but those turned off.
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct Passes {
    off: BTreeSet<&'static str>,
}

impl Passes {
    /// Every pass.
    pub fn all() -> Passes {
        Passes::default()
    }

    /// None of them: no optimizing at all.
    pub fn none() -> Passes {
        Passes { off: PASSES.iter().map(|(name, _)| *name).collect() }
    }

    /// Whether the pass `name` runs.
    pub fn on(&self, name: &str) -> bool {
        !self.off.contains(name)
    }

    /// Whether any of the IR optimizer's passes run.
    pub fn any_ir(&self) -> bool {
        ir_passes().any(|n| self.on(n))
    }

    /// Turns the pass `name` (one of `PASSES`) on or off; `ir` is all the IR
    /// optimizer's. An error if there's no such pass.
    pub fn set(&mut self, name: &str, on: bool) -> Result<(), String> {
        let names: Vec<&'static str> = if name == "ir" { ir_passes().collect() } else { PASSES.iter().map(|(n, _)| *n).filter(|&n| n == name).collect() };
        if names.is_empty() {
            return Err(format!("no pass called `{name}` (see --passes)"));
        }
        for n in names {
            if on {
                self.off.remove(n);
            } else {
                self.off.insert(n);
            }
        }
        Ok(())
    }
}
