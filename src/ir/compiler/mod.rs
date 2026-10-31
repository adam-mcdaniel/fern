//! Turning programs into ops: the optimizer and its passes, the runtime code
//! programs get (the garbage collector), and lowering to the `asm` helpers.

use super::*;

mod gc;
mod imperative;
mod inline;
mod interproc;
mod loops;
pub(in crate::ir) mod lower;
mod memory;
mod opt;
mod passes;
mod prepare;
mod range;
pub(super) mod sched;

pub use lower::{lower, lower_with, Options};
pub use opt::{optimize, optimize_with};
pub use passes::{Passes, PASSES};
pub use prepare::EXIT;
