//! The DOT language's FFI, from Rust: runs examples/dot/tour/ffi.dot on the
//! VM, with its external functions given as host functions.
//!
//! An external function is called the way the VM calls any function the
//! program doesn't define, so a host function gets what the C function
//! `void name(int64_t **tape, int64_t **ptr, int64_t *acc)` would (see
//! examples/dot/tour/ffi.c): the tape, the address of the cell the pointer
//! is at (the first argument; the rest follow), and the accumulator, where
//! it leaves its result. A `String` argument is the address of its length,
//! then its characters.

use bf::asm::ir::{dot, lower, optimize};
use bf::interp::{HostFn, Machine};

fn main() {
    let mut compiler = dot::Compiler::new();
    compiler.dir("examples/dot/tour");
    let src = std::fs::read_to_string("examples/dot/tour/ffi.dot").unwrap();
    let mut module = compiler.compile(&src).unwrap_or_else(|e| panic!("{e}"));
    optimize(&mut module);
    let ops = lower(&module).unwrap();
    let machine = Machine::cpu()
        .host(
            "popcount",
            HostFn::new(|c| {
                c.acc = c.arg(0)?.count_ones() as i64;
                Ok(())
            }),
        )
        .host(
            "checksum",
            HostFn::new(|c| {
                c.acc = c.string(c.arg(0)?)?.bytes().map(|b| b as i64).sum();
                Ok(())
            }),
        )
        .host(
            "clamp",
            HostFn::new(|c| {
                c.acc = c.arg(0)?.clamp(c.arg(1)?, c.arg(2)?);
                Ok(())
            }),
        );
    let halted = machine.run(&ops, b"").unwrap_or_else(|e| panic!("{e}"));
    print!("{}", String::from_utf8_lossy(&halted.output));
}
