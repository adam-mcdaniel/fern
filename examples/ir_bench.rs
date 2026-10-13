//! Measures what `optimize` buys on a few IR programs: the size of each
//! lowered program's machine code, and how many ops it runs, before and after
//! optimizing. Also checks that every version prints the same thing.

#[path = "common/programs.rs"]
mod programs;

use bf::asm::ir::{lower, optimize, run, Module};
use programs::*;
use bf::interp::Machine;

fn measure(m: &Module, input: &[u8]) -> (usize, u64, Vec<u8>) {
    let ops = lower(m).unwrap();
    let bytes = bf::cpu::assemble(&ops, 64).unwrap().len();
    let halted = Machine::cpu().run(&ops, input).unwrap();
    (bytes, halted.steps, halted.output)
}

fn main() {
    if let Some(name) = std::env::args().skip_while(|a| a != "--show").nth(1) {
        let mut m = match name.as_str() {
            "fib" => fib(),
            "sieve" => sieve(),
            "demo" => demo(),
            "kernel" => kernel(),
            "loops" => loops(),
            _ => tail(),
        };
        optimize(&mut m);
        print!("{m}");
        return;
    }
    let programs = all();
    println!("{:8} {:>17} {:>17} {:>13}", "", "bytes", "ops run", "ops saved");
    println!("{:8} {:>8} {:>8} {:>8} {:>8}", "program", "before", "after", "before", "after");
    for (name, m, input) in programs {
        let want = run(&m, input, 64).unwrap();
        let mut optimized = m.clone();
        optimize(&mut optimized);
        let (b0, s0, out0) = measure(&m, input);
        let (b1, s1, out1) = measure(&optimized, input);
        assert_eq!(out0, want, "{name} unoptimized");
        assert_eq!(out1, want, "{name} optimized");
        println!(
            "{name:8} {b0:>8} {b1:>8} {s0:>8} {s1:>8} {:>12.1}%",
            100.0 * (s0 as f64 - s1 as f64) / s0 as f64
        );
    }
}
