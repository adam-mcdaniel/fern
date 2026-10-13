//! What `asm::opt` does to the programs the IR lowers to: how many ops
//! each has, and how many steps it takes on the VM, without it and with
//! it (checking that both print the same), and how many VM steps that is
//! for each step the IR takes.
//!
//! ```text
//! cargo run --release --example vm_opt [-- --cells N] [--kinds] [--only NAME]
//! ```
//!
//! `--cells` sets the tape the programs are lowered for (4096, the
//! hardware's, by default); `--kinds` adds how many steps of each kind of
//! op each program takes, optimized, and which functions take them (and
//! checks that no pointer leads to the registers, as lowering promises).

#[path = "common/programs.rs"]
mod programs;
use bf::asm::ir::{dot, lower_with, optimize, run_counting, Module, Options};
use bf::interp::Machine;
use bf::Op;
use std::collections::BTreeMap;

/// How many times each kind of op runs (on the 64-bit CPU model), and how
/// many steps each function takes (not counting the ones it calls).
fn kinds(ops: &[Op], input: &[u8], cells: usize) -> (BTreeMap<&'static str, u64>, BTreeMap<String, u64>) {
    // which function each op is in
    let mut owner = vec![String::from("main"); ops.len()];
    let mut inside: Vec<String> = vec![];
    for (i, op) in ops.iter().enumerate() {
        if let (Op::Func, Some(Op::Label(l))) = (op, i.checked_sub(1).map(|j| ops[j])) {
            inside.push(l.iter().take_while(|&&c| c != 0).map(|&c| c as char).collect());
        }
        if let Some(f) = inside.last() {
            owner[i] = f.clone();
        }
        if *op == Op::EndFunc {
            inside.pop();
        }
    }
    let mut per_function: BTreeMap<String, u64> = BTreeMap::new();
    let mut pair = vec![0; ops.len()];
    let mut open = vec![];
    let mut funcs = std::collections::HashMap::new();
    for (i, op) in ops.iter().enumerate() {
        match op {
            Op::While | Op::Func => open.push(i),
            Op::EndWhile | Op::EndFunc => {
                let j = open.pop().unwrap();
                pair[i] = j;
                pair[j] = i;
            }
            _ => {}
        }
        if let (Op::Func, Some(Op::Label(l))) = (op, i.checked_sub(1).map(|j| ops[j])) {
            funcs.insert(l, i + 1);
        }
    }
    let mut count = BTreeMap::new();
    let mut tape = vec![0i64; cells];
    let (mut p, mut acc, mut pc) = (0usize, 0i64, 0usize);
    let (mut ptrs, mut rets) = (vec![], vec![]);
    let mut input = input.iter();
    while pc < ops.len() {
        let mut next = pc + 1;
        let name = match &ops[pc] {
            Op::Deref => {
                ptrs.push(p);
                p = tape[p] as usize;
                // lowering promises no pointer leads to the registers
                assert!(p >= 48, "a pointer to cell {p}, at op {pc}");
                "*"
            }
            Op::Refer => {
                p = ptrs.pop().unwrap();
                "&"
            }
            Op::Where => {
                acc = p as i64;
                "?"
            }
            Op::Move(n) => {
                p = (p as i64 + n) as usize;
                assert!(ptrs.is_empty() || p >= 48, "through a pointer to cell {p}, at op {pc}");
                "move"
            }
            Op::Set(n) => {
                acc = *n as i64;
                "set"
            }
            Op::Label(l) => {
                acc = funcs[l] as i64;
                "label"
            }
            Op::Load => {
                acc = tape[p];
                "load"
            }
            Op::Store => {
                tape[p] = acc;
                "store"
            }
            Op::Call => {
                rets.push(next);
                next = acc as usize;
                "call"
            }
            Op::Read => {
                acc = input.next().map_or(-1, |b| *b as i64);
                "read"
            }
            Op::Write => "write",
            Op::Add => {
                acc = acc.wrapping_add(tape[p]);
                "add"
            }
            Op::Neg => {
                acc = acc.wrapping_neg();
                "neg"
            }
            Op::Positive => {
                acc = (acc > 0) as i64;
                "#"
            }
            Op::While => {
                if acc == 0 {
                    next = pair[pc] + 1;
                }
                "[ ]"
            }
            Op::EndWhile => {
                if acc != 0 {
                    next = pair[pc] + 1;
                }
                "[ ]"
            }
            Op::Func => {
                next = pair[pc] + 1;
                "func"
            }
            Op::EndFunc => {
                next = rets.pop().unwrap();
                "ret"
            }
        };
        *count.entry(name).or_default() += 1;
        *per_function.entry(owner[pc].clone()).or_default() += 1;
        pc = next;
    }
    (count, per_function)
}

fn main() {
    let args: Vec<String> = std::env::args().collect();
    let value = |flag: &str| args.iter().position(|a| a == flag).map(|i| args[i + 1].clone());
    let cells: u64 = value("--cells").map_or(4096, |c| c.parse().unwrap());
    let only = value("--only");
    let mut all: Vec<(String, Module, Vec<u8>)> =
        programs::all().into_iter().map(|(n, m, i)| (n.to_string(), m, i.to_vec())).collect();
    for (name, input) in [("hello", ""), ("lists", ""), ("strings", "hello world\n\n"), ("trees", ""), ("tour/modules", "1\n"), ("tour/generics", "")] {
        let path = format!("examples/dot/{name}.dot");
        let mut c = dot::Compiler::new();
        c.dir(std::path::Path::new(&path).parent().unwrap());
        let m = c.compile(&std::fs::read_to_string(&path).unwrap()).unwrap_or_else(|e| panic!("{name}: {e}"));
        all.push((format!("dot:{name}"), m, input.as_bytes().to_vec()));
    }
    println!("lowered for a tape of {cells} cells");
    println!("{:18} {:>8} {:>8} {:>10} {:>10} {:>7} {:>9} {:>6}", "program", "ops", "opt ops", "steps", "opt steps", "saved", "IR steps", "ratio");
    let (mut before, mut after) = (0u64, 0u64);
    let mut total_kinds: BTreeMap<&str, u64> = BTreeMap::new();
    for (name, mut m, input) in all {
        if only.as_ref().is_some_and(|o| !name.contains(o.as_str())) {
            continue;
        }
        optimize(&mut m);
        let plain = lower_with(&m, &Options { optimize: false, cells, ..Options::default() }).unwrap();
        let opt = lower_with(&m, &Options { cells, ..Options::default() }).unwrap();
        // (a little past the end of the tape: the program's pointer may step
        // just past it)
        let tape = (cells as usize).max(1 << 16) + 64;
        let machine = Machine { cells: tape, ..Machine::cpu() };
        let a = machine.run(&plain, &input).unwrap();
        let b = machine.run(&opt, &input);
        let (steps, same, n) = match &b {
            Ok(b) => (b.steps.to_string(), b.output == a.output, b.steps),
            Err(e) => (e.clone(), false, a.steps),
        };
        before += a.steps;
        after += n;
        let saved = 100.0 * (1.0 - n as f64 / a.steps as f64);
        // how many steps the IR takes (without the garbage collector, which
        // lowering adds), and how many VM steps that comes to for each
        let ir = run_counting(&m, &input, 64, &Default::default()).map_or(0, |(_, s)| s);
        println!(
            "{name:18} {:>8} {:>8} {:>10} {:>10} {saved:>6.1}% {ir:>9} {:>6.1} {}",
            plain.len(),
            opt.len(),
            a.steps,
            steps,
            n as f64 / ir as f64,
            if same { "" } else { "PRINTS SOMETHING ELSE" }
        );
        if args.iter().any(|a| a == "--kinds") {
            let (k, funcs) = kinds(&opt, &input, tape);
            let line: Vec<String> = k.iter().map(|(n, c)| format!("{n} {c}")).collect();
            println!("    {}", line.join(", "));
            let mut funcs: Vec<(String, u64)> = funcs.into_iter().collect();
            funcs.sort_by_key(|(_, c)| std::cmp::Reverse(*c));
            let line: Vec<String> = funcs.iter().take(6).map(|(f, c)| format!("{f} {:.0}%", 100.0 * *c as f64 / n as f64)).collect();
            println!("    {}", line.join(", "));
            for (n, c) in k {
                *total_kinds.entry(n).or_default() += c;
            }
        }
    }
    println!("{:18} {:>8} {:>8} {before:>10} {after:>10} {:>6.1}%", "total", "", "", 100.0 * (1.0 - after as f64 / before as f64));
    if !total_kinds.is_empty() {
        let line: Vec<String> = total_kinds.iter().map(|(n, c)| format!("{n} {:.1}%", 100.0 * *c as f64 / after as f64)).collect();
        println!("    {}", line.join(", "));
    }
}
