//! minic: a compiler for a small C-like language, to the VM, through
//! `bf::ir`. An example of how to organize a compiler on the IR.
//!
//! ```text
//! cargo run --example minic -- examples/minic/fib.mini        # compile and run
//! cargo run --example minic -- examples/minic/fib.mini --ops  # the VM program, for `bf`
//! cargo run --example minic -- examples/minic/fib.mini --ir   # what the optimizer made
//! ```
//!
//! The language:
//!
//! ```text
//! fn gcd(a, b) {
//!     while b != 0 { let t = b; b = a % b; a = t; }
//!     return a;
//! }
//! fn main() {
//!     let xs = array(3);              // an array on the heap; `let xs[3];` on the stack
//!     xs[0] = read();                 // a number from the input
//!     let p = &xs[0];                 // pointers: &x, &a[i], *p, *p = v, p[i]
//!     let pt = new Point;             // structs (`struct Point { x, y }`): new,
//!     pt.x = 3;                       //   p.field, `let q: Point;` on the stack
//!     if xs[0] > 0 && gcd(xs[0], 12) == 1 { print("coprime\n"); }
//!     else { print(xs[0], " isn't\n"); }
//! }
//! ```
//!
//! A compiler is a pipeline, each stage a file, each knowing only about the
//! one before:
//!
//! 1. `lexer.rs`: text into tokens.
//! 2. `parser.rs`: tokens into a tree (`ast.rs`).
//! 3. `check.rs`: the tree's mistakes, as error messages.
//! 4. `codegen.rs`: the tree into a `bf::ir::Program`. The only stage that
//!    knows about the IR.
//! 5. `Program::compile()` / `run()`: the IR's optimizer and lowering, to
//!    VM ops (or running them).

mod ast;
mod check;
mod codegen;
mod lexer;
mod parser;

use std::io::Read;
use std::process::exit;

fn main() {
    let args: Vec<String> = std::env::args().skip(1).collect();
    let Some(path) = args.iter().find(|a| !a.starts_with("--")) else {
        eprintln!("usage: minic FILE.mini [--ops | --ir]");
        exit(1);
    };
    let src = std::fs::read_to_string(path).unwrap_or_else(|e| fail(path, &e.to_string()));

    let tokens = lexer::lex(&src).unwrap_or_else(|e| fail(path, &e));
    let module = parser::parse(tokens).unwrap_or_else(|e| fail(path, &e));
    check::check(&module).unwrap_or_else(|e| fail(path, &e));
    let program = codegen::generate(&module);

    if args.iter().any(|a| a == "--ops") {
        println!("{}", bf::asm::to_source(&program.compile()));
    } else if args.iter().any(|a| a == "--ir") {
        println!("{}", program.ir().1);

    } else {
        // (the input, if the program reads any: `run` takes it all at once)
        let mut input = vec![];
        if ast::calls(&module.funcs, "read") {
            std::io::stdin().read_to_end(&mut input).unwrap();
        }
        print!("{}", program.run(&input));
    }
}

fn fail(path: &str, why: &str) -> ! {
    eprintln!("{path}:{why}");
    exit(1)
}
