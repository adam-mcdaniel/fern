//! A program written with `bf::ir`: reads n, prints 1² + 2² + ... + n², and
//! the primes up to n.
//!
//! ```text
//! echo 30 | cargo run --example ir            # runs it
//! cargo run --example ir -- --ops > sum.bf    # the VM program, for `bf`
//! cargo run --example ir -- --ir              # what the optimizer made of it
//! ```

use bf::asm::to_source;
use bf::ir::Program;
use std::io::Read;

fn main() {
    let mut p = Program::new();

    p.function("square", &["x"], |f| {
        let x = f.arg("x");
        f.ret(x * x);
    });

    p.function("is_prime", &["n"], |f| {
        let n = f.arg("n");
        f.if_(n.lt(2), |f| f.ret(0));
        let d = f.var(2);
        f.while_((d * d).le(n), |f| {
            f.if_((n % d).eq(0), |f| f.ret(0));
            f.set(d, d + 1);
        });
        f.ret(1);
    });

    p.main(|f| {
        let n = f.read_int();
        let sum = f.var(0);
        f.for_(1, n + 1, |f, i| {
            let sq = f.call("square", i);
            f.set(sum, sum + sq);
        });
        f.print_int(sum);
        f.print("\n");
        f.for_(2, n + 1, |f, i| {
            let prime = f.call("is_prime", i);
            f.if_(prime, |f| {
                f.print_int(i);
                f.print(" ");
            });
        });
        f.print("\n");
    });

    match std::env::args().nth(1).as_deref() {
        Some("--ops") => println!("{}", to_source(&p.compile())),
        Some("--ir") => println!("{}", p.ir().1),
        _ => {
            let mut input = vec![];
            std::io::stdin().read_to_end(&mut input).unwrap();
            print!("{}", p.run(&input));
        }
    }
}
