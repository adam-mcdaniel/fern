use bf::asm::{R1, mul_assign};
use bf::*;
use std::env::args;
use std::fs::read_to_string;
use std::process::exit;
use bf::asm::*;

const USAGE: &str = "Usage: bfc [--hex [--xlen N]] <file>
  --hex     emit machine code for the CPU in hw/ ($readmemh format)
  --xlen N  cell width of the target CPU in bits, 8 to 64 (default 64)";

fn main() {
    let mut hex = false;
    let mut xlen = 64;
    let mut path = None;
    let mut argv = args().skip(1);
    while let Some(arg) = argv.next() {
        match arg.as_str() {
            "--hex" => hex = true,
            "--xlen" => match argv.next().and_then(|n| n.parse().ok()) {
                Some(n) => xlen = n,
                None => {
                    eprintln!("--xlen needs a number\n{USAGE}");
                    exit(1);
                }
            },
            _ if path.is_none() => path = Some(arg),
            _ => {
                eprintln!("{USAGE}");
                exit(1);
            }
        }
    }
    let Some(path) = path else {
        eprintln!("{USAGE}");
        return;
    };

    let ops = parse(&read_to_string(path).expect("Could not open file"));

    if let Ok(ops) = ops {
        if hex {
            match cpu::assemble(&ops, xlen) {
                Ok(code) => print!("{}", cpu::to_hex(&code)),
                Err(e) => {
                    eprintln!("error: {e}");
                    exit(1);
                }
            }
        } else {
            println!("{}", compile(&ops));
        }
    }
}
