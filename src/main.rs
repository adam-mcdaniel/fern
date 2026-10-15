use bf::*;
use bf::backends::*;
use std::env::args;
use std::fs::read_to_string;
use std::process::exit;


const USAGE: &str = "Usage: bfc [--hex [--xlen N] | --parallel] <file>
  --hex       emit machine code for the CPU in hw/ ($readmemh format)
  --xlen N    cell width of the target CPU in bits, 8 to 64 (default 64)
  --parallel  emit C that runs loops in parallel where it can (with OpenMP:
              compile with -fopenmp, and -DBF_STATS to see which do)";

fn main() {
    let mut hex = false;
    let mut parallel = false;
    let mut xlen = 64;
    let mut path = None;
    let mut argv = args().skip(1);
    while let Some(arg) = argv.next() {
        match arg.as_str() {
            "--hex" => hex = true,
            "--parallel" => parallel = true,
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
        } else if parallel {
            println!("{}", ParallelC::default().compile(&ops));
        } else {
            println!("{}", C.compile(&ops));
        }
    }
}
