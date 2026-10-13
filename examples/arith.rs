//! Prints a table of arithmetic on values near the cell width's limits, so
//! the output depends on the width. Prints the program as source, or with
//! `--out XLEN`, the output the interpreter gets on an XLEN-bit CPU;
//! `hw/gen.sh` saves both as a hardware test.

use bf::asm::*;
use bf::interp::Machine;
use bf::Op;

fn program() -> Vec<Op> {
    let o = &mut vec![];
    let (min, max, a, b, x) = (R1, R2, R3, R4, R5);
    // min = the most negative value: double 1 until the next doubling is 0
    set(o, min, 1);
    begin_loop(o);
    mov(o, x, min);
    add_assign(o, x, x);
    lnot_assign(o, x);
    break_if(o, x);
    add_assign(o, min, min);
    end_loop(o);
    mov(o, max, min);
    dec(o, max);

    type Op2 = fn(&mut dyn Program, &Location, &Location);
    let ops: [(&str, Op2); 18] = [
        ("+", add_assign),
        ("-", sub_assign),
        ("*", mul_assign),
        ("/", div_assign),
        ("%", rem_assign),
        ("/u", divu_assign),
        ("%u", remu_assign),
        ("^", xor_assign),
        ("&", and_assign),
        ("|", or_assign),
        ("<<", lsh_assign),
        (">>", rsh_assign),
        (">>u", rshu_assign),
        ("<", lt_assign),
        ("<u", ltu_assign),
        (">=", ge_assign),
        ("==", eq_assign),
        ("max", max_assign),
    ];
    let pairs: [(&dyn Fn(&mut Vec<Op>), &dyn Fn(&mut Vec<Op>)); 5] = [
        (&|o| mov(o, a, min), &|o| set_int(o, b, -1)),
        (&|o| mov(o, a, max), &|o| set_int(o, b, 7)),
        (&|o| mov(o, a, min), &|o| mov(o, b, max)),
        (&|o| set_int(o, a, -1234), &|o| set_int(o, b, 5)),
        (&|o| set_int(o, a, 300), &|o| set_int(o, b, 0)),
    ];
    for (set_a, set_b) in pairs {
        for (name, f) in ops {
            set_a(o);
            set_b(o);
            putint(o, a);
            puts(o, &format!(" {name} "));
            putint(o, b);
            puts(o, " = ");
            f(o, a, b);
            putint(o, a);
            puts(o, "\n");
        }
    }
    putuint(o, min);
    puts(o, "\n");
    std::mem::take(o)
}

fn main() {
    let ops = program();
    let args: Vec<String> = std::env::args().collect();
    if let [_, flag, xlen] = &args[..] {
        assert_eq!(flag, "--out");
        let halted = Machine::cpu_xlen(xlen.parse().unwrap()).run(&ops, b"").unwrap();
        print!("{}", String::from_utf8(halted.output).unwrap());
    } else {
        print!("{}", bf::asm::to_source(&ops));
    }
}
