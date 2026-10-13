//! Reads lines and prints each one's length, the line reversed, and how it
//! compares with "hello". Prints the program as source; `hw/gen.sh` saves it
//! as a hardware test.

use bf::asm::*;

fn main() {
    let o = &mut vec![];
    let (buf, cap, len, i, c, hello, cmp, flag) = (R1, R2, R3, R4, R5, R6, R7, R8);
    init(o);
    set(o, cap, 32);
    heap_alloc(o, buf, cap);
    heap_str(o, hello, "hello");

    begin_loop(o);
    read_line(o, len, buf, cap);
    // stop at an empty line or the end of input
    mov(o, flag, len);
    lnot_assign(o, flag);
    break_if(o, flag);

    putint(o, len);
    puts(o, " ");
    mov(o, i, len);
    while_loop(o, flag, |o| { mov(o, flag, i); gt_const(o, flag, 0); }, |o| {
        dec(o, i);
        load_index(o, c, buf, i);
        putchar(o, c);
    });
    str_cmp(o, cmp, buf, hello);
    puts(o, " ");
    putint(o, cmp);
    puts(o, "\n");
    end_loop(o);
    print!("{}", to_source(o));
}
