//! The total number of bits set in `i * 2654435761 mod 2^32` for `i` below
//! 5000000, a bit at a time.

mod common;

use bf::asm::*;
use common::*;

const N: i64 = 5_000_000;

#[test]
fn bitcount_prints_what_c_does() {
    let ops = program(|o| {
        let (i, v, t, total) = (R1, R2, R3, R4);
        set(o, total, 0);
        for_const(o, i, 0, N, R5, |o| {
            mov(o, v, i);
            mul_const(o, v, 2_654_435_761);
            and_const(o, v, 0xFFFF_FFFF);
            while_loop(o, R6, |o| mov(o, R6, v), |o| {
                mov(o, t, v);
                and_const(o, t, 1);
                add_assign(o, total, t);
                rshu_const(o, v, 1);
            });
        });
        putint(o, total);
        puts(o, "\n");
    });
    let c = format!(
        r#"{C_HEAD}
int main(void) {{
    int64_t total = 0;
    for (int64_t i = 0; i < {N}; i++) {{
        uint64_t v = (uint64_t)(i * 2654435761ll) & 0xFFFFFFFFull;
        while (v) {{ total += v & 1; v >>= 1; }}
    }}
    printf("%lld\n", (long long)total);
}}
"#
    );
    check("bitcount", &ops, &c);
}
