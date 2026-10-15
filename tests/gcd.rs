//! The sum of `gcd(i, 720720)` for `i` up to 2000000, by Euclid's algorithm
//! with `%`.

mod common;

use bf::asm::*;
use common::*;

const N: i64 = 2_000_000;

#[test]
fn gcd_prints_what_c_does() {
    let ops = program(|o| {
        let (n, i, a, b, t, total, flag) = (R1, R2, R3, R4, R5, R6, R7);
        set(o, n, N as u64);
        set(o, i, 1);
        set(o, total, 0);
        while_loop(o, flag, |o| { mov(o, flag, i); le_assign(o, flag, n); }, |o| {
            mov(o, a, i);
            set(o, b, 720_720);
            while_loop(o, R8, |o| mov(o, R8, b), |o| {
                mov(o, t, a);
                rem_assign(o, t, b);
                mov(o, a, b);
                mov(o, b, t);
            });
            add_assign(o, total, a);
            inc(o, i);
        });
        putint(o, total);
        puts(o, "\n");
    });
    let c = format!(
        r#"{C_HEAD}
int main(void) {{
    int64_t total = 0;
    for (int64_t i = 1; i <= {N}; i++) {{
        int64_t a = i, b = 720720;
        while (b) {{ int64_t t = a % b; a = b; b = t; }}
        total += a;
    }}
    printf("%lld\n", (long long)total);
}}
"#
    );
    check("gcd", &ops, &c);
}
