//! Collatz: the total number of steps the numbers up to 2000000 take to reach
//! 1, halving the even ones (with `%` and `/` by 2) and taking the odd ones to
//! `3x + 1`.

mod common;

use bf::asm::*;
use common::*;

const N: i64 = 2_000_000;

#[test]
fn collatz_prints_what_c_does() {
    let ops = program(|o| {
        let (n, i, x, t, total, flag) = (R1, R2, R3, R4, R5, R6);
        set(o, n, N as u64);
        set(o, i, 1);
        set(o, total, 0);
        while_loop(o, flag, |o| { mov(o, flag, i); le_assign(o, flag, n); }, |o| {
            mov(o, x, i);
            while_loop(o, R7, |o| { mov(o, R7, x); ne_const(o, R7, 1); }, |o| {
                mov(o, t, x);
                rem_const(o, t, 2);
                begin_if(o, t);
                mul_const(o, x, 3);
                inc(o, x);
                begin_else(o);
                div_const(o, x, 2);
                end_if(o);
                inc(o, total);
            });
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
        int64_t x = i;
        while (x != 1) {{ if (x % 2) x = 3 * x + 1; else x /= 2; total++; }}
    }}
    printf("%lld\n", (long long)total);
}}
"#
    );
    check("collatz", &ops, &c);
}
