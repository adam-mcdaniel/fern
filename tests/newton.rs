//! Integer cube roots of half a million random numbers below 2^36, by
//! Newton's method from above (a different number of steps for each, a
//! division in each); prints their sum.

mod common;

use bf::asm::*;
use common::*;

const N: i64 = 500_000;

#[test]
fn newton_prints_what_c_does() {
    let ops = program(|o| {
        let (i, n, x, y, t, seed, sum) = (R1, R2, R3, R4, R5, R6, R7);
        set(o, seed, 12345);
        set(o, sum, 0);
        for_const(o, i, 0, N, R0, |o| {
            // n = (i * 2654435761 + seed-ish) mod 2^36, as a hash of i
            mov(o, n, i);
            mul_const(o, n, 2_654_435_761);
            add_assign(o, n, seed);
            mov(o, t, n);
            rshu_const(o, t, 29);
            xor_assign(o, n, t);
            and_const(o, n, (1 << 36) - 1);
            inc(o, n);
            set(o, x, 4097);
            // y = (2x + n / x^2) / 3, while it's below x
            let next = |o: &mut dyn Program| {
                mov(o, y, x);
                mul_assign(o, y, x);
                mov(o, t, n);
                div_assign(o, t, y);
                mov(o, y, x);
                add_assign(o, y, x);
                add_assign(o, y, t);
                div_const(o, y, 3);
            };
            next(o);
            while_loop(o, R8, |o| { mov(o, R8, y); lt_assign(o, R8, x); }, |o| {
                mov(o, x, y);
                next(o);
            });
            add_assign(o, sum, x);
        });
        putint(o, sum);
        puts(o, "\n");
    });
    let c = format!(
        r#"{C_HEAD}
int main(void) {{
    int64_t seed = 12345, sum = 0;
    for (int64_t i = 0; i < {N}; i++) {{
        int64_t n = i * 2654435761LL + seed;
        n ^= (int64_t)((uint64_t)n >> 29);
        n = (n & (((int64_t)1 << 36) - 1)) + 1;
        int64_t x = 4097, y = (2 * x + n / (x * x)) / 3;
        while (y < x) {{ x = y; y = (2 * x + n / (x * x)) / 3; }}
        sum += x;
    }}
    printf("%lld\n", (long long)sum);
}}
"#
    );
    check("newton", &ops, &c);
}
