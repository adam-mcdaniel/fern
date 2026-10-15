//! A polynomial of degree 20 (with coefficients 1 to 21), by Horner's rule,
//! at each of 20000 points, modulo 65537, then their sum.

mod common;

use bf::asm::*;
use common::*;

const N: i64 = 20_000;

#[test]
fn polynomial_prints_what_c_does() {
    let ops = program(|o| {
        let (n, a, i, t, sum, flag, k) = (R1, R2, R3, R4, R5, R6, R7);
        set(o, n, N as u64);
        heap_alloc(o, a, n);
        for_range(o, i, 0, n, flag, |o| {
            set(o, t, 0);
            for_const(o, k, 0, 21, R8, |o| {
                mul_assign(o, t, i);
                add_assign(o, t, k);
                inc(o, t);
                rem_const(o, t, 65_537);
            });
            store_index(o, a, i, t);
        });
        set(o, sum, 0);
        for_range(o, i, 0, n, flag, |o| {
            load_index(o, t, a, i);
            add_assign(o, sum, t);
        });
        putint(o, sum);
        puts(o, "\n");
    });
    let c = format!(
        r#"{C_HEAD}
static int64_t a[{N}];
int main(void) {{
    for (int64_t i = 0; i < {N}; i++) {{
        int64_t t = 0;
        for (int64_t k = 0; k < 21; k++) t = (t * i + k + 1) % 65537;
        a[i] = t;
    }}
    int64_t sum = 0;
    for (int64_t i = 0; i < {N}; i++) sum += a[i];
    printf("%lld\n", (long long)sum);
}}
"#
    );
    check("polynomial", &ops, &c);
}
