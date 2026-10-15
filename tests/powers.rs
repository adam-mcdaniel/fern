//! `a[i] = i^5 % 1000003` for 90000 elements, by multiplying and reducing
//! four times, then their sum.

mod common;

use bf::asm::*;
use common::*;

const N: i64 = 90_000;

#[test]
fn powers_prints_what_c_does() {
    let ops = program(|o| {
        let (n, a, i, t, sum, flag) = (R1, R2, R3, R4, R5, R6);
        set(o, n, N as u64);
        heap_alloc(o, a, n);
        for_range(o, i, 0, n, flag, |o| {
            mov(o, t, i);
            for _ in 0..4 {
                mul_assign(o, t, i);
                rem_const(o, t, 1_000_003);
            }
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
        int64_t t = i;
        for (int k = 0; k < 4; k++) t = t * i % 1000003;
        a[i] = t;
    }}
    int64_t sum = 0;
    for (int64_t i = 0; i < {N}; i++) sum += a[i];
    printf("%lld\n", (long long)sum);
}}
"#
    );
    check("powers", &ops, &c);
}
