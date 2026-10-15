//! The sum of the integer square roots of `i * 1000003` for `i` below
//! 2000000, through a function (a bit at a time).

mod common;

use bf::asm::*;
use common::*;

const N: i64 = 2_000_000;

#[test]
fn isqrtsum_prints_what_c_does() {
    let ops = program(|o| {
        isqrt_func(o);
        let (i, t, sum) = (R1, R2, R3);
        set(o, sum, 0);
        for_const(o, i, 0, N, R4, |o| {
            mov(o, t, i);
            mul_const(o, t, 1_000_003);
            call(o, "isqrt", &[t]);
            add_assign(o, sum, R0);
        });
        putint(o, sum);
        puts(o, "\n");
    });
    let c = format!(
        r#"{C_HEAD}{ISQRT_C}
int main(void) {{
    int64_t sum = 0;
    for (int64_t i = 0; i < {N}; i++) sum += isqrt(i * 1000003);
    printf("%lld\n", (long long)sum);
}}
"#
    );
    check("isqrtsum", &ops, &c);
}
