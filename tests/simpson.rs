//! Pi, by the midpoint rule for the integral of 4 / (1 + x^2) from 0 to 1
//! over five million intervals, in Q30: a division each.

mod common;

use bf::asm::*;
use common::*;

const N: i64 = 5_000_000;
const ONE: i64 = 1 << 30;

#[test]
fn simpson_prints_what_c_does() {
    let ops = program(|o| {
        let (i, x, f, sum, h) = (R1, R2, R3, R4, R5);
        set_int(o, h, ONE / N);
        set(o, sum, 0);
        for_const(o, i, 0, N, R0, |o| {
            mov(o, x, i);
            mul_assign(o, x, h);
            mov(o, f, h);
            rsh_const(o, f, 1);
            add_assign(o, x, f);
            mul_assign(o, x, x);
            rsh_const(o, x, 30);
            add_const(o, x, ONE);
            set_int(o, f, 1 << 62);
            div_assign(o, f, x);
            add_assign(o, sum, f);
        });
        putint(o, sum);
        puts(o, " ");
        div_const(o, sum, N);
        putint(o, sum);
        puts(o, "\n");
    });
    let c = format!(
        r#"{C_HEAD}
int main(void) {{
    int64_t h = {ONE} / {N}, sum = 0;
    for (int64_t i = 0; i < {N}; i++) {{
        int64_t x = i * h + (h >> 1);
        x = (x * x >> 30) + {ONE};
        sum += ((int64_t)1 << 62) / x;
    }}
    printf("%lld %lld\n", (long long)sum, (long long)(sum / {N}));
}}
"#
    );
    check("simpson", &ops, &c);
}
