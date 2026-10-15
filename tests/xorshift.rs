//! A xorshift generator run 30 million times (shifts and `^`, every step
//! depending on the last), summing the low 8 bits of what it gives.

mod common;

use bf::asm::*;
use common::*;

const N: i64 = 30_000_000;

#[test]
fn xorshift_prints_what_c_does() {
    let ops = program(|o| {
        let (x, t, i, sum, flag) = (R1, R2, R3, R4, R5);
        set_int(o, x, 88_172_645_463_325_252);
        set(o, sum, 0);
        for_const(o, i, 0, N, flag, |o| {
            mov(o, t, x);
            lsh_const(o, t, 13);
            xor_assign(o, x, t);
            mov(o, t, x);
            rshu_const(o, t, 7);
            xor_assign(o, x, t);
            mov(o, t, x);
            lsh_const(o, t, 17);
            xor_assign(o, x, t);
            mov(o, t, x);
            and_const(o, t, 255);
            add_assign(o, sum, t);
        });
        putint(o, sum);
        puts(o, "\n");
    });
    let c = format!(
        r#"{C_HEAD}
int main(void) {{
    uint64_t x = 88172645463325252ull;
    int64_t sum = 0;
    for (int64_t i = 0; i < {N}; i++) {{ x ^= x << 13; x ^= x >> 7; x ^= x << 17; sum += x & 255; }}
    printf("%lld\n", (long long)sum);
}}
"#
    );
    check("xorshift", &ops, &c);
}
