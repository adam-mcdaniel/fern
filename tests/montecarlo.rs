//! Estimating pi: of ten million points, each from a hash of its index
//! (splitmix-like), how many are in the quarter circle.

mod common;

use bf::asm::*;
use common::*;

const N: i64 = 10_000_000;
const K1: u64 = 0x9E37_79B9_7F4A_7C15;
const K2: u64 = 0xBF58_476D_1CE4_E5B9;

#[test]
fn montecarlo_prints_what_c_does() {
    let ops = program(|o| {
        let (i, h, t, x, y, count) = (R1, R2, R3, R4, R5, R6);
        set(o, count, 0);
        for_const(o, i, 0, N, R7, |o| {
            mov(o, h, i);
            mul_const(o, h, K1 as i64);
            mov(o, t, h);
            rshu_const(o, t, 31);
            xor_assign(o, h, t);
            mul_const(o, h, K2 as i64);
            mov(o, x, h);
            and_const(o, x, 0xffff);
            mov(o, y, h);
            rshu_const(o, y, 16);
            and_const(o, y, 0xffff);
            mul_assign(o, x, x);
            mul_assign(o, y, y);
            add_assign(o, x, y);
            lt_const(o, x, 1 << 32);
            add_assign(o, count, x);
        });
        putint(o, count);
        puts(o, "\n");
    });
    let c = format!(
        r#"{C_HEAD}
int main(void) {{
    int64_t count = 0;
    for (int64_t i = 0; i < {N}; i++) {{
        uint64_t h = (uint64_t)i * {K1}ull;
        h ^= h >> 31;
        h *= {K2}ull;
        int64_t x = h & 0xffff, y = (h >> 16) & 0xffff;
        count += x * x + y * y < ((int64_t)1 << 32);
    }}
    printf("%lld\n", (long long)count);
}}
"#
    );
    check("montecarlo", &ops, &c);
}
