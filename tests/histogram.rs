//! A histogram of ten million random bytes (each a write to a bucket only the
//! value says), then a weighted sum of it.

mod common;

use bf::asm::*;
use common::*;

const N: i64 = 10_000_000;

#[test]
fn histogram_prints_what_c_does() {
    let ops = program(|o| {
        let (hist, i, v, t, seed) = (R1, R2, R3, R4, R5);
        heap_alloc_const(o, hist, 256);
        set(o, t, 0);
        for_const(o, i, 0, 256, R0, |o| store_index(o, hist, i, t));
        set(o, seed, 99);
        for_const(o, i, 0, N, R0, |o| {
            lcg(o, seed);
            mov(o, v, seed);
            rshu_const(o, v, 12);
            and_const(o, v, 255);
            load_index(o, t, hist, v);
            inc(o, t);
            store_index(o, hist, v, t);
        });
        set(o, v, 0);
        for_const(o, i, 0, 256, R0, |o| {
            load_index(o, t, hist, i);
            mul_assign(o, t, i);
            add_assign(o, v, t);
        });
        putint(o, v);
        puts(o, "\n");
    });
    let c = format!(
        r#"{C_HEAD}{LCG_C}
static int64_t hist[256];
int main(void) {{
    int64_t seed = 99;
    for (int64_t i = 0; i < {N}; i++) {{ LCG(seed); hist[(seed >> 12) & 255]++; }}
    int64_t sum = 0;
    for (int64_t i = 0; i < 256; i++) sum += hist[i] * i;
    printf("%lld\n", (long long)sum);
}}
"#
    );
    check("histogram", &ops, &c);
}
