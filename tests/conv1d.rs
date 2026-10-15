//! A 32-tap convolution over 40000 samples, 30 times (each output scaled
//! back to a byte as the next input); prints a checksum.

mod common;

use bf::asm::*;
use common::*;

const N: i64 = 40_000;
const K: i64 = 32;
const ROUNDS: i64 = 30;

#[test]
fn conv1d_prints_what_c_does() {
    let ops = program(|o| {
        let (x, y, w, i, k, s, t, u) = (R1, R2, R3, R4, R5, R6, R7, R8);
        heap_alloc_const(o, x, N);
        heap_alloc_const(o, y, N);
        heap_alloc_const(o, w, K);
        set(o, R9, 23);
        for_const(o, i, 0, N, R0, |o| {
            lcg(o, R9);
            mov(o, t, R9);
            rshu_const(o, t, 9);
            and_const(o, t, 255);
            store_index(o, x, i, t);
            set(o, t, 0);
            store_index(o, y, i, t);
        });
        for_const(o, k, 0, K, R0, |o| {
            mov(o, t, k);
            mul_const(o, t, 5);
            rem_const(o, t, 13);
            sub_const(o, t, 6);
            store_index(o, w, k, t);
        });
        for_const(o, R9, 0, ROUNDS, R0, |o| {
            for_const(o, i, 0, N - K, R0, |o| {
                set(o, s, 0);
                for_const(o, k, 0, K, R0, |o| {
                    mov(o, t, i);
                    add_assign(o, t, k);
                    load_index(o, t, x, t);
                    load_index(o, u, w, k);
                    mul_assign(o, t, u);
                    add_assign(o, s, t);
                });
                store_index(o, y, i, s);
            });
            for_const(o, i, 0, N, R0, |o| {
                load_index(o, t, y, i);
                rsh_const(o, t, 3);
                and_const(o, t, 255);
                store_index(o, x, i, t);
            });
        });
        set(o, s, 0);
        for_const(o, i, 0, N, R0, |o| {
            load_index(o, t, x, i);
            mov(o, u, i);
            rem_const(o, u, 5);
            inc(o, u);
            mul_assign(o, t, u);
            add_assign(o, s, t);
        });
        putint(o, s);
        puts(o, "\n");
    });
    let c = format!(
        r#"{C_HEAD}{LCG_C}
#define N {N}
#define K {K}
static int64_t x[N], y[N], w[K];
int main(void) {{
    int64_t seed = 23;
    for (int64_t i = 0; i < N; i++) {{ LCG(seed); x[i] = (seed >> 9) & 255; y[i] = 0; }}
    for (int64_t k = 0; k < K; k++) w[k] = k * 5 % 13 - 6;
    for (int r = 0; r < {ROUNDS}; r++) {{
        for (int64_t i = 0; i < N - K; i++) {{
            int64_t s = 0;
            for (int64_t k = 0; k < K; k++) s += x[i + k] * w[k];
            y[i] = s;
        }}
        for (int64_t i = 0; i < N; i++) x[i] = (y[i] >> 3) & 255;
    }}
    int64_t sum = 0;
    for (int64_t i = 0; i < N; i++) sum += x[i] * (i % 5 + 1);
    printf("%lld\n", (long long)sum);
}}
"#
    );
    check("conv1d", &ops, &c);
}
