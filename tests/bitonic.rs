//! Bitonic sort of 16384 random keys, 8 times over new keys: the
//! compare-and-swap network, with partners found by xor.

mod common;

use bf::asm::*;
use common::*;

const N: i64 = 1 << 14;
const ROUNDS: i64 = 8;

#[test]
fn bitonic_prints_what_c_does() {
    let ops = program(|o| {
        let (a, i, k, j, p, x, y, t) = (R1, R2, R3, R4, R5, R6, R7, R8);
        heap_alloc_const(o, a, N);
        heap_alloc_const(o, R9, 3);
        let (seed, sum, round) = (g(0), g(1), g(2));
        set(o, &seed, 11);
        set(o, &sum, 0);
        for_const(o, &round, 0, ROUNDS, R0, |o| {
            for_const(o, i, 0, N, R0, |o| {
                lcg(o, &seed);
                store_index(o, a, i, &seed);
            });
            set(o, k, 2);
            while_loop(o, R0, |o| { mov(o, R0, k); le_const(o, R0, N); }, |o| {
                mov(o, j, k);
                rsh_const(o, j, 1);
                while_loop(o, R0, |o| mov(o, R0, j), |o| {
                    for_const(o, i, 0, N, R0, |o| {
                        mov(o, p, i);
                        xor_assign(o, p, j);
                        mov(o, t, p);
                        gt_assign(o, t, i);
                        begin_if(o, t);
                        load_index(o, x, a, i);
                        load_index(o, y, a, p);
                        mov(o, t, i);
                        and_assign(o, t, k);
                        begin_if(o, t);
                        mov(o, t, x);
                        lt_assign(o, t, y);
                        begin_else(o);
                        mov(o, t, x);
                        gt_assign(o, t, y);
                        end_if(o);
                        begin_if(o, t);
                        store_index(o, a, i, y);
                        store_index(o, a, p, x);
                        end_if(o);
                        end_if(o);
                    });
                    rsh_const(o, j, 1);
                });
                lsh_const(o, k, 1);
            });
            for_const(o, i, 0, N, R0, |o| {
                load_index(o, t, a, i);
                mov(o, x, i);
                and_const(o, x, 15);
                inc(o, x);
                mul_assign(o, t, x);
                add_assign(o, &sum, t);
            });
        });
        putint(o, &sum);
        puts(o, "\n");
    });
    let c = format!(
        r#"{C_HEAD}{LCG_C}
#define N {N}
static int64_t a[N];
int main(void) {{
    int64_t seed = 11, sum = 0;
    for (int round = 0; round < {ROUNDS}; round++) {{
        for (int64_t i = 0; i < N; i++) {{ LCG(seed); a[i] = seed; }}
        for (int64_t k = 2; k <= N; k <<= 1)
            for (int64_t j = k >> 1; j; j >>= 1)
                for (int64_t i = 0; i < N; i++) {{
                    int64_t p = i ^ j;
                    if (p > i) {{
                        int64_t x = a[i], y = a[p];
                        int sw = (i & k) ? x < y : x > y;
                        if (sw) {{ a[i] = y; a[p] = x; }}
                    }}
                }}
        for (int64_t i = 0; i < N; i++) sum += a[i] * ((i & 15) + 1);
    }}
    printf("%lld\n", (long long)sum);
}}
"#
    );
    check("bitonic", &ops, &c);
}
