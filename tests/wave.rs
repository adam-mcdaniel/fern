//! The 1D wave equation on 30000 points (fixed ends), 1000 steps from a
//! bump in the middle, in Q16; prints a weighted sum.

mod common;

use bf::asm::*;
use common::*;

const N: i64 = 30_000;
const STEPS: i64 = 1000;

#[test]
fn wave_prints_what_c_does() {
    let ops = program(|o| {
        let (prev, cur, next, i, s, t, k) = (R1, R2, R3, R4, R5, R6, R7);
        for a in [prev, cur, next] {
            heap_alloc_const(o, a, N);
        }
        for_const(o, i, 0, N, R0, |o| {
            // a bump: 65536 - (i - N/2)^2 * 16, where that's above 0
            mov(o, t, i);
            sub_const(o, t, N / 2);
            mul_assign(o, t, t);
            mul_const(o, t, 16);
            neg_assign(o, t);
            add_const(o, t, 65_536);
            mov(o, s, t);
            lt_const(o, s, 0);
            begin_if(o, s);
            set(o, t, 0);
            end_if(o);
            store_index(o, prev, i, t);
            store_index(o, cur, i, t);
            set(o, s, 0);
            store_index(o, next, i, s);
        });
        for_const(o, R8, 0, STEPS, R9, |o| {
            for_const(o, i, 1, N - 1, R0, |o| {
                load_index(o, s, cur, i);
                add_assign(o, s, s);
                load_index(o, t, prev, i);
                sub_assign(o, s, t);
                mov(o, k, i);
                dec(o, k);
                load_index(o, t, cur, k);
                add_const(o, k, 2);
                load_index(o, k, cur, k);
                add_assign(o, t, k);
                load_index(o, k, cur, i);
                sub_assign(o, t, k);
                sub_assign(o, t, k);
                rsh_const(o, t, 2);
                add_assign(o, s, t);
                store_index(o, next, i, s);
            });
            mov(o, t, prev);
            mov(o, prev, cur);
            mov(o, cur, next);
            mov(o, next, t);
        });
        set(o, s, 0);
        for_const(o, i, 0, N, R0, |o| {
            load_index(o, t, cur, i);
            mov(o, k, i);
            rem_const(o, k, 9);
            inc(o, k);
            mul_assign(o, t, k);
            add_assign(o, s, t);
        });
        putint(o, s);
        puts(o, "\n");
    });
    let c = format!(
        r#"{C_HEAD}
#define N {N}
static int64_t a0[N], a1[N], a2[N];
int main(void) {{
    int64_t *prev = a0, *cur = a1, *next = a2;
    for (int64_t i = 0; i < N; i++) {{
        int64_t t = 65536 - (i - N / 2) * (i - N / 2) * 16;
        if (t < 0) t = 0;
        prev[i] = cur[i] = t;
        next[i] = 0;
    }}
    for (int s = 0; s < {STEPS}; s++) {{
        for (int64_t i = 1; i < N - 1; i++)
            next[i] = 2 * cur[i] - prev[i] + ((cur[i - 1] + cur[i + 1] - 2 * cur[i]) >> 2);
        int64_t *t = prev; prev = cur; cur = next; next = t;
    }}
    int64_t sum = 0;
    for (int64_t i = 0; i < N; i++) sum += cur[i] * (i % 9 + 1);
    printf("%lld\n", (long long)sum);
}}
"#
    );
    check("wave", &ops, &c);
}
