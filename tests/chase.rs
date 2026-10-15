//! Pointer chasing: a random cycle through 60000 slots (Sattolo's
//! shuffle), followed for 3 million steps, each to wherever the last one
//! says.

mod common;

use bf::asm::*;
use common::*;

const N: i64 = 60_000;
const STEPS: i64 = 3_000_000;

#[test]
fn chase_prints_what_c_does() {
    let ops = program(|o| {
        let (next, i, j, t, u, p, sum, seed) = (R1, R2, R3, R4, R5, R6, R7, R8);
        heap_alloc_const(o, next, N);
        for_const(o, i, 0, N, R0, |o| store_index(o, next, i, i));
        // Sattolo: swap each slot with one below it
        set(o, seed, 101);
        set_int(o, i, N - 1);
        while_loop(o, R0, |o| mov(o, R0, i), |o| {
            lcg(o, seed);
            mov(o, j, seed);
            rem_assign(o, j, i);
            load_index(o, t, next, i);
            load_index(o, u, next, j);
            store_index(o, next, i, u);
            store_index(o, next, j, t);
            dec(o, i);
        });
        set(o, p, 0);
        set(o, sum, 0);
        for_const(o, i, 0, STEPS, R0, |o| {
            load_index(o, p, next, p);
            add_assign(o, sum, p);
        });
        putint(o, sum);
        puts(o, "\n");
    });
    let c = format!(
        r#"{C_HEAD}{LCG_C}
#define N {N}
static int64_t next[N];
int main(void) {{
    for (int64_t i = 0; i < N; i++) next[i] = i;
    int64_t seed = 101;
    for (int64_t i = N - 1; i; i--) {{
        LCG(seed);
        int64_t j = seed % i, t = next[i];
        next[i] = next[j]; next[j] = t;
    }}
    int64_t p = 0, sum = 0;
    for (int64_t i = 0; i < {STEPS}; i++) {{ p = next[p]; sum += p; }}
    printf("%lld\n", (long long)sum);
}}
"#
    );
    check("chase", &ops, &c);
}
