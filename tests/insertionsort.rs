//! Insertion sort of 6000 random numbers; prints a weighted sum.

mod common;

use bf::asm::*;
use common::*;

const N: i64 = 6000;

#[test]
fn insertionsort_prints_what_c_does() {
    let ops = program(|o| {
        let (a, i, j, key, t, u, seed) = (R1, R2, R3, R4, R5, R6, R7);
        heap_alloc_const(o, a, N);
        set(o, seed, 17);
        for_const(o, i, 0, N, R0, |o| {
            lcg(o, seed);
            mov(o, t, seed);
            rshu_const(o, t, 4);
            rem_const(o, t, 1_000_000);
            store_index(o, a, i, t);
        });
        for_const(o, i, 1, N, R0, |o| {
            load_index(o, key, a, i);
            mov(o, j, i);
            dec(o, j);
            // shift up what's bigger
            begin_loop(o);
            mov(o, t, j);
            lt_const(o, t, 0);
            break_if(o, t);
            load_index(o, t, a, j);
            mov(o, u, t);
            gt_assign(o, u, key);
            lnot_assign(o, u);
            break_if(o, u);
            mov(o, u, j);
            inc(o, u);
            store_index(o, a, u, t);
            dec(o, j);
            end_loop(o);
            inc(o, j);
            store_index(o, a, j, key);
        });
        set(o, u, 0);
        for_const(o, i, 0, N, R0, |o| {
            load_index(o, t, a, i);
            mov(o, j, i);
            rem_const(o, j, 101);
            inc(o, j);
            mul_assign(o, t, j);
            add_assign(o, u, t);
        });
        putint(o, u);
        puts(o, "\n");
    });
    let c = format!(
        r#"{C_HEAD}{LCG_C}
#define N {N}
static int64_t a[N];
int main(void) {{
    int64_t seed = 17;
    for (int64_t i = 0; i < N; i++) {{ LCG(seed); a[i] = (seed >> 4) % 1000000; }}
    for (int64_t i = 1; i < N; i++) {{
        int64_t key = a[i], j = i - 1;
        while (j >= 0 && a[j] > key) {{ a[j + 1] = a[j]; j--; }}
        a[j + 1] = key;
    }}
    int64_t sum = 0;
    for (int64_t i = 0; i < N; i++) sum += a[i] * (i % 101 + 1);
    printf("%lld\n", (long long)sum);
}}
"#
    );
    check("insertionsort", &ops, &c);
}
