//! Quicksort of 20000 random numbers (Lomuto partitions, with a stack of
//! ranges still to sort); prints a weighted sum.

mod common;

use bf::asm::*;
use common::*;

const N: i64 = 20_000;

#[test]
fn quicksort_prints_what_c_does() {
    let ops = program(|o| {
        let (a, stk, sp, lo, hi, i, j, t) = (R1, R2, R3, R4, R5, R6, R7, R8);
        heap_alloc_const(o, a, N);
        heap_alloc_const(o, stk, 2 * N);
        set(o, R9, 13);
        for_const(o, i, 0, N, R0, |o| {
            lcg(o, R9);
            mov(o, t, R9);
            rshu_const(o, t, 3);
            rem_const(o, t, 1_000_000);
            store_index(o, a, i, t);
        });
        // the ranges to sort, as pairs
        set(o, sp, 0);
        set(o, t, 0);
        store_index(o, stk, sp, t);
        inc(o, sp);
        set(o, t, (N - 1) as u64);
        store_index(o, stk, sp, t);
        inc(o, sp);
        while_loop(o, R0, |o| mov(o, R0, sp), |o| {
            dec(o, sp);
            load_index(o, hi, stk, sp);
            dec(o, sp);
            load_index(o, lo, stk, sp);
            mov(o, t, lo);
            lt_assign(o, t, hi);
            begin_if(o, t);
            // partition around the last
            load_index(o, R9, a, hi);
            mov(o, i, lo);
            mov(o, j, lo);
            while_loop(o, R0, |o| { mov(o, R0, j); lt_assign(o, R0, hi); }, |o| {
                load_index(o, t, a, j);
                mov(o, R0, t);
                lt_assign(o, R0, R9);
                begin_if(o, R0);
                load_index(o, R0, a, i);
                store_index(o, a, j, R0);
                store_index(o, a, i, t);
                inc(o, i);
                end_if(o);
                inc(o, j);
            });
            load_index(o, t, a, i);
            store_index(o, a, hi, t);
            store_index(o, a, i, R9);
            // both sides, to do
            store_index(o, stk, sp, lo);
            inc(o, sp);
            mov(o, t, i);
            dec(o, t);
            store_index(o, stk, sp, t);
            inc(o, sp);
            mov(o, t, i);
            inc(o, t);
            store_index(o, stk, sp, t);
            inc(o, sp);
            store_index(o, stk, sp, hi);
            inc(o, sp);
            end_if(o);
        });
        set(o, j, 0);
        for_const(o, i, 0, N, R0, |o| {
            load_index(o, t, a, i);
            mov(o, R9, i);
            rem_const(o, R9, 89);
            inc(o, R9);
            mul_assign(o, t, R9);
            add_assign(o, j, t);
        });
        putint(o, j);
        puts(o, "\n");
    });
    let c = format!(
        r#"{C_HEAD}{LCG_C}
#define N {N}
static int64_t a[N], stk[2 * N];
int main(void) {{
    int64_t seed = 13, sp = 0;
    for (int64_t i = 0; i < N; i++) {{ LCG(seed); a[i] = (seed >> 3) % 1000000; }}
    stk[sp++] = 0; stk[sp++] = N - 1;
    while (sp) {{
        int64_t hi = stk[--sp], lo = stk[--sp];
        if (lo < hi) {{
            int64_t pivot = a[hi], i = lo;
            for (int64_t j = lo; j < hi; j++) {{
                int64_t t = a[j];
                if (t < pivot) {{ a[j] = a[i]; a[i] = t; i++; }}
            }}
            a[hi] = a[i]; a[i] = pivot;
            stk[sp++] = lo; stk[sp++] = i - 1; stk[sp++] = i + 1; stk[sp++] = hi;
        }}
    }}
    int64_t sum = 0;
    for (int64_t i = 0; i < N; i++) sum += a[i] * (i % 89 + 1);
    printf("%lld\n", (long long)sum);
}}
"#
    );
    check("quicksort", &ops, &c);
}
