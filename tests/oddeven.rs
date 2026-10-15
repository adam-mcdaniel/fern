//! Odd-even transposition sort of 8000 random numbers (as many phases, each
//! comparing and swapping disjoint neighbours); prints a weighted sum.

mod common;

use bf::asm::*;
use common::*;

const N: i64 = 8000;

#[test]
fn oddeven_prints_what_c_does() {
    let ops = program(|o| {
        let (x, p, i, a, b, t, k, seed) = (R1, R2, R3, R4, R5, R6, R8, R9);
        heap_alloc_const(o, x, N);
        set(o, seed, 7);
        for_const(o, i, 0, N, R0, |o| {
            lcg(o, seed);
            mov(o, t, seed);
            rshu_const(o, t, 8);
            rem_const(o, t, 100_000);
            store_index(o, x, i, t);
        });
        for_const(o, p, 0, N, R7, |o| {
            mov(o, i, p);
            and_const(o, i, 1);
            while_loop(o, R0, |o| { mov(o, R0, i); inc(o, R0); lt_const(o, R0, N); }, |o| {
                load_index(o, a, x, i);
                mov(o, k, i);
                inc(o, k);
                load_index(o, b, x, k);
                mov(o, t, a);
                gt_assign(o, t, b);
                begin_if(o, t);
                store_index(o, x, i, b);
                store_index(o, x, k, a);
                end_if(o);
                add_const(o, i, 2);
            });
        });
        set(o, a, 0);
        for_const(o, i, 0, N, R0, |o| {
            load_index(o, t, x, i);
            mov(o, k, i);
            inc(o, k);
            mul_assign(o, t, k);
            add_assign(o, a, t);
        });
        putint(o, a);
        puts(o, "\n");
    });
    let c = format!(
        r#"{C_HEAD}{LCG_C}
#define N {N}
static int64_t x[N];
int main(void) {{
    int64_t seed = 7;
    for (int64_t i = 0; i < N; i++) {{ LCG(seed); x[i] = (seed >> 8) % 100000; }}
    for (int64_t p = 0; p < N; p++)
        for (int64_t i = p & 1; i + 1 < N; i += 2)
            if (x[i] > x[i + 1]) {{ int64_t t = x[i]; x[i] = x[i + 1]; x[i + 1] = t; }}
    int64_t sum = 0;
    for (int64_t i = 0; i < N; i++) sum += x[i] * (i + 1);
    printf("%lld\n", (long long)sum);
}}
"#
    );
    check("oddeven", &ops, &c);
}
