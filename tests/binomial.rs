//! European call options on a binomial tree of 2000 steps, for 16 strikes,
//! in Q16: each step back updates the row in place (each node reads the
//! next, which the step hasn't reached yet).

mod common;

use bf::asm::*;
use common::*;

const N: i64 = 2000;
const STRIKES: i64 = 16;
const UP: i64 = 65_600;
const DOWN: i64 = 65_472;
const PU: i64 = 32_700;
const PD: i64 = 32_790;
const S0: i64 = 100 << 16;

#[test]
fn binomial_prints_what_c_does() {
    let ops = program(|o| {
        let (price, v, i, step, s, t, k, total) = (R1, R2, R3, R4, R5, R6, R7, R8);
        heap_alloc_const(o, price, N + 1);
        heap_alloc_const(o, v, N + 1);
        set_int(o, s, S0);
        for_const(o, i, 0, N, R0, |o| {
            mul_const(o, s, DOWN);
            rsh_const(o, s, 16);
        });
        for_const(o, i, 0, N + 1, R0, |o| {
            store_index(o, price, i, s);
            for _ in 0..2 {
                mul_const(o, s, UP);
                rsh_const(o, s, 16);
            }
        });
        set(o, total, 0);
        for_const(o, k, 0, STRIKES, R9, |o| {
            for_const(o, i, 0, N + 1, R0, |o| {
                load_index(o, t, price, i);
                mov(o, s, k);
                mul_const(o, s, 4 << 16);
                add_const(o, s, 70 << 16);
                sub_assign(o, t, s);
                set(o, s, 0);
                max_assign(o, t, s);
                store_index(o, v, i, t);
            });
            set_int(o, step, N);
            while_loop(o, R0, |o| mov(o, R0, step), |o| {
                dec(o, step);
                set(o, i, 0);
                while_loop(o, R0, |o| { mov(o, R0, i); le_assign(o, R0, step); }, |o| {
                    load_index(o, t, v, i);
                    mul_const(o, t, PD);
                    mov(o, s, i);
                    inc(o, s);
                    load_index(o, s, v, s);
                    mul_const(o, s, PU);
                    add_assign(o, t, s);
                    rsh_const(o, t, 16);
                    store_index(o, v, i, t);
                    inc(o, i);
                });
            });
            set(o, t, 0);
            load_index(o, t, v, t);
            add_assign(o, total, t);
            putint(o, t);
            puts(o, " ");
        });
        putint(o, total);
        puts(o, "\n");
    });
    let c = format!(
        r#"{C_HEAD}
#define N {N}
static int64_t price[N + 1], v[N + 1];
int main(void) {{
    int64_t s = {S0};
    for (int i = 0; i < N; i++) s = s * {DOWN} >> 16;
    for (int i = 0; i <= N; i++) {{
        price[i] = s;
        s = s * {UP} >> 16;
        s = s * {UP} >> 16;
    }}
    int64_t total = 0;
    for (int64_t k = 0; k < {STRIKES}; k++) {{
        for (int i = 0; i <= N; i++) {{
            int64_t t = price[i] - (k * (4 << 16) + (70 << 16));
            v[i] = t > 0 ? t : 0;
        }}
        for (int step = N - 1; step >= 0; step--)
            for (int i = 0; i <= step; i++) v[i] = (v[i] * {PD} + v[i + 1] * {PU}) >> 16;
        total += v[0];
        printf("%lld ", (long long)v[0]);
    }}
    printf("%lld\n", (long long)total);
}}
"#
    );
    check("binomial", &ops, &c);
}
