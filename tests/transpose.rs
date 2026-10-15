//! A 200 by 200 matrix transposed back and forth 100 times (each element
//! written where its column says, an element at a time); prints a weighted
//! sum.

mod common;

use bf::asm::*;
use common::*;

const N: i64 = 200;
const ROUNDS: i64 = 100;

#[test]
fn transpose_prints_what_c_does() {
    let ops = program(|o| {
        let (a, b, i, j, t, u) = (R1, R2, R3, R4, R5, R6);
        heap_alloc_const(o, a, N * N);
        heap_alloc_const(o, b, N * N);
        for_const(o, i, 0, N * N, R0, |o| {
            mov(o, t, i);
            div_const(o, t, N);
            mul_const(o, t, 7);
            mov(o, u, i);
            rem_const(o, u, N);
            mul_const(o, u, 13);
            add_assign(o, t, u);
            rem_const(o, t, 1000);
            store_index(o, a, i, t);
        });
        for_const(o, R8, 0, ROUNDS, R7, |o| {
            for_const(o, i, 0, N, R0, |o| {
                for_const(o, j, 0, N, R9, |o| {
                    mov(o, t, i);
                    mul_const(o, t, N);
                    add_assign(o, t, j);
                    load_index(o, t, a, t);
                    mov(o, u, j);
                    mul_const(o, u, N);
                    add_assign(o, u, i);
                    store_index(o, b, u, t);
                });
            });
            mov(o, t, a);
            mov(o, a, b);
            mov(o, b, t);
        });
        set(o, j, 0);
        for_const(o, i, 0, N * N, R0, |o| {
            load_index(o, t, a, i);
            mov(o, u, i);
            rem_const(o, u, 11);
            inc(o, u);
            mul_assign(o, t, u);
            add_assign(o, j, t);
        });
        putint(o, j);
        puts(o, "\n");
    });
    let c = format!(
        r#"{C_HEAD}
#define N {N}
static int64_t m0[N * N], m1[N * N];
int main(void) {{
    int64_t *a = m0, *b = m1;
    for (int64_t i = 0; i < N * N; i++) a[i] = (i / N * 7 + i % N * 13) % 1000;
    for (int r = 0; r < {ROUNDS}; r++) {{
        for (int64_t i = 0; i < N; i++)
            for (int64_t j = 0; j < N; j++) b[j * N + i] = a[i * N + j];
        int64_t *t = a; a = b; b = t;
    }}
    int64_t sum = 0;
    for (int64_t i = 0; i < N * N; i++) sum += a[i] * (i % 11 + 1);
    printf("%lld\n", (long long)sum);
}}
"#
    );
    check("transpose", &ops, &c);
}
