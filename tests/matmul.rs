//! Matrix multiplication: C = A B, of n by n integer matrices, an element at a
//! time; prints a weighted sum of C.

mod common;

use bf::asm::*;
use bf::Op;
use common::*;

pub fn matmul(n: i64) -> Vec<Op> {
    program(|o| {
        let (a, b, c, k, i, j, t, s) = (R1, R2, R3, R4, R5, R6, R7, R8);
        set(o, R9, (n * n) as u64);
        heap_alloc(o, a, R9);
        heap_alloc(o, b, R9);
        heap_alloc(o, c, R9);
        set(o, k, 0);
        while_loop(o, R0, |o| { mov(o, R0, k); lt_const(o, R0, n * n); }, |o| {
            mov(o, i, k);
            div_const(o, i, n);
            mov(o, j, k);
            rem_const(o, j, n);
            mov(o, t, i);
            mul_const(o, t, 7);
            mov(o, s, j);
            mul_const(o, s, 3);
            add_assign(o, t, s);
            rem_const(o, t, 17);
            sub_const(o, t, 8);
            store_index(o, a, k, t);
            mul_const(o, i, 5);
            mul_const(o, j, 11);
            add_assign(o, i, j);
            rem_const(o, i, 13);
            sub_const(o, i, 6);
            store_index(o, b, k, i);
            inc(o, k);
        });
        set(o, k, 0);
        while_loop(o, R0, |o| { mov(o, R0, k); lt_const(o, R0, n * n); }, |o| {
            mov(o, i, k);
            div_const(o, i, n);
            mul_const(o, i, n);
            mov(o, j, k);
            rem_const(o, j, n);
            set(o, s, 0);
            set(o, t, 0);
            while_loop(o, R0, |o| { mov(o, R0, t); lt_const(o, R0, n); }, |o| {
                // s += A[i][t] * B[t][j]
                mov(o, R9, i);
                add_assign(o, R9, t);
                load_index(o, R9, a, R9);
                push(o, R9);
                mov(o, R9, t);
                mul_const(o, R9, n);
                add_assign(o, R9, j);
                load_index(o, R9, b, R9);
                pop(o, R0);
                mul_assign(o, R9, R0);
                add_assign(o, s, R9);
                inc(o, t);
            });
            store_index(o, c, k, s);
            inc(o, k);
        });
        set(o, k, 0);
        set(o, s, 0);
        while_loop(o, R0, |o| { mov(o, R0, k); lt_const(o, R0, n * n); }, |o| {
            load_index(o, t, c, k);
            mov(o, i, k);
            rem_const(o, i, 7);
            inc(o, i);
            mul_assign(o, t, i);
            add_assign(o, s, t);
            inc(o, k);
        });
        putint(o, s);
        puts(o, "\n");
    })
}

pub fn matmul_c(n: i64) -> String {
    format!(
        r#"#include <stdio.h>
#include <stdint.h>
#define N {n}
static int64_t a[N * N], b[N * N], c[N * N];
int main(void) {{
    for (int64_t k = 0; k < N * N; k++) {{
        int64_t i = k / N, j = k % N;
        a[k] = (i * 7 + j * 3) % 17 - 8;
        b[k] = (i * 5 + j * 11) % 13 - 6;
    }}
    for (int64_t k = 0; k < N * N; k++) {{
        int64_t i = k / N * N, j = k % N, s = 0;
        for (int64_t t = 0; t < N; t++) s += a[i + t] * b[t * N + j];
        c[k] = s;
    }}
    int64_t s = 0;
    for (int64_t k = 0; k < N * N; k++) s += c[k] * (k % 7 + 1);
    printf("%lld\n", (long long)s);
    return 0;
}}
"#
    )
}

#[test]
fn matmul_prints_what_c_does() {
    check("matmul", &matmul(150), &matmul_c(150));
}
