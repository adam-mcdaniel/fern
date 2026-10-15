//! Spectral norm (as in the benchmarks game), in Q30: the largest singular
//! value of the infinite matrix A(i, j) = 1 / ((i + j)(i + j + 1) / 2 + i + 1),
//! cut to n by n, by the power method. Prints u.v, v.v and the norm (Q10).

mod common;

use bf::asm::*;
use bf::Op;
use common::*;

pub fn spectral(n: i64, iterations: i64) -> Vec<Op> {
    program(|o| {
        let (u, v, tmp, i, j, sum, t, d) = (R1, R2, R3, R4, R5, R6, R7, R8);
        set(o, R9, n as u64);
        heap_alloc(o, u, R9);
        heap_alloc(o, v, R9);
        heap_alloc(o, tmp, R9);
        set(o, i, 0);
        set_int(o, t, 1 << 30);
        while_loop(o, R0, |o| { mov(o, R0, i); lt_const(o, R0, n); }, |o| {
            store_index(o, u, i, t);
            inc(o, i);
        });
        // out = A x (or A^T x)
        let mul = |o: &mut dyn Program, x: &Location, out: &Location, transposed: bool| {
            set(o, i, 0);
            while_loop(o, R0, |o| { mov(o, R0, i); lt_const(o, R0, n); }, |o| {
                set(o, sum, 0);
                set(o, j, 0);
                while_loop(o, R0, |o| { mov(o, R0, j); lt_const(o, R0, n); }, |o| {
                    mov(o, d, i);
                    add_assign(o, d, j);
                    mov(o, t, d);
                    inc(o, t);
                    mul_assign(o, d, t);
                    rsh_const(o, d, 1);
                    add_assign(o, d, if transposed { j } else { i });
                    inc(o, d);
                    load_index(o, t, x, j);
                    div_assign(o, t, d);
                    add_assign(o, sum, t);
                    inc(o, j);
                });
                store_index(o, out, i, sum);
                inc(o, i);
            });
        };
        set(o, R9, 0);
        while_loop(o, R0, |o| { mov(o, R0, R9); lt_const(o, R0, iterations); }, |o| {
            mul(o, u, tmp, false);
            mul(o, tmp, v, true);
            mul(o, v, tmp, false);
            mul(o, tmp, u, true);
            inc(o, R9);
        });
        // u.v and v.v, each a little smaller to fit
        set(o, i, 0);
        set(o, sum, 0);
        set(o, d, 0);
        while_loop(o, R0, |o| { mov(o, R0, i); lt_const(o, R0, n); }, |o| {
            load_index(o, t, v, i);
            rsh_const(o, t, 20);
            load_index(o, j, u, i);
            rsh_const(o, j, 20);
            mul_assign(o, j, t);
            add_assign(o, sum, j);
            mul_assign(o, t, t);
            add_assign(o, d, t);
            inc(o, i);
        });
        putint(o, sum);
        puts(o, " ");
        putint(o, d);
        puts(o, " ");
        rsh_const(o, d, 20);
        div_assign(o, sum, d);
        mov(o, R9, sum);
        isqrt_inline(o, R9);
        putint(o, R9);
        puts(o, "\n");
    })
}

pub fn spectral_c(n: i64, iterations: i64) -> String {
    format!(
        r#"#include <stdio.h>
#include <stdint.h>
#define N {n}
{ISQRT_C}
static int64_t u[N], v[N], tmp[N];
static void mul(const int64_t *x, int64_t *out, int transposed) {{
    for (int64_t i = 0; i < N; i++) {{
        int64_t s = 0;
        for (int64_t j = 0; j < N; j++) {{
            int64_t d = (i + j) * (i + j + 1) >> 1;
            d += (transposed ? j : i) + 1;
            s += x[j] / d;
        }}
        out[i] = s;
    }}
}}
int main(void) {{
    for (int i = 0; i < N; i++) u[i] = (int64_t)1 << 30;
    for (int k = 0; k < {iterations}; k++) {{
        mul(u, tmp, 0); mul(tmp, v, 1);
        mul(v, tmp, 0); mul(tmp, u, 1);
    }}
    int64_t uv = 0, vv = 0;
    for (int i = 0; i < N; i++) {{
        int64_t a = v[i] >> 20, b = u[i] >> 20;
        uv += b * a; vv += a * a;
    }}
    printf("%lld %lld %lld\n", (long long)uv, (long long)vv, (long long)isqrt(uv / (vv >> 20)));
    return 0;
}}
"#
    )
}

#[test]
fn spectral_prints_what_c_does() {
    check("spectral", &spectral(250, 40), &spectral_c(250, 40));
}
