//! A 7-point stencil on a 30 by 30 by 30 grid (fixed faces), 100 steps;
//! prints a weighted sum.

mod common;

use bf::asm::*;
use common::*;

const N: i64 = 30;
const STEPS: i64 = 100;

#[test]
fn stencil3d_prints_what_c_does() {
    let cells = N * N * N;
    let ops = program(|o| {
        let (u, v, i, s, t, k) = (R1, R2, R3, R4, R5, R6);
        heap_alloc_const(o, u, cells);
        heap_alloc_const(o, v, cells);
        for_const(o, i, 0, cells, R0, |o| {
            mov(o, t, i);
            mul_const(o, t, 104_729);
            rem_const(o, t, 4096);
            store_index(o, u, i, t);
            store_index(o, v, i, t);
        });
        for_const(o, R8, 0, STEPS, R0, |o| {
            for_const(o, i, N * N + N + 1, cells - N * N - N - 1, R0, |o| {
                load_index(o, s, u, i);
                add_assign(o, s, s);
                for d in [-1, 1, -N, N, -N * N, N * N] {
                    mov(o, k, i);
                    add_const(o, k, d);
                    load_index(o, t, u, k);
                    add_assign(o, s, t);
                }
                rsh_const(o, s, 3);
                store_index(o, v, i, s);
            });
            mov(o, t, u);
            mov(o, u, v);
            mov(o, v, t);
        });
        set(o, s, 0);
        for_const(o, i, 0, cells, R0, |o| {
            load_index(o, t, u, i);
            mov(o, k, i);
            rem_const(o, k, 7);
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
#define CELLS (N * N * N)
static int64_t a[CELLS], b[CELLS];
int main(void) {{
    int64_t *u = a, *v = b;
    for (int64_t i = 0; i < CELLS; i++) u[i] = v[i] = i * 104729 % 4096;
    for (int s = 0; s < {STEPS}; s++) {{
        for (int64_t i = N * N + N + 1; i < CELLS - N * N - N - 1; i++)
            v[i] = (2 * u[i] + u[i - 1] + u[i + 1] + u[i - N] + u[i + N] + u[i - N * N] + u[i + N * N]) >> 3;
        int64_t *t = u; u = v; v = t;
    }}
    int64_t sum = 0;
    for (int64_t i = 0; i < CELLS; i++) sum += u[i] * (i % 7 + 1);
    printf("%lld\n", (long long)sum);
}}
"#
    );
    check("stencil3d", &ops, &c);
}
