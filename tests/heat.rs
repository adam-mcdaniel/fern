//! Heat diffusion: Jacobi steps of the 2D heat equation on a 200 by 200
//! grid (fixed edges), each cell becoming a weighted average of itself and
//! its four neighbours; prints a weighted sum of the grid.

mod common;

use bf::asm::*;
use common::*;

const W: i64 = 200;
const STEPS: i64 = 600;

#[test]
fn heat_prints_what_c_does() {
    let cells = W * W;
    let ops = program(|o| {
        let (u, v, i, s, t, k) = (R1, R2, R3, R4, R5, R6);
        set(o, R7, cells as u64);
        heap_alloc(o, u, R7);
        heap_alloc(o, v, R7);
        for_const(o, i, 0, cells, R0, |o| {
            mov(o, t, i);
            mul_const(o, t, 7919);
            rem_const(o, t, 1000);
            mul_const(o, t, 64);
            store_index(o, u, i, t);
            store_index(o, v, i, t);
        });
        for_const(o, R8, 0, STEPS, R7, |o| {
            for_const(o, i, W + 1, cells - W - 1, R0, |o| {
                load_index(o, s, u, i);
                add_assign(o, s, s);
                add_assign(o, s, s);
                for d in [-1, 1, -W, W] {
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
            rem_const(o, k, 13);
            inc(o, k);
            mul_assign(o, t, k);
            add_assign(o, s, t);
        });
        putint(o, s);
        puts(o, "\n");
    });
    let c = format!(
        r#"{C_HEAD}
#define W {W}
static int64_t a[W * W], b[W * W];
int main(void) {{
    int64_t *u = a, *v = b;
    for (int64_t i = 0; i < W * W; i++) u[i] = v[i] = i * 7919 % 1000 * 64;
    for (int s = 0; s < {STEPS}; s++) {{
        for (int64_t i = W + 1; i < W * W - W - 1; i++)
            v[i] = (4 * u[i] + u[i - 1] + u[i + 1] + u[i - W] + u[i + W]) >> 3;
        int64_t *t = u; u = v; v = t;
    }}
    int64_t sum = 0;
    for (int64_t i = 0; i < W * W; i++) sum += u[i] * (i % 13 + 1);
    printf("%lld\n", (long long)sum);
}}
"#
    );
    check("heat", &ops, &c);
}
