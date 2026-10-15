//! Laplace's equation on a 150x150 grid by Jacobi sweeps (the top edge held
//! high), until no point moves by more than 2 or 3000 sweeps: each sweep a
//! largest-change reduction; prints how many it took and a checksum.

mod common;

use bf::asm::*;
use common::*;

const G: i64 = 150;
const MAX_SWEEPS: i64 = 3000;
const TOP: i64 = 1 << 20;
// the globals
const MAXD: i64 = 0;
const SWEEPS: i64 = 1;
const ROW: i64 = 2;
const FLAG: i64 = 3;

#[test]
fn jacobi2d_prints_what_c_does() {
    let ops = program(|o| {
        let (u, v, i, j, at, s, t, w) = (R1, R2, R3, R4, R5, R6, R7, R8);
        heap_alloc_const(o, R9, 4);
        heap_alloc_const(o, u, G * G);
        heap_alloc_const(o, v, G * G);
        for_const(o, i, 0, G * G, R0, |o| {
            mov(o, t, i);
            lt_const(o, t, G);
            mul_const(o, t, TOP);
            store_index(o, u, i, t);
            store_index(o, v, i, t);
        });
        set(o, &g(SWEEPS), 0);
        set_int(o, &g(MAXD), i64::MAX);
        while_loop(o, &g(FLAG), |o| {
            mov(o, &g(FLAG), &g(MAXD));
            gt_const(o, &g(FLAG), 2);
            mov(o, R0, &g(SWEEPS));
            lt_const(o, R0, MAX_SWEEPS);
            land_assign(o, &g(FLAG), R0);
        }, |o| {
            set(o, &g(MAXD), 0);
            for_const(o, i, 1, G - 1, &g(ROW), |o| {
                for_const(o, j, 1, G - 1, R0, |o| {
                    mov(o, at, i);
                    mul_const(o, at, G);
                    add_assign(o, at, j);
                    mov(o, w, at);
                    sub_const(o, w, G);
                    load_index(o, s, u, w);
                    add_const(o, w, 2 * G);
                    load_index(o, t, u, w);
                    add_assign(o, s, t);
                    mov(o, w, at);
                    dec(o, w);
                    load_index(o, t, u, w);
                    add_assign(o, s, t);
                    add_const(o, w, 2);
                    load_index(o, t, u, w);
                    add_assign(o, s, t);
                    rsh_const(o, s, 2);
                    store_index(o, v, at, s);
                    load_index(o, t, u, at);
                    sub_assign(o, t, s);
                    abs_assign(o, t);
                    max_assign(o, &g(MAXD), t);
                });
            });
            mov(o, t, u);
            mov(o, u, v);
            mov(o, v, t);
            inc(o, &g(SWEEPS));
        });
        set(o, s, 0);
        for_const(o, i, 0, G * G, R0, |o| {
            load_index(o, t, u, i);
            mov(o, w, i);
            rem_const(o, w, 7);
            inc(o, w);
            mul_assign(o, t, w);
            add_assign(o, s, t);
        });
        putint(o, &g(SWEEPS));
        puts(o, " ");
        putint(o, s);
        puts(o, "\n");
    });
    let c = format!(
        r#"{C_HEAD}
#define G {G}
static int64_t a0[G * G], a1[G * G];
int main(void) {{
    int64_t *u = a0, *v = a1;
    for (int64_t i = 0; i < G * G; i++) u[i] = v[i] = (i < G) * {TOP};
    int64_t sweeps = 0, maxd = INT64_MAX;
    while (maxd > 2 && sweeps < {MAX_SWEEPS}) {{
        maxd = 0;
        for (int64_t i = 1; i < G - 1; i++)
            for (int64_t j = 1; j < G - 1; j++) {{
                int64_t at = i * G + j;
                int64_t s = (u[at - G] + u[at + G] + u[at - 1] + u[at + 1]) >> 2;
                v[at] = s;
                int64_t d = u[at] - s;
                if (d < 0) d = -d;
                if (d > maxd) maxd = d;
            }}
        int64_t *t = u; u = v; v = t;
        sweeps++;
    }}
    int64_t s = 0;
    for (int64_t i = 0; i < G * G; i++) s += u[i] * (i % 7 + 1);
    printf("%lld %lld\n", (long long)sweeps, (long long)s);
}}
"#
    );
    check("jacobi2d", &ops, &c);
}
