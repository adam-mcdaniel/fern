//! A 250 by 250 matrix times a vector, 300 times over (each result reduced
//! modulo 1000003 and multiplied again); prints the vector's sum.

mod common;

use bf::asm::*;
use common::*;

const N: i64 = 250;
const ROUNDS: i64 = 300;

#[test]
fn matvec_prints_what_c_does() {
    let ops = program(|o| {
        let (m, v, w, i, j, s, t, u) = (R1, R2, R3, R4, R5, R6, R7, R8);
        heap_alloc_const(o, m, N * N);
        heap_alloc_const(o, v, N);
        heap_alloc_const(o, w, N);
        for_const(o, i, 0, N * N, R0, |o| {
            mov(o, t, i);
            div_const(o, t, N);
            inc(o, t);
            mov(o, u, i);
            rem_const(o, u, N);
            add_const(o, u, 3);
            mul_assign(o, t, u);
            rem_const(o, t, 101);
            store_index(o, m, i, t);
        });
        for_const(o, j, 0, N, R0, |o| {
            mov(o, t, j);
            rem_const(o, t, 7);
            inc(o, t);
            store_index(o, v, j, t);
        });
        for_const(o, R9, 0, ROUNDS, R0, |o| {
            for_const(o, i, 0, N, R0, |o| {
                set(o, s, 0);
                for_const(o, j, 0, N, R0, |o| {
                    mov(o, t, i);
                    mul_const(o, t, N);
                    add_assign(o, t, j);
                    load_index(o, t, m, t);
                    load_index(o, u, v, j);
                    mul_assign(o, t, u);
                    add_assign(o, s, t);
                });
                rem_const(o, s, 1_000_003);
                store_index(o, w, i, s);
            });
            mov(o, t, v);
            mov(o, v, w);
            mov(o, w, t);
        });
        set(o, s, 0);
        for_const(o, j, 0, N, R0, |o| {
            load_index(o, t, v, j);
            add_assign(o, s, t);
        });
        putint(o, s);
        puts(o, "\n");
    });
    let c = format!(
        r#"{C_HEAD}
#define N {N}
static int64_t m[N * N], v0[N], v1[N];
int main(void) {{
    int64_t *v = v0, *w = v1;
    for (int64_t i = 0; i < N * N; i++) m[i] = (i / N + 1) * (i % N + 3) % 101;
    for (int64_t j = 0; j < N; j++) v[j] = j % 7 + 1;
    for (int r = 0; r < {ROUNDS}; r++) {{
        for (int64_t i = 0; i < N; i++) {{
            int64_t s = 0;
            for (int64_t j = 0; j < N; j++) s += m[i * N + j] * v[j];
            w[i] = s % 1000003;
        }}
        int64_t *t = v; v = w; w = t;
    }}
    int64_t sum = 0;
    for (int64_t j = 0; j < N; j++) sum += v[j];
    printf("%lld\n", (long long)sum);
}}
"#
    );
    check("matvec", &ops, &c);
}
