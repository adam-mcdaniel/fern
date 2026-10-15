//! Floyd-Warshall: the shortest paths between every pair of 150 nodes of a
//! dense graph; prints their total. (Each row of the middle loop reads the
//! row being worked through, which is also written: the checks say so, and
//! it runs in order.)

mod common;

use bf::asm::*;
use common::*;

const N: i64 = 150;

#[test]
fn floyd_prints_what_c_does() {
    let ops = program(|o| {
        let (d, k, i, j, a, b, t, u) = (R1, R2, R3, R4, R5, R6, R7, R8);
        heap_alloc_const(o, d, N * N);
        for_const(o, i, 0, N, R0, |o| {
            for_const(o, j, 0, N, R9, |o| {
                mov(o, t, i);
                mul_const(o, t, 31);
                mov(o, u, j);
                mul_const(o, u, 17);
                add_assign(o, t, u);
                rem_const(o, t, 97);
                inc(o, t);
                mov(o, u, i);
                eq_assign(o, u, j);
                begin_if(o, u);
                set(o, t, 0);
                end_if(o);
                mov(o, u, i);
                mul_const(o, u, N);
                add_assign(o, u, j);
                store_index(o, d, u, t);
            });
        });
        for_const(o, k, 0, N, R9, |o| {
            for_const(o, i, 0, N, R0, |o| {
                mov(o, t, i);
                mul_const(o, t, N);
                add_assign(o, t, k);
                load_index(o, a, d, t);
                for_const(o, j, 0, N, R0, |o| {
                    mov(o, t, k);
                    mul_const(o, t, N);
                    add_assign(o, t, j);
                    load_index(o, b, d, t);
                    add_assign(o, b, a);
                    mov(o, u, i);
                    mul_const(o, u, N);
                    add_assign(o, u, j);
                    load_index(o, t, d, u);
                    lt_assign(o, b, t);
                    begin_if(o, b);
                    mov(o, t, k);
                    mul_const(o, t, N);
                    add_assign(o, t, j);
                    load_index(o, b, d, t);
                    add_assign(o, b, a);
                    store_index(o, d, u, b);
                    end_if(o);
                });
            });
        });
        set(o, a, 0);
        for_const(o, i, 0, N * N, R0, |o| {
            load_index(o, t, d, i);
            add_assign(o, a, t);
        });
        putint(o, a);
        puts(o, "\n");
    });
    let c = format!(
        r#"{C_HEAD}
#define N {N}
static int64_t d[N * N];
int main(void) {{
    for (int64_t i = 0; i < N; i++)
        for (int64_t j = 0; j < N; j++) d[i * N + j] = i == j ? 0 : (i * 31 + j * 17) % 97 + 1;
    for (int64_t k = 0; k < N; k++)
        for (int64_t i = 0; i < N; i++) {{
            int64_t a = d[i * N + k];
            for (int64_t j = 0; j < N; j++)
                if (d[k * N + j] + a < d[i * N + j]) d[i * N + j] = d[k * N + j] + a;
        }}
    int64_t sum = 0;
    for (int64_t i = 0; i < N * N; i++) sum += d[i];
    printf("%lld\n", (long long)sum);
}}
"#
    );
    check("floyd", &ops, &c);
}
