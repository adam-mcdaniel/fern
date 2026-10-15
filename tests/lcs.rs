//! The longest common subsequence of two random 4000-letter strings over
//! four letters, by the table a row at a time (two rows); prints its length.

mod common;

use bf::asm::*;
use common::*;

const N: i64 = 4000;

#[test]
fn lcs_prints_what_c_does() {
    let ops = program(|o| {
        let (a, b, prev, cur, i, j, t, u) = (R1, R2, R3, R4, R5, R6, R7, R8);
        heap_alloc_const(o, a, N);
        heap_alloc_const(o, b, N);
        heap_alloc_const(o, prev, N + 1);
        heap_alloc_const(o, cur, N + 1);
        set(o, R9, 4321);
        for s in [a, b] {
            for_const(o, i, 0, N, R0, |o| {
                lcg(o, R9);
                mov(o, t, R9);
                rshu_const(o, t, 16);
                and_const(o, t, 3);
                store_index(o, s, i, t);
            });
        }
        set(o, t, 0);
        for_const(o, j, 0, N + 1, R0, |o| {
            store_index(o, prev, j, t);
            store_index(o, cur, j, t);
        });
        for_const(o, i, 0, N, R9, |o| {
            for_const(o, j, 0, N, R0, |o| {
                // cur[j + 1] = a[i] == b[j] ? prev[j] + 1 : max(prev[j + 1], cur[j])
                load_index(o, t, a, i);
                load_index(o, u, b, j);
                eq_assign(o, t, u);
                begin_if(o, t);
                load_index(o, t, prev, j);
                inc(o, t);
                begin_else(o);
                load_index(o, t, cur, j);
                mov(o, u, j);
                inc(o, u);
                load_index(o, u, prev, u);
                max_assign(o, t, u);
                end_if(o);
                mov(o, u, j);
                inc(o, u);
                store_index(o, cur, u, t);
            });
            mov(o, t, prev);
            mov(o, prev, cur);
            mov(o, cur, t);
        });
        set_int(o, t, N);
        load_index(o, t, prev, t);
        putint(o, t);
        puts(o, "\n");
    });
    let c = format!(
        r#"{C_HEAD}{LCG_C}
#define N {N}
static int64_t a[N], b[N], r0[N + 1], r1[N + 1];
int main(void) {{
    int64_t seed = 4321;
    for (int64_t i = 0; i < N; i++) {{ LCG(seed); a[i] = (seed >> 16) & 3; }}
    for (int64_t i = 0; i < N; i++) {{ LCG(seed); b[i] = (seed >> 16) & 3; }}
    int64_t *prev = r0, *cur = r1;
    for (int64_t i = 0; i < N; i++) {{
        for (int64_t j = 0; j < N; j++) {{
            if (a[i] == b[j]) cur[j + 1] = prev[j] + 1;
            else cur[j + 1] = prev[j + 1] > cur[j] ? prev[j + 1] : cur[j];
        }}
        int64_t *t = prev; prev = cur; cur = t;
    }}
    printf("%lld\n", (long long)prev[N]);
}}
"#
    );
    check("lcs", &ops, &c);
}
