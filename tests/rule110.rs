//! Rule 110, the 1D cellular automaton, on 40000 cells (dead edges) for
//! 300 generations from a random start; prints how many are alive and a
//! checksum.

mod common;

use bf::asm::*;
use common::*;

const N: i64 = 40_000;
const GENS: i64 = 300;

#[test]
fn rule110_prints_what_c_does() {
    let ops = program(|o| {
        let (cur, next, i, t, u, k) = (R1, R2, R3, R4, R5, R6);
        heap_alloc_const(o, cur, N);
        heap_alloc_const(o, next, N);
        set(o, R8, 9);
        for_const(o, i, 0, N, R0, |o| {
            lcg(o, R8);
            mov(o, t, R8);
            rshu_const(o, t, 17);
            and_const(o, t, 1);
            store_index(o, cur, i, t);
            set(o, t, 0);
            store_index(o, next, i, t);
        });
        for_const(o, R9, 0, GENS, R0, |o| {
            for_const(o, i, 1, N - 1, R0, |o| {
                // the neighbourhood as 3 bits, then rule 110's bit for it
                mov(o, k, i);
                dec(o, k);
                load_index(o, t, cur, k);
                add_assign(o, t, t);
                load_index(o, u, cur, i);
                add_assign(o, t, u);
                add_assign(o, t, t);
                add_const(o, k, 2);
                load_index(o, u, cur, k);
                add_assign(o, t, u);
                set(o, u, 110);
                rshu_assign(o, u, t);
                and_const(o, u, 1);
                store_index(o, next, i, u);
            });
            mov(o, t, cur);
            mov(o, cur, next);
            mov(o, next, t);
        });
        set(o, t, 0);
        set(o, u, 0);
        for_const(o, i, 0, N, R0, |o| {
            load_index(o, k, cur, i);
            add_assign(o, t, k);
            mul_assign(o, k, i);
            add_assign(o, u, k);
        });
        putint(o, t);
        puts(o, " ");
        putint(o, u);
        puts(o, "\n");
    });
    let c = format!(
        r#"{C_HEAD}{LCG_C}
#define N {N}
static int64_t a[N], b[N];
int main(void) {{
    int64_t *cur = a, *next = b, seed = 9;
    for (int64_t i = 0; i < N; i++) {{ LCG(seed); cur[i] = (seed >> 17) & 1; next[i] = 0; }}
    for (int g = 0; g < {GENS}; g++) {{
        for (int64_t i = 1; i < N - 1; i++) next[i] = (110 >> (cur[i - 1] * 4 + cur[i] * 2 + cur[i + 1])) & 1;
        int64_t *t = cur; cur = next; next = t;
    }}
    int64_t alive = 0, sum = 0;
    for (int64_t i = 0; i < N; i++) {{ alive += cur[i]; sum += cur[i] * i; }}
    printf("%lld %lld\n", (long long)alive, (long long)sum);
}}
"#
    );
    check("rule110", &ops, &c);
}
