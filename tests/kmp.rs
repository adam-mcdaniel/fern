//! Knuth-Morris-Pratt: the failure table of a 12-letter pattern over two
//! letters, then counting where it occurs in five million random letters
//! made as they're read (a state machine, in order).

mod common;

use bf::asm::*;
use common::*;

const N: i64 = 5_000_000;
const PATTERN: [i64; 12] = [0, 1, 0, 0, 1, 0, 1, 0, 0, 1, 0, 0];

#[test]
fn kmp_prints_what_c_does() {
    let m = PATTERN.len() as i64;
    let ops = program(|o| {
        let (pat, fail, i, q, c, t, seed, count) = (R1, R2, R3, R4, R5, R6, R7, R8);
        heap_alloc_const(o, pat, m);
        heap_alloc_const(o, fail, m);
        for (k, &p) in PATTERN.iter().enumerate() {
            set(o, t, k as u64);
            set(o, c, p as u64);
            store_index(o, pat, t, c);
        }
        // the failure table
        set(o, t, 0);
        store_index(o, fail, t, t);
        set(o, q, 0);
        for_const(o, i, 1, m, R9, |o| {
            load_index(o, c, pat, i);
            while_loop(o, R0, |o| {
                mov(o, R0, q);
                gt_const(o, R0, 0);
                load_index(o, t, pat, q);
                ne_assign(o, t, c);
                land_assign(o, R0, t);
            }, |o| {
                dec(o, q);
                load_index(o, q, fail, q);
            });
            load_index(o, t, pat, q);
            eq_assign(o, t, c);
            add_assign(o, q, t);
            store_index(o, fail, i, q);
        });
        // the search
        set(o, seed, 1);
        set(o, q, 0);
        set(o, count, 0);
        for_const(o, i, 0, N, R9, |o| {
            lcg(o, seed);
            mov(o, c, seed);
            rshu_const(o, c, 16);
            and_const(o, c, 1);
            while_loop(o, R0, |o| {
                mov(o, R0, q);
                gt_const(o, R0, 0);
                load_index(o, t, pat, q);
                ne_assign(o, t, c);
                land_assign(o, R0, t);
            }, |o| {
                dec(o, q);
                load_index(o, q, fail, q);
            });
            load_index(o, t, pat, q);
            eq_assign(o, t, c);
            add_assign(o, q, t);
            mov(o, t, q);
            eq_const(o, t, m);
            begin_if(o, t);
            inc(o, count);
            dec(o, q);
            load_index(o, q, fail, q);
            end_if(o);
        });
        putint(o, count);
        puts(o, "\n");
    });
    let pattern = PATTERN.iter().map(|p| p.to_string()).collect::<Vec<_>>().join(", ");
    let c = format!(
        r#"{C_HEAD}{LCG_C}
#define M {m}
static const int64_t pat[M] = {{{pattern}}};
static int64_t fail[M];
int main(void) {{
    fail[0] = 0;
    for (int64_t i = 1, q = 0; i < M; i++) {{
        while (q > 0 && pat[q] != pat[i]) q = fail[q - 1];
        q += pat[q] == pat[i];
        fail[i] = q;
    }}
    int64_t seed = 1, q = 0, count = 0;
    for (int64_t i = 0; i < {N}; i++) {{
        LCG(seed);
        int64_t c = (seed >> 16) & 1;
        while (q > 0 && pat[q] != c) q = fail[q - 1];
        q += pat[q] == c;
        if (q == M) {{ count++; q = fail[q - 1]; }}
    }}
    printf("%lld\n", (long long)count);
}}
"#
    );
    check("kmp", &ops, &c);
}
