//! The edit distance between two random strings of 4000 letters (from a, b,
//! c and d), by dynamic programming a row at a time.

mod common;

use bf::asm::*;
use common::*;

const L: i64 = 4000;

#[test]
fn levenshtein_prints_what_c_does() {
    let ops = program(|o| {
        let (a, b, prev, cur, i, j, t, u) = (R1, R2, R3, R4, R5, R6, R7, R8);
        heap_alloc_const(o, a, L);
        heap_alloc_const(o, b, L);
        heap_alloc_const(o, prev, L + 1);
        heap_alloc_const(o, cur, L + 1);
        set(o, R9, 5);
        for s in [a, b] {
            for_const(o, i, 0, L, R0, |o| {
                lcg(o, R9);
                mov(o, t, R9);
                rshu_const(o, t, 16);
                and_const(o, t, 3);
                store_index(o, s, i, t);
            });
        }
        for_const(o, j, 0, L + 1, R0, |o| store_index(o, prev, j, j));
        for_const(o, i, 1, L + 1, R9, |o| {
            set(o, t, 0);
            store_index(o, cur, t, i);
            for_const(o, j, 1, L + 1, R0, |o| {
                // the substitution's cost
                mov(o, t, i);
                dec(o, t);
                load_index(o, t, a, t);
                mov(o, u, j);
                dec(o, u);
                load_index(o, u, b, u);
                ne_assign(o, t, u);
                mov(o, u, j);
                dec(o, u);
                load_index(o, u, prev, u);
                add_assign(o, t, u);
                // or deleting or inserting
                load_index(o, u, prev, j);
                inc(o, u);
                min_assign(o, t, u);
                mov(o, u, j);
                dec(o, u);
                load_index(o, u, cur, u);
                inc(o, u);
                min_assign(o, t, u);
                store_index(o, cur, j, t);
            });
            mov(o, t, prev);
            mov(o, prev, cur);
            mov(o, cur, t);
        });
        set(o, t, L as u64);
        load_index(o, t, prev, t);
        putint(o, t);
        puts(o, "\n");
    });
    let c = format!(
        r#"{C_HEAD}{LCG_C}
#define L {L}
static int64_t a[L], b[L], r0[L + 1], r1[L + 1];
int main(void) {{
    int64_t seed = 5, *prev = r0, *cur = r1;
    for (int64_t i = 0; i < L; i++) {{ LCG(seed); a[i] = (seed >> 16) & 3; }}
    for (int64_t i = 0; i < L; i++) {{ LCG(seed); b[i] = (seed >> 16) & 3; }}
    for (int64_t j = 0; j <= L; j++) prev[j] = j;
    for (int64_t i = 1; i <= L; i++) {{
        cur[0] = i;
        for (int64_t j = 1; j <= L; j++) {{
            int64_t t = (a[i - 1] != b[j - 1]) + prev[j - 1];
            if (prev[j] + 1 < t) t = prev[j] + 1;
            if (cur[j - 1] + 1 < t) t = cur[j - 1] + 1;
            cur[j] = t;
        }}
        int64_t *t = prev; prev = cur; cur = t;
    }}
    printf("%lld\n", (long long)prev[L]);
}}
"#
    );
    check("levenshtein", &ops, &c);
}
