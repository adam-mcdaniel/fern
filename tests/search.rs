//! How many times a pattern of 8 letters is in 60000 random letters (from
//! 4), comparing at each place until a letter differs.

mod common;

use bf::asm::*;
use common::*;

const N: i64 = 60_000;
const M: i64 = 8;
const PATTERN: [i64; M as usize] = [1, 0, 2, 1, 3, 0, 1, 2];

#[test]
fn search_prints_what_c_does() {
    let ops = program(|o| {
        let (text, pat, i, k, t, u, count, seed) = (R1, R2, R3, R4, R5, R6, R7, R8);
        heap_alloc_const(o, text, N);
        heap_alloc_const(o, pat, M);
        for (j, p) in PATTERN.iter().enumerate() {
            set(o, k, j as u64);
            set(o, t, *p as u64);
            store_index(o, pat, k, t);
        }
        set(o, seed, 11);
        for_const(o, i, 0, N, R0, |o| {
            lcg(o, seed);
            mov(o, t, seed);
            rshu_const(o, t, 13);
            and_const(o, t, 3);
            store_index(o, text, i, t);
        });
        set(o, count, 0);
        for_const(o, i, 0, N - M + 1, R0, |o| {
            set(o, k, 0);
            begin_loop(o);
            mov(o, t, k);
            eq_const(o, t, M);
            begin_if(o, t);
            inc(o, count);
            break_loop(o);
            end_if(o);
            mov(o, t, i);
            add_assign(o, t, k);
            load_index(o, t, text, t);
            load_index(o, u, pat, k);
            ne_assign(o, t, u);
            break_if(o, t);
            inc(o, k);
            end_loop(o);
        });
        putint(o, count);
        puts(o, "\n");
    });
    let pattern: Vec<String> = PATTERN.iter().map(|p| p.to_string()).collect();
    let c = format!(
        r#"{C_HEAD}{LCG_C}
#define N {N}
#define M {M}
static int64_t text[N];
static const int64_t pat[M] = {{{}}};
int main(void) {{
    int64_t seed = 11, count = 0;
    for (int64_t i = 0; i < N; i++) {{ LCG(seed); text[i] = (seed >> 13) & 3; }}
    for (int64_t i = 0; i < N - M + 1; i++) {{
        int64_t k = 0;
        for (;;) {{
            if (k == M) {{ count++; break; }}
            if (text[i + k] != pat[k]) break;
            k++;
        }}
    }}
    printf("%lld\n", (long long)count);
}}
"#,
        pattern.join(", ")
    );
    check("search", &ops, &c);
}
