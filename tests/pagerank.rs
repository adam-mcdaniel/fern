//! PageRank on a random graph of 5000 pages with 8 links into each, 200
//! rounds in Q30: what each page passes on, then each page gathering from
//! the pages that link to it.

mod common;

use bf::asm::*;
use common::*;

const N: i64 = 5000;
const IN: i64 = 8;
const ROUNDS: i64 = 200;
const ONE: i64 = 1 << 30;
// the globals
const SRC: i64 = 0;
const OUT: i64 = 1;
const RANK: i64 = 2;
const PASS: i64 = 3;
const ROUND: i64 = 4;
const RF: i64 = 5;

#[test]
fn pagerank_prints_what_c_does() {
    let ops = program(|o| {
        let (v, e, u, t, s, seed, src, pass) = (R1, R2, R3, R4, R5, R6, R7, R8);
        heap_alloc_const(o, R9, 6);
        for (array, n) in [(SRC, N * IN), (OUT, N), (RANK, N), (PASS, N)] {
            heap_alloc_const(o, t, n);
            mov(o, &g(array), t);
        }
        set(o, t, 0);
        for_const(o, v, 0, N, R0, |o| put(o, OUT, v, t));
        set(o, seed, 8);
        mov(o, src, &g(SRC));
        for_const(o, e, 0, N * IN, R0, |o| {
            lcg(o, seed);
            mov(o, u, seed);
            rshu_const(o, u, 8);
            rem_const(o, u, N);
            store_index(o, src, e, u);
            get(o, t, OUT, u);
            inc(o, t);
            put(o, OUT, u, t);
        });
        set_int(o, t, ONE / N);
        for_const(o, v, 0, N, R0, |o| put(o, RANK, v, t));
        for_const(o, &g(ROUND), 0, ROUNDS, &g(RF), |o| {
            mov(o, pass, &g(PASS));
            for_const(o, u, 0, N, R0, |o| {
                get(o, t, OUT, u);
                begin_if(o, t);
                get(o, s, RANK, u);
                mul_const(o, s, 85);
                div_const(o, s, 100);
                get(o, t, OUT, u);
                div_assign(o, s, t);
                begin_else(o);
                set(o, s, 0);
                end_if(o);
                store_index(o, pass, u, s);
            });
            for_const(o, v, 0, N, R0, |o| {
                set_int(o, s, ONE * 15 / 100 / N);
                mov(o, e, v);
                mul_const(o, e, IN);
                for _ in 0..IN {
                    load_index(o, u, src, e);
                    load_index(o, t, pass, u);
                    add_assign(o, s, t);
                    inc(o, e);
                }
                put(o, RANK, v, s);
            });
        });
        set(o, s, 0);
        set(o, e, 0);
        set(o, u, 0);
        for_const(o, v, 0, N, R0, |o| {
            get(o, t, RANK, v);
            add_assign(o, s, t);
            mov(o, R0, t);
            gt_assign(o, R0, e);
            begin_if(o, R0);
            mov(o, e, t);
            mov(o, u, v);
            end_if(o);
        });
        putint(o, s);
        puts(o, " ");
        putint(o, u);
        puts(o, " ");
        putint(o, e);
        puts(o, "\n");
    });
    let c = format!(
        r#"{C_HEAD}{LCG_C}
#define N {N}
#define IN {IN}
static int64_t src[N * IN], out[N], rank[N], pass[N];
int main(void) {{
    int64_t seed = 8;
    for (int64_t e = 0; e < N * IN; e++) {{ LCG(seed); src[e] = (seed >> 8) % N; out[src[e]]++; }}
    for (int64_t v = 0; v < N; v++) rank[v] = {ONE} / N;
    for (int round = 0; round < {ROUNDS}; round++) {{
        for (int64_t u = 0; u < N; u++) pass[u] = out[u] ? rank[u] * 85 / 100 / out[u] : 0;
        for (int64_t v = 0; v < N; v++) {{
            int64_t s = (int64_t){ONE} * 15 / 100 / N;
            for (int e = 0; e < IN; e++) s += pass[src[v * IN + e]];
            rank[v] = s;
        }}
    }}
    int64_t sum = 0, best = 0, at = 0;
    for (int64_t v = 0; v < N; v++) {{
        sum += rank[v];
        if (rank[v] > best) {{ best = rank[v]; at = v; }}
    }}
    printf("%lld %lld %lld\n", (long long)sum, (long long)at, (long long)best);
}}
"#
    );
    check("pagerank", &ops, &c);
}
