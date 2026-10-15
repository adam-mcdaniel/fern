//! Triangles in a random graph of 1024 nodes (each edge there with
//! probability 3/10), with rows of the adjacency matrix as bitsets: for each
//! edge, the common neighbours by and-ing rows and counting bits (by the
//! shift-and-multiply way).

mod common;

use bf::asm::*;
use common::*;

const V: i64 = 1024;
const WORDS: i64 = V / 32;

/// `x = popcount(x)` for `x` below 2^32 (uses `R0`).
fn popcount(o: &mut dyn Program, x: &Location) {
    mov(o, R0, x);
    rshu_const(o, R0, 1);
    and_const(o, R0, 0x5555_5555);
    sub_assign(o, x, R0);
    mov(o, R0, x);
    rshu_const(o, R0, 2);
    and_const(o, R0, 0x3333_3333);
    and_const(o, x, 0x3333_3333);
    add_assign(o, x, R0);
    mov(o, R0, x);
    rshu_const(o, R0, 4);
    add_assign(o, x, R0);
    and_const(o, x, 0x0f0f_0f0f);
    mul_const(o, x, 0x0101_0101);
    and_const(o, x, 0xffff_ffff);
    rshu_const(o, x, 24);
}

#[test]
fn triangles_prints_what_c_does() {
    let ops = program(|o| {
        let (adj, i, j, k, t, u, seed, count) = (R1, R2, R3, R4, R5, R6, R7, R8);
        heap_alloc_const(o, adj, V * WORDS);
        set(o, t, 0);
        for_const(o, i, 0, V * WORDS, R0, |o| store_index(o, adj, i, t));
        set(o, seed, 2718);
        // the edges, both ways
        for_const(o, i, 0, V, R9, |o| {
            mov(o, j, i);
            inc(o, j);
            while_loop(o, R0, |o| { mov(o, R0, j); lt_const(o, R0, V); }, |o| {
                lcg(o, seed);
                mov(o, t, seed);
                rshu_const(o, t, 8);
                rem_const(o, t, 10);
                lt_const(o, t, 3);
                begin_if(o, t);
                for (a, b) in [(i, j), (j, i)] {
                    // adj[a * WORDS + b / 32] |= 1 << (b % 32)
                    mov(o, k, a);
                    mul_const(o, k, WORDS);
                    mov(o, u, b);
                    rshu_const(o, u, 5);
                    add_assign(o, k, u);
                    mov(o, u, b);
                    and_const(o, u, 31);
                    set(o, t, 1);
                    lsh_assign(o, t, u);
                    load_index(o, u, adj, k);
                    or_assign(o, u, t);
                    store_index(o, adj, k, u);
                }
                end_if(o);
                inc(o, j);
            });
        });
        // for each edge i < j, the k > j next to both
        set(o, count, 0);
        for_const(o, i, 0, V, R9, |o| {
            mov(o, j, i);
            inc(o, j);
            while_loop(o, R0, |o| { mov(o, R0, j); lt_const(o, R0, V); }, |o| {
                mov(o, k, i);
                mul_const(o, k, WORDS);
                mov(o, u, j);
                rshu_const(o, u, 5);
                add_assign(o, k, u);
                load_index(o, t, adj, k);
                mov(o, u, j);
                and_const(o, u, 31);
                rshu_assign(o, t, u);
                and_const(o, t, 1);
                begin_if(o, t);
                for_const(o, k, 0, WORDS, R0, |o| {
                    mov(o, t, i);
                    mul_const(o, t, WORDS);
                    add_assign(o, t, k);
                    load_index(o, t, adj, t);
                    mov(o, u, j);
                    mul_const(o, u, WORDS);
                    add_assign(o, u, k);
                    load_index(o, u, adj, u);
                    and_assign(o, t, u);
                    popcount(o, t);
                    add_assign(o, count, t);
                });
                end_if(o);
                inc(o, j);
            });
        });
        // (each triangle counted once for each of its edges)
        putint(o, count);
        puts(o, " ");
        div_const(o, count, 3);
        putint(o, count);
        puts(o, "\n");
    });
    let c = format!(
        r#"{C_HEAD}{LCG_C}
#define V {V}
#define WORDS {WORDS}
static int64_t adj[V * WORDS];
static int64_t popcount(int64_t x) {{
    x -= (int64_t)((uint64_t)x >> 1) & 0x55555555;
    x = ((int64_t)((uint64_t)x >> 2) & 0x33333333) + (x & 0x33333333);
    x = (x + (int64_t)((uint64_t)x >> 4)) & 0x0f0f0f0f;
    return (int64_t)((uint64_t)((x * 0x01010101) & 0xffffffff) >> 24);
}}
int main(void) {{
    int64_t seed = 2718;
    for (int64_t i = 0; i < V; i++)
        for (int64_t j = i + 1; j < V; j++) {{
            LCG(seed);
            if ((seed >> 8) % 10 < 3) {{
                adj[i * WORDS + j / 32] |= (int64_t)1 << (j % 32);
                adj[j * WORDS + i / 32] |= (int64_t)1 << (i % 32);
            }}
        }}
    int64_t count = 0;
    for (int64_t i = 0; i < V; i++)
        for (int64_t j = i + 1; j < V; j++)
            if ((adj[i * WORDS + j / 32] >> (j % 32)) & 1)
                for (int64_t k = 0; k < WORDS; k++) count += popcount(adj[i * WORDS + k] & adj[j * WORDS + k]);
    printf("%lld %lld\n", (long long)count, (long long)(count / 3));
}}
"#
    );
    check("triangles", &ops, &c);
}
