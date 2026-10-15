//! Dijkstra's shortest paths on a complete graph of 1500 nodes with hashed
//! edge weights, the array way: each step the nearest unfinished node (an
//! argmin), then relaxing every edge from it; prints a sum of the distances.

mod common;

use bf::asm::*;
use common::*;

const V: i64 = 1500;

/// `dst = weight(a, b)`: a hash of the pair, from 1 to 1000 (uses `R0`).
fn weight(o: &mut dyn Program, dst: &Location, a: &Location, b: &Location) {
    mov(o, dst, a);
    mul_const(o, dst, 1_000_003);
    add_assign(o, dst, b);
    mul_const(o, dst, 2_654_435_761);
    mov(o, R0, dst);
    rshu_const(o, R0, 17);
    xor_assign(o, dst, R0);
    and_const(o, dst, 0xffff);
    rem_const(o, dst, 1000);
    inc(o, dst);
}

#[test]
fn dijkstra_prints_what_c_does() {
    let ops = program(|o| {
        let (dist, done, step, v, best, at, d, t) = (R1, R2, R3, R4, R5, R6, R7, R8);
        heap_alloc_const(o, dist, V);
        heap_alloc_const(o, done, V);
        for_const(o, v, 0, V, R0, |o| {
            set_int(o, t, i64::MAX / 2);
            store_index(o, dist, v, t);
            set(o, t, 0);
            store_index(o, done, v, t);
        });
        set(o, t, 0);
        store_index(o, dist, t, t);
        for_const(o, step, 0, V, R9, |o| {
            set_int(o, best, i64::MAX);
            set(o, at, 0);
            for_const(o, v, 0, V, R0, |o| {
                load_index(o, t, done, v);
                lnot_assign(o, t);
                load_index(o, d, dist, v);
                mov(o, R0, d);
                lt_assign(o, R0, best);
                land_assign(o, t, R0);
                begin_if(o, t);
                mov(o, best, d);
                mov(o, at, v);
                end_if(o);
            });
            set(o, t, 1);
            store_index(o, done, at, t);
            for_const(o, v, 0, V, R0, |o| {
                weight(o, d, at, v);
                add_assign(o, d, best);
                load_index(o, t, dist, v);
                gt_assign(o, t, d);
                begin_if(o, t);
                store_index(o, dist, v, d);
                end_if(o);
            });
        });
        set(o, best, 0);
        for_const(o, v, 0, V, R0, |o| {
            load_index(o, t, dist, v);
            mov(o, d, v);
            rem_const(o, d, 11);
            inc(o, d);
            mul_assign(o, t, d);
            add_assign(o, best, t);
        });
        putint(o, best);
        puts(o, "\n");
    });
    let c = format!(
        r#"{C_HEAD}
#define V {V}
static int64_t dist[V], done[V];
static int64_t weight(int64_t a, int64_t b) {{
    int64_t h = (a * 1000003 + b) * 2654435761LL;
    h ^= (int64_t)((uint64_t)h >> 17);
    return (h & 0xffff) % 1000 + 1;
}}
int main(void) {{
    for (int64_t v = 0; v < V; v++) {{ dist[v] = INT64_MAX / 2; done[v] = 0; }}
    dist[0] = 0;
    for (int64_t step = 0; step < V; step++) {{
        int64_t best = INT64_MAX, at = 0;
        for (int64_t v = 0; v < V; v++)
            if (!done[v] && dist[v] < best) {{ best = dist[v]; at = v; }}
        done[at] = 1;
        for (int64_t v = 0; v < V; v++) {{
            int64_t d = weight(at, v) + best;
            if (dist[v] > d) dist[v] = d;
        }}
    }}
    int64_t s = 0;
    for (int64_t v = 0; v < V; v++) s += dist[v] * (v % 11 + 1);
    printf("%lld\n", (long long)s);
}}
"#
    );
    check("dijkstra", &ops, &c);
}
