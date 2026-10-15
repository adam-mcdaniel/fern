//! Life: Conway's, on a grid with a border, from a random start; prints how
//! many cells are alive at the end.

mod common;

use bf::asm::*;
use bf::Op;
use common::*;

pub fn life(size: i64, generations: i64) -> Vec<Op> {
    let w = size + 2;
    let cells = w * w;
    program(|o| {
        let (cur, next, i, sum, t, alive) = (R1, R2, R3, R4, R5, R6);
        set(o, R7, cells as u64);
        heap_alloc(o, cur, R7);
        heap_alloc(o, next, R7);
        // random cells alive (not the first and last rows)
        set(o, i, 0);
        set(o, R8, 12345);
        while_loop(o, R0, |o| { mov(o, R0, i); lt_const(o, R0, cells); }, |o| {
            mul_const(o, R8, 1_103_515_245);
            add_const(o, R8, 12345);
            and_const(o, R8, 0x7fff_ffff);
            mov(o, t, R8);
            rshu_const(o, t, 16);
            rem_const(o, t, 3);
            eq_const(o, t, 0);
            mov(o, sum, i);
            lt_const(o, sum, w);
            mov(o, alive, i);
            ge_const(o, alive, cells - w);
            add_assign(o, sum, alive);
            begin_if(o, sum);
            set(o, t, 0);
            end_if(o);
            store_index(o, cur, i, t);
            set(o, t, 0);
            store_index(o, next, i, t);
            inc(o, i);
        });
        set(o, R8, 0);
        while_loop(o, R9, |o| { mov(o, R9, R8); lt_const(o, R9, generations); }, |o| {
            set(o, i, (w + 1) as u64);
            while_loop(o, R0, |o| { mov(o, R0, i); lt_const(o, R0, cells - w - 1); }, |o| {
                set(o, sum, 0);
                for d in [-w - 1, -w, -w + 1, -1, 1, w - 1, w, w + 1] {
                    mov(o, t, i);
                    add_const(o, t, d);
                    load_index(o, alive, cur, t);
                    add_assign(o, sum, alive);
                }
                load_index(o, alive, cur, i);
                mov(o, t, sum);
                eq_const(o, t, 3);
                eq_const(o, sum, 2);
                mul_assign(o, sum, alive);
                add_assign(o, t, sum);
                store_index(o, next, i, t);
                inc(o, i);
            });
            mov(o, t, cur);
            mov(o, cur, next);
            mov(o, next, t);
            inc(o, R8);
        });
        set(o, i, 0);
        set(o, sum, 0);
        while_loop(o, R0, |o| { mov(o, R0, i); lt_const(o, R0, cells); }, |o| {
            load_index(o, t, cur, i);
            add_assign(o, sum, t);
            inc(o, i);
        });
        putint(o, sum);
        puts(o, "\n");
    })
}

pub fn life_c(size: i64, generations: i64) -> String {
    let w = size + 2;
    format!(
        r#"#include <stdio.h>
#include <stdint.h>
#define W {w}
#define CELLS (W * W)
static int64_t a[CELLS], b[CELLS];
int main(void) {{
    int64_t *cur = a, *next = b, seed = 12345;
    for (int64_t i = 0; i < CELLS; i++) {{
        seed = (seed * 1103515245 + 12345) & 0x7fffffff;
        int64_t t = ((int64_t)((uint64_t)seed >> 16)) % 3 == 0;
        if ((i < W) + (i >= CELLS - W)) t = 0;
        cur[i] = t;
        next[i] = 0;
    }}
    for (int g = 0; g < {generations}; g++) {{
        for (int64_t i = W + 1; i < CELLS - W - 1; i++) {{
            int64_t s = cur[i - W - 1] + cur[i - W] + cur[i - W + 1] + cur[i - 1] + cur[i + 1] + cur[i + W - 1] + cur[i + W] + cur[i + W + 1];
            next[i] = (s == 3) + (s == 2) * cur[i];
        }}
        int64_t *t = cur; cur = next; next = t;
    }}
    int64_t sum = 0;
    for (int64_t i = 0; i < CELLS; i++) sum += cur[i];
    printf("%lld\n", (long long)sum);
    return 0;
}}
"#
    )
}

#[test]
fn life_prints_what_c_does() {
    check("life", &life(208, 600), &life_c(208, 600));
}
