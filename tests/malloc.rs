//! 20000 random steps on 256 slots: an empty slot gets a new block (of 1 to
//! 32 cells, or sometimes 101 to 132) filled with numbers; a full one has
//! its block summed and freed. Then the rest are summed. If any two blocks
//! that were in use at once overlapped, the sums would be off.

mod common;

use bf::asm::*;
use common::*;

const SLOTS: i64 = 256;
const STEPS: i64 = 20_000;

/// `g(2) += p[j] * (j + 1)` for each of the `n` cells of block `p`, then
/// frees it.
fn sum_and_free(o: &mut dyn Program, p: &Location, n: &Location) {
    for_range(o, R6, 0, n, R7, |o| {
        load_index(o, R8, p, R6);
        inc(o, R6);
        mul_assign(o, R8, R6);
        dec(o, R6);
        add_assign(o, &g(2), R8);
    });
    free(o, p);
}

#[test]
fn malloc_prints_what_c_does() {
    let ops = program(|o| {
        // g(0): the blocks, g(1): their sizes, g(2): the sum, g(3): how many
        // were freed
        let (i, seed, slot, size, p, t) = (R1, R2, R3, R4, R5, R8);
        heap_alloc_const(o, R9, 4);
        heap_alloc_const(o, &g(0), SLOTS);
        heap_alloc_const(o, &g(1), SLOTS);
        set(o, t, 0);
        for_const(o, i, 0, SLOTS, R0, |o| put(o, 0, i, t));
        set(o, &g(2), 0);
        set(o, &g(3), 0);
        set(o, seed, 7);
        for_const(o, i, 0, STEPS, R0, |o| {
            lcg(o, seed);
            mov(o, slot, seed);
            rshu_const(o, slot, 8);
            and_const(o, slot, SLOTS - 1);
            get(o, p, 0, slot);
            begin_if(o, p);
            get(o, size, 1, slot);
            sum_and_free(o, p, size);
            set(o, t, 0);
            put(o, 0, slot, t);
            inc(o, &g(3));
            begin_else(o);
            mov(o, size, seed);
            rshu_const(o, size, 16);
            and_const(o, size, 31);
            inc(o, size);
            mov(o, t, seed);
            rshu_const(o, t, 21);
            and_const(o, t, 7);
            lnot_assign(o, t);
            begin_if(o, t);
            add_const(o, size, 100);
            end_if(o);
            malloc(o, p, size);
            put(o, 0, slot, p);
            put(o, 1, slot, size);
            for_range(o, R6, 0, size, R7, |o| {
                mov(o, t, seed);
                add_assign(o, t, R6);
                store_index(o, p, R6, t);
            });
            end_if(o);
        });
        for_const(o, i, 0, SLOTS, R0, |o| {
            get(o, p, 0, i);
            begin_if(o, p);
            get(o, size, 1, i);
            sum_and_free(o, p, size);
            end_if(o);
        });
        putint(o, &g(2));
        puts(o, " ");
        putint(o, &g(3));
        puts(o, "\n");
    });
    let c = format!(
        r#"{C_HEAD}#include <stdlib.h>
{LCG_C}
#define SLOTS {SLOTS}
static int64_t *blocks[SLOTS], sizes[SLOTS];
static int64_t sum = 0, freed = 0;
static void sum_and_free(int64_t *p, int64_t n) {{
    for (int64_t j = 0; j < n; j++) sum += p[j] * (j + 1);
    free(p);
}}
int main(void) {{
    int64_t seed = 7;
    for (int64_t i = 0; i < {STEPS}; i++) {{
        LCG(seed);
        int64_t slot = (seed >> 8) & (SLOTS - 1);
        if (blocks[slot]) {{
            sum_and_free(blocks[slot], sizes[slot]);
            blocks[slot] = 0;
            freed++;
        }} else {{
            int64_t size = ((seed >> 16) & 31) + 1;
            if (((seed >> 21) & 7) == 0) size += 100;
            int64_t *p = malloc(size * sizeof *p);
            blocks[slot] = p;
            sizes[slot] = size;
            for (int64_t j = 0; j < size; j++) p[j] = seed + j;
        }}
    }}
    for (int64_t i = 0; i < SLOTS; i++)
        if (blocks[i]) sum_and_free(blocks[i], sizes[i]);
    printf("%lld %lld\n", (long long)sum, (long long)freed);
}}
"#
    );
    check("malloc", &ops, &c);
}
