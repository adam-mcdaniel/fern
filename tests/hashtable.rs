//! 40000 random keys put in an open-addressing hash table of 65536 slots
//! (probing on), counting the probes; then a checksum of the table.

mod common;

use bf::asm::*;
use common::*;

const N: i64 = 40_000;
const SLOTS: i64 = 65_536;

#[test]
fn hashtable_prints_what_c_does() {
    let ops = program(|o| {
        let (table, i, key, slot, t, probes, seed) = (R1, R2, R3, R4, R5, R6, R7);
        heap_alloc_const(o, table, SLOTS);
        set(o, t, 0);
        for_const(o, i, 0, SLOTS, R0, |o| store_index(o, table, i, t));
        set(o, seed, 3);
        set(o, probes, 0);
        for_const(o, i, 0, N, R0, |o| {
            lcg(o, seed);
            mov(o, key, seed);
            inc(o, key);
            mov(o, slot, key);
            mul_const(o, slot, 2_654_435_761);
            rshu_const(o, slot, 16);
            and_const(o, slot, SLOTS - 1);
            // on while the slot holds another key
            begin_loop(o);
            load_index(o, t, table, slot);
            mov(o, R8, t);
            lnot_assign(o, R8);
            break_if(o, R8);
            eq_assign(o, t, key);
            break_if(o, t);
            inc(o, probes);
            inc(o, slot);
            and_const(o, slot, SLOTS - 1);
            end_loop(o);
            store_index(o, table, slot, key);
        });
        set(o, key, 0);
        for_const(o, i, 0, SLOTS, R0, |o| {
            load_index(o, t, table, i);
            mov(o, R8, i);
            and_const(o, R8, 7);
            inc(o, R8);
            mul_assign(o, t, R8);
            add_assign(o, key, t);
        });
        putint(o, probes);
        puts(o, " ");
        putint(o, key);
        puts(o, "\n");
    });
    let c = format!(
        r#"{C_HEAD}{LCG_C}
#define SLOTS {SLOTS}
static int64_t table[SLOTS];
int main(void) {{
    int64_t seed = 3, probes = 0;
    for (int64_t i = 0; i < {N}; i++) {{
        LCG(seed);
        int64_t key = seed + 1, slot = (int64_t)((uint64_t)(key * 2654435761ll) >> 16) & (SLOTS - 1);
        for (;;) {{
            int64_t t = table[slot];
            if (!t) break;
            if (t == key) break;
            probes++;
            slot = (slot + 1) & (SLOTS - 1);
        }}
        table[slot] = key;
    }}
    int64_t sum = 0;
    for (int64_t i = 0; i < SLOTS; i++) sum += table[i] * ((i & 7) + 1);
    printf("%lld %lld\n", (long long)probes, (long long)sum);
}}
"#
    );
    check("hashtable", &ops, &c);
}
