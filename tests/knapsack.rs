//! 0/1 knapsack: 300 random items, capacity 30000, the usual table of one
//! row updated in place from the top down (each cell reads one below it
//! that the row hasn't reached yet).

mod common;

use bf::asm::*;
use common::*;

const ITEMS: i64 = 300;
const CAP: i64 = 30_000;

#[test]
fn knapsack_prints_what_c_does() {
    let ops = program(|o| {
        let (dp, item, w, v, c, t, u, seed) = (R1, R2, R3, R4, R5, R6, R7, R8);
        heap_alloc_const(o, dp, CAP + 1);
        set(o, t, 0);
        for_const(o, c, 0, CAP + 1, R0, |o| store_index(o, dp, c, t));
        set(o, seed, 4242);
        for_const(o, item, 0, ITEMS, R9, |o| {
            lcg(o, seed);
            mov(o, w, seed);
            rshu_const(o, w, 8);
            rem_const(o, w, 900);
            add_const(o, w, 100);
            lcg(o, seed);
            mov(o, v, seed);
            rshu_const(o, v, 8);
            rem_const(o, v, 1000);
            inc(o, v);
            set_int(o, c, CAP);
            while_loop(o, R0, |o| { mov(o, R0, c); ge_assign(o, R0, w); }, |o| {
                mov(o, t, c);
                sub_assign(o, t, w);
                load_index(o, t, dp, t);
                add_assign(o, t, v);
                load_index(o, u, dp, c);
                lt_assign(o, u, t);
                begin_if(o, u);
                store_index(o, dp, c, t);
                end_if(o);
                dec(o, c);
            });
        });
        set_int(o, c, CAP);
        load_index(o, t, dp, c);
        putint(o, t);
        puts(o, " ");
        set_int(o, c, CAP / 2);
        load_index(o, t, dp, c);
        putint(o, t);
        puts(o, "\n");
    });
    let c = format!(
        r#"{C_HEAD}{LCG_C}
#define CAP {CAP}
static int64_t dp[CAP + 1];
int main(void) {{
    int64_t seed = 4242;
    for (int item = 0; item < {ITEMS}; item++) {{
        LCG(seed); int64_t w = (seed >> 8) % 900 + 100;
        LCG(seed); int64_t v = (seed >> 8) % 1000 + 1;
        for (int64_t c = CAP; c >= w; c--)
            if (dp[c - w] + v > dp[c]) dp[c] = dp[c - w] + v;
    }}
    printf("%lld %lld\n", (long long)dp[CAP], (long long)dp[CAP / 2]);
}}
"#
    );
    check("knapsack", &ops, &c);
}
