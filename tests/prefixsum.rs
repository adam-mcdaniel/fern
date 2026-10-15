//! Running sums (each element plus the one before, kept to 20 bits) over
//! 80000 elements, 60 times: every step depends on the last.

mod common;

use bf::asm::*;
use common::*;

const N: i64 = 80_000;
const ROUNDS: i64 = 60;

#[test]
fn prefixsum_prints_what_c_does() {
    let ops = program(|o| {
        let (x, i, t, u, k) = (R1, R2, R3, R4, R5);
        heap_alloc_const(o, x, N);
        for_const(o, i, 0, N, R0, |o| {
            mov(o, t, i);
            rem_const(o, t, 97);
            store_index(o, x, i, t);
        });
        for_const(o, R8, 0, ROUNDS, R0, |o| {
            for_const(o, i, 1, N, R0, |o| {
                mov(o, k, i);
                dec(o, k);
                load_index(o, u, x, k);
                load_index(o, t, x, i);
                add_assign(o, t, u);
                and_const(o, t, 0xF_FFFF);
                store_index(o, x, i, t);
            });
        });
        set(o, u, 0);
        for_const(o, i, 0, N, R0, |o| {
            load_index(o, t, x, i);
            add_assign(o, u, t);
        });
        putint(o, u);
        puts(o, "\n");
    });
    let c = format!(
        r#"{C_HEAD}
#define N {N}
static int64_t x[N];
int main(void) {{
    for (int64_t i = 0; i < N; i++) x[i] = i % 97;
    for (int r = 0; r < {ROUNDS}; r++)
        for (int64_t i = 1; i < N; i++) x[i] = (x[i] + x[i - 1]) & 0xFFFFF;
    int64_t sum = 0;
    for (int64_t i = 0; i < N; i++) sum += x[i];
    printf("%lld\n", (long long)sum);
}}
"#
    );
    check("prefixsum", &ops, &c);
}
