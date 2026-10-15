//! LSD radix sort of 30000 random 31-bit keys, a byte at a time (count,
//! prefix sums, scatter), 30 times over new keys; prints a checksum and
//! whether each came out sorted.

mod common;

use bf::asm::*;
use common::*;

const N: i64 = 30_000;
const ROUNDS: i64 = 30;
// the globals
const A: i64 = 0;
const B: i64 = 1;
const COUNT: i64 = 2;
const ROUND: i64 = 3;
const PASS: i64 = 4;
const SORTED: i64 = 5;
const SUM: i64 = 6;
const FLAG: i64 = 7;

#[test]
fn radixsort_prints_what_c_does() {
    let ops = program(|o| {
        let (i, t, d, sh, u, seed, a, b) = (R1, R2, R3, R4, R5, R6, R7, R8);
        heap_alloc_const(o, R9, 8);
        for (array, n) in [(A, N), (B, N), (COUNT, 256)] {
            heap_alloc_const(o, t, n);
            mov(o, &g(array), t);
        }
        set(o, seed, 5);
        set(o, &g(SORTED), 0);
        set(o, &g(SUM), 0);
        for_const(o, &g(ROUND), 0, ROUNDS, &g(FLAG), |o| {
            for_const(o, i, 0, N, R0, |o| {
                lcg(o, seed);
                put(o, A, i, seed);
            });
            set(o, sh, 0);
            for_const(o, &g(PASS), 0, 4, R0, |o| {
                set(o, t, 0);
                for_const(o, i, 0, 256, R0, |o| put(o, COUNT, i, t));
                mov(o, a, &g(A));
                for_const(o, i, 0, N, R0, |o| {
                    load_index(o, d, a, i);
                    rsh_assign(o, d, sh);
                    and_const(o, d, 255);
                    get(o, t, COUNT, d);
                    inc(o, t);
                    put(o, COUNT, d, t);
                });
                set(o, u, 0);
                for_const(o, i, 0, 256, R0, |o| {
                    get(o, t, COUNT, i);
                    put(o, COUNT, i, u);
                    add_assign(o, u, t);
                });
                mov(o, b, &g(B));
                for_const(o, i, 0, N, R0, |o| {
                    load_index(o, u, a, i);
                    mov(o, d, u);
                    rsh_assign(o, d, sh);
                    and_const(o, d, 255);
                    get(o, t, COUNT, d);
                    store_index(o, b, t, u);
                    inc(o, t);
                    put(o, COUNT, d, t);
                });
                mov(o, &g(A), b);
                mov(o, &g(B), a);
                add_const(o, sh, 8);
            });
            mov(o, a, &g(A));
            set(o, u, 1);
            for_const(o, i, 1, N, R0, |o| {
                load_index(o, t, a, i);
                mov(o, d, i);
                dec(o, d);
                load_index(o, d, a, d);
                le_assign(o, d, t);
                land_assign(o, u, d);
            });
            add_assign(o, &g(SORTED), u);
            for_const(o, i, 0, N, R0, |o| {
                load_index(o, t, a, i);
                mov(o, d, i);
                rem_const(o, d, 7);
                inc(o, d);
                mul_assign(o, t, d);
                add_assign(o, &g(SUM), t);
            });
        });
        putint(o, &g(SORTED));
        puts(o, " ");
        putint(o, &g(SUM));
        puts(o, "\n");
    });
    let c = format!(
        r#"{C_HEAD}{LCG_C}
#define N {N}
static int64_t a0[N], b0[N], count[256];
int main(void) {{
    int64_t seed = 5, sorted = 0, sum = 0;
    for (int round = 0; round < {ROUNDS}; round++) {{
        int64_t *a = a0, *b = b0;
        for (int64_t i = 0; i < N; i++) {{ LCG(seed); a[i] = seed; }}
        for (int sh = 0; sh < 32; sh += 8) {{
            memset(count, 0, sizeof count);
            for (int64_t i = 0; i < N; i++) count[(a[i] >> sh) & 255]++;
            int64_t u = 0;
            for (int i = 0; i < 256; i++) {{ int64_t t = count[i]; count[i] = u; u += t; }}
            for (int64_t i = 0; i < N; i++) b[count[(a[i] >> sh) & 255]++] = a[i];
            int64_t *t = a; a = b; b = t;
        }}
        int64_t ok = 1;
        for (int64_t i = 1; i < N; i++) ok &= a[i - 1] <= a[i];
        sorted += ok;
        for (int64_t i = 0; i < N; i++) sum += a[i] * (i % 7 + 1);
    }}
    printf("%lld %lld\n", (long long)sorted, (long long)sum);
}}
"#
    );
    check("radixsort", &ops, &c);
}
