//! A summed-area table of a 220x220 image, built in place (each row's
//! running sums, then each column's), then the sums of two million random
//! boxes from it, four reads each.

mod common;

use bf::asm::*;
use common::*;

const S: i64 = 220;
const QUERIES: i64 = 2_000_000;

#[test]
fn sat_prints_what_c_does() {
    let ops = program(|o| {
        let (a, i, j, at, t, u, seed, sum) = (R1, R2, R3, R4, R5, R6, R7, R8);
        heap_alloc_const(o, a, S * S);
        set(o, seed, 31);
        for_const(o, i, 0, S * S, R0, |o| {
            lcg(o, seed);
            mov(o, t, seed);
            rshu_const(o, t, 10);
            and_const(o, t, 255);
            store_index(o, a, i, t);
        });
        // rows
        for_const(o, i, 0, S, R9, |o| {
            for_const(o, j, 1, S, R0, |o| {
                mov(o, at, i);
                mul_const(o, at, S);
                add_assign(o, at, j);
                mov(o, t, at);
                dec(o, t);
                load_index(o, t, a, t);
                load_index(o, u, a, at);
                add_assign(o, u, t);
                store_index(o, a, at, u);
            });
        });
        // columns
        for_const(o, j, 0, S, R9, |o| {
            for_const(o, i, 1, S, R0, |o| {
                mov(o, at, i);
                mul_const(o, at, S);
                add_assign(o, at, j);
                mov(o, t, at);
                sub_const(o, t, S);
                load_index(o, t, a, t);
                load_index(o, u, a, at);
                add_assign(o, u, t);
                store_index(o, a, at, u);
            });
        });
        // boxes (x0, y0) to (x1, y1), both inclusive, x0 and y0 at least 1
        set(o, sum, 0);
        for_const(o, i, 0, QUERIES, R9, |o| {
            lcg(o, seed);
            mov(o, at, seed);
            rshu_const(o, at, 4);
            // x0, x1 from at's bits
            mov(o, j, at);
            and_const(o, j, 127);
            inc(o, j);
            mov(o, t, at);
            rshu_const(o, t, 7);
            and_const(o, t, 63);
            add_assign(o, t, j);
            // y0 = j's, y1 = t's: the box is rows j..t, columns j..t, and the
            // sum is A[t][t] - A[j-1][t] - A[t][j-1] + A[j-1][j-1]
            mov(o, u, t);
            mul_const(o, u, S);
            add_assign(o, u, t);
            load_index(o, u, a, u);
            add_assign(o, sum, u);
            mov(o, u, j);
            dec(o, u);
            mul_const(o, u, S);
            add_assign(o, u, t);
            load_index(o, u, a, u);
            sub_assign(o, sum, u);
            mov(o, u, t);
            mul_const(o, u, S);
            add_assign(o, u, j);
            dec(o, u);
            load_index(o, u, a, u);
            sub_assign(o, sum, u);
            mov(o, u, j);
            dec(o, u);
            mul_const(o, u, S + 1);
            load_index(o, u, a, u);
            add_assign(o, sum, u);
        });
        putint(o, sum);
        puts(o, "\n");
    });
    let c = format!(
        r#"{C_HEAD}{LCG_C}
#define S {S}
static int64_t a[S * S];
int main(void) {{
    int64_t seed = 31;
    for (int64_t i = 0; i < S * S; i++) {{ LCG(seed); a[i] = (seed >> 10) & 255; }}
    for (int64_t i = 0; i < S; i++)
        for (int64_t j = 1; j < S; j++) a[i * S + j] += a[i * S + j - 1];
    for (int64_t j = 0; j < S; j++)
        for (int64_t i = 1; i < S; i++) a[i * S + j] += a[(i - 1) * S + j];
    int64_t sum = 0;
    for (int64_t q = 0; q < {QUERIES}; q++) {{
        LCG(seed);
        int64_t r = seed >> 4;
        int64_t j = (r & 127) + 1, t = ((r >> 7) & 63) + j;
        sum += a[t * S + t] - a[(j - 1) * S + t] - a[t * S + j - 1] + a[(j - 1) * (S + 1)];
    }}
    printf("%lld\n", (long long)sum);
}}
"#
    );
    check("sat", &ops, &c);
}
