//! The autocorrelation of a noisy square wave of 20000 samples at lags 0 to
//! 399 (a sum of a different length for each); prints the strongest lag.

mod common;

use bf::asm::*;
use common::*;

const N: i64 = 20_000;
const LAGS: i64 = 400;

#[test]
fn autocorr_prints_what_c_does() {
    let ops = program(|o| {
        let (x, r, i, lag, s, t, u, seed) = (R1, R2, R3, R4, R5, R6, R7, R8);
        heap_alloc_const(o, x, N);
        heap_alloc_const(o, r, LAGS);
        set(o, seed, 31337);
        for_const(o, i, 0, N, R0, |o| {
            lcg(o, seed);
            mov(o, t, seed);
            rshu_const(o, t, 12);
            and_const(o, t, 1023);
            sub_const(o, t, 512);
            mov(o, u, i);
            rem_const(o, u, 50);
            lt_const(o, u, 25);
            mul_const(o, u, 600);
            sub_const(o, u, 300);
            add_assign(o, t, u);
            store_index(o, x, i, t);
        });
        for_const(o, lag, 0, LAGS, R0, |o| {
            set(o, s, 0);
            set(o, i, 0);
            while_loop(o, R9, |o| { mov(o, R9, i); add_assign(o, R9, lag); lt_const(o, R9, N); }, |o| {
                load_index(o, t, x, i);
                mov(o, u, i);
                add_assign(o, u, lag);
                load_index(o, u, x, u);
                mul_assign(o, t, u);
                add_assign(o, s, t);
                inc(o, i);
            });
            store_index(o, r, lag, s);
        });
        // the strongest lag past 10
        set(o, s, 0);
        set(o, u, 0);
        for_const(o, lag, 10, LAGS, R0, |o| {
            load_index(o, t, r, lag);
            mov(o, R9, t);
            gt_assign(o, R9, s);
            begin_if(o, R9);
            mov(o, s, t);
            mov(o, u, lag);
            end_if(o);
        });
        set(o, t, 0);
        load_index(o, t, r, t);
        putint(o, t);
        puts(o, " ");
        putint(o, u);
        puts(o, " ");
        putint(o, s);
        puts(o, "\n");
    });
    let c = format!(
        r#"{C_HEAD}{LCG_C}
#define N {N}
static int64_t x[N], r[{LAGS}];
int main(void) {{
    int64_t seed = 31337;
    for (int64_t i = 0; i < N; i++) {{
        LCG(seed);
        x[i] = ((seed >> 12) & 1023) - 512 + (i % 50 < 25) * 600 - 300;
    }}
    for (int64_t lag = 0; lag < {LAGS}; lag++) {{
        int64_t s = 0;
        for (int64_t i = 0; i + lag < N; i++) s += x[i] * x[i + lag];
        r[lag] = s;
    }}
    int64_t best = 0, at = 0;
    for (int64_t lag = 10; lag < {LAGS}; lag++)
        if (r[lag] > best) {{ best = r[lag]; at = lag; }}
    printf("%lld %lld %lld\n", (long long)r[0], (long long)at, (long long)best);
}}
"#
    );
    check("autocorr", &ops, &c);
}
