//! k-means clustering: 20000 random points in the plane, 8 clusters, 100
//! rounds of assigning each point to its nearest centroid (in parallel) and
//! moving each centroid to the mean of its points; prints the centroids.

mod common;

use bf::asm::*;
use common::*;

const P: i64 = 20_000;
const K: i64 = 8;
const ROUNDS: i64 = 100;
// the globals: the arrays, and the round
const X: i64 = 0;
const Y: i64 = 1;
const ASSIGN: i64 = 2;
const CX: i64 = 3;
const CY: i64 = 4;
const SX: i64 = 5;
const SY: i64 = 6;
const CNT: i64 = 7;
const ROUND: i64 = 8;

#[test]
fn kmeans_prints_what_c_does() {
    let ops = program(|o| {
        let (p, k, best, bd, d, t, seed) = (R1, R2, R3, R4, R5, R6, R3);
        heap_alloc_const(o, R9, 9);
        for (array, n) in [(X, P), (Y, P), (ASSIGN, P), (CX, K), (CY, K), (SX, K), (SY, K), (CNT, K)] {
            heap_alloc_const(o, R7, n);
            mov(o, &g(array), R7);
        }
        set(o, seed, 2024);
        for_const(o, p, 0, P, R0, |o| {
            for array in [X, Y] {
                lcg(o, seed);
                mov(o, t, seed);
                rshu_const(o, t, 8);
                rem_const(o, t, 10_000);
                put(o, array, p, t);
            }
        });
        for_const(o, k, 0, K, R0, |o| {
            get(o, t, X, k);
            put(o, CX, k, t);
            get(o, t, Y, k);
            put(o, CY, k, t);
        });
        for_const(o, &g(ROUND), 0, ROUNDS, R8, |o| {
            // each point's nearest centroid
            for_const(o, p, 0, P, R0, |o| {
                set_int(o, bd, i64::MAX);
                set(o, best, 0);
                for_const(o, k, 0, K, R7, |o| {
                    get(o, d, X, p);
                    get(o, t, CX, k);
                    sub_assign(o, d, t);
                    mul_assign(o, d, d);
                    get(o, t, Y, p);
                    get(o, R7, CY, k);
                    sub_assign(o, t, R7);
                    mul_assign(o, t, t);
                    add_assign(o, d, t);
                    mov(o, t, d);
                    lt_assign(o, t, bd);
                    begin_if(o, t);
                    mov(o, bd, d);
                    mov(o, best, k);
                    end_if(o);
                });
                put(o, ASSIGN, p, best);
            });
            // the means
            set(o, t, 0);
            for_const(o, k, 0, K, R0, |o| {
                for array in [SX, SY, CNT] {
                    put(o, array, k, t);
                }
            });
            for_const(o, p, 0, P, R0, |o| {
                get(o, k, ASSIGN, p);
                for (from, to) in [(X, SX), (Y, SY)] {
                    get(o, d, from, p);
                    get(o, t, to, k);
                    add_assign(o, t, d);
                    put(o, to, k, t);
                }
                get(o, t, CNT, k);
                inc(o, t);
                put(o, CNT, k, t);
            });
            for_const(o, k, 0, K, R0, |o| {
                get(o, t, CNT, k);
                mov(o, d, t);
                gt_const(o, d, 0);
                begin_if(o, d);
                for (from, to) in [(SX, CX), (SY, CY)] {
                    get(o, d, from, k);
                    div_assign(o, d, t);
                    put(o, to, k, d);
                }
                end_if(o);
            });
        });
        for_const(o, k, 0, K, R0, |o| {
            get(o, t, CX, k);
            putint(o, t);
            puts(o, " ");
            get(o, t, CY, k);
            putint(o, t);
            puts(o, "\n");
        });
    });
    let c = format!(
        r#"{C_HEAD}{LCG_C}
#define P {P}
#define K {K}
static int64_t x[P], y[P], assign[P], cx[K], cy[K], sx[K], sy[K], cnt[K];
int main(void) {{
    int64_t seed = 2024;
    for (int64_t p = 0; p < P; p++) {{
        LCG(seed); x[p] = (seed >> 8) % 10000;
        LCG(seed); y[p] = (seed >> 8) % 10000;
    }}
    for (int k = 0; k < K; k++) {{ cx[k] = x[k]; cy[k] = y[k]; }}
    for (int r = 0; r < {ROUNDS}; r++) {{
        for (int64_t p = 0; p < P; p++) {{
            int64_t bd = INT64_MAX, best = 0;
            for (int64_t k = 0; k < K; k++) {{
                int64_t dx = x[p] - cx[k], dy = y[p] - cy[k], d = dx * dx + dy * dy;
                if (d < bd) {{ bd = d; best = k; }}
            }}
            assign[p] = best;
        }}
        for (int k = 0; k < K; k++) sx[k] = sy[k] = cnt[k] = 0;
        for (int64_t p = 0; p < P; p++) {{ int64_t k = assign[p]; sx[k] += x[p]; sy[k] += y[p]; cnt[k]++; }}
        for (int k = 0; k < K; k++) if (cnt[k] > 0) {{ cx[k] = sx[k] / cnt[k]; cy[k] = sy[k] / cnt[k]; }}
    }}
    for (int k = 0; k < K; k++) printf("%lld %lld\n", (long long)cx[k], (long long)cy[k]);
}}
"#
    );
    check("kmeans", &ops, &c);
}
