//! A Voronoi diagram: for each pixel of an 800x600 image, the nearest of 48
//! random seeds; prints a sum over the pixels of the distance and the seed.

mod common;

use bf::asm::*;
use common::*;

const W: i64 = 800;
const H: i64 = 600;
const K: i64 = 48;
// the globals
const SUM: i64 = 0;
const YF: i64 = 1;
const XF: i64 = 2;
const SX: i64 = 3;
const SY: i64 = 4;

#[test]
fn voronoi_prints_what_c_does() {
    let ops = program(|o| {
        let (seed, y, x, k, bd, best, d, t) = (R1, R2, R3, R4, R5, R6, R7, R8);
        heap_alloc_const(o, R9, 5);
        for array in [SX, SY] {
            heap_alloc_const(o, t, K);
            mov(o, &g(array), t);
        }
        set(o, seed, 7);
        for_const(o, k, 0, K, R0, |o| {
            for (array, n) in [(SX, W), (SY, H)] {
                lcg(o, seed);
                mov(o, t, seed);
                rshu_const(o, t, 8);
                rem_const(o, t, n);
                put(o, array, k, t);
            }
        });
        set(o, &g(SUM), 0);
        for_const(o, y, 0, H, &g(YF), |o| {
            for_const(o, x, 0, W, &g(XF), |o| {
                set_int(o, bd, i64::MAX);
                set(o, best, 0);
                for_const(o, k, 0, K, R0, |o| {
                    mov(o, d, x);
                    get(o, t, SX, k);
                    sub_assign(o, d, t);
                    mul_assign(o, d, d);
                    mov(o, t, y);
                    get(o, R0, SY, k);
                    sub_assign(o, t, R0);
                    mul_assign(o, t, t);
                    add_assign(o, d, t);
                    mov(o, t, d);
                    lt_assign(o, t, bd);
                    begin_if(o, t);
                    mov(o, bd, d);
                    mov(o, best, k);
                    end_if(o);
                });
                mov(o, t, best);
                mul_const(o, t, 1000);
                add_assign(o, t, bd);
                add_assign(o, &g(SUM), t);
            });
        });
        putint(o, &g(SUM));
        puts(o, "\n");
    });
    let c = format!(
        r#"{C_HEAD}{LCG_C}
#define K {K}
static int64_t sx[K], sy[K];
int main(void) {{
    int64_t seed = 7;
    for (int k = 0; k < K; k++) {{
        LCG(seed); sx[k] = (seed >> 8) % {W};
        LCG(seed); sy[k] = (seed >> 8) % {H};
    }}
    int64_t sum = 0;
    for (int64_t y = 0; y < {H}; y++)
        for (int64_t x = 0; x < {W}; x++) {{
            int64_t bd = INT64_MAX, best = 0;
            for (int64_t k = 0; k < K; k++) {{
                int64_t d = (x - sx[k]) * (x - sx[k]) + (y - sy[k]) * (y - sy[k]);
                if (d < bd) {{ bd = d; best = k; }}
            }}
            sum += best * 1000 + bd;
        }}
    printf("%lld\n", (long long)sum);
}}
"#
    );
    check("voronoi", &ops, &c);
}
