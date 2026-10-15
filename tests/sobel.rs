//! Sobel edge detection (|gx| + |gy|) on a random 300 by 150 image, 20
//! times over (each result scaled back to a byte as the next image); prints
//! a checksum.

mod common;

use bf::asm::*;
use common::*;

const W: i64 = 300;
const H: i64 = 150;
const ROUNDS: i64 = 20;

#[test]
fn sobel_prints_what_c_does() {
    let cells = W * H;
    let ops = program(|o| {
        let (img, out, i, gx, gy, t, k) = (R1, R2, R3, R4, R5, R6, R7);
        heap_alloc_const(o, img, cells);
        heap_alloc_const(o, out, cells);
        set(o, R8, 3);
        for_const(o, i, 0, cells, R0, |o| {
            lcg(o, R8);
            mov(o, t, R8);
            rshu_const(o, t, 11);
            and_const(o, t, 255);
            store_index(o, img, i, t);
            store_index(o, out, i, t);
        });
        let px = |o: &mut dyn Program, dst: &Location, d: i64| {
            mov(o, k, i);
            add_const(o, k, d);
            load_index(o, dst, img, k);
        };
        for_const(o, R9, 0, ROUNDS, R0, |o| {
            for_const(o, i, W + 1, cells - W - 1, R0, |o| {
                // gx = (r - l) weighted 1 2 1 down the rows; gy likewise across
                set(o, gx, 0);
                set(o, gy, 0);
                for (d, wx, wy) in [(-W - 1, -1, -1), (-W, 0, -2), (-W + 1, 1, -1), (-1, -2, 0), (1, 2, 0), (W - 1, -1, 1), (W, 0, 2), (W + 1, 1, 1)] {
                    px(o, t, d);
                    if wx != 0 {
                        push(o, t);
                        mul_const(o, t, wx);
                        add_assign(o, gx, t);
                        pop(o, t);
                    }
                    if wy != 0 {
                        mul_const(o, t, wy);
                        add_assign(o, gy, t);
                    }
                }
                abs_assign(o, gx);
                abs_assign(o, gy);
                add_assign(o, gx, gy);
                rsh_const(o, gx, 2);
                and_const(o, gx, 255);
                store_index(o, out, i, gx);
            });
            mov(o, t, img);
            mov(o, img, out);
            mov(o, out, t);
        });
        set(o, gx, 0);
        for_const(o, i, 0, cells, R0, |o| {
            load_index(o, t, img, i);
            mov(o, k, i);
            rem_const(o, k, 9);
            inc(o, k);
            mul_assign(o, t, k);
            add_assign(o, gx, t);
        });
        putint(o, gx);
        puts(o, "\n");
    });
    let c = format!(
        r#"{C_HEAD}{LCG_C}
#define W {W}
#define CELLS ({W} * {H})
static int64_t a[CELLS], b[CELLS];
static int64_t iabs(int64_t x) {{ return x < 0 ? -x : x; }}
int main(void) {{
    int64_t *img = a, *out = b, seed = 3;
    for (int64_t i = 0; i < CELLS; i++) {{ LCG(seed); img[i] = out[i] = (seed >> 11) & 255; }}
    for (int r = 0; r < {ROUNDS}; r++) {{
        for (int64_t i = W + 1; i < CELLS - W - 1; i++) {{
            int64_t gx = -img[i - W - 1] + img[i - W + 1] - 2 * img[i - 1] + 2 * img[i + 1] - img[i + W - 1] + img[i + W + 1];
            int64_t gy = -img[i - W - 1] - 2 * img[i - W] - img[i - W + 1] + img[i + W - 1] + 2 * img[i + W] + img[i + W + 1];
            out[i] = ((iabs(gx) + iabs(gy)) >> 2) & 255;
        }}
        int64_t *t = img; img = out; out = t;
    }}
    int64_t sum = 0;
    for (int64_t i = 0; i < CELLS; i++) sum += img[i] * (i % 9 + 1);
    printf("%lld\n", (long long)sum);
}}
"#
    );
    check("sobel", &ops, &c);
}
