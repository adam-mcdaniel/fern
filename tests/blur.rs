//! A 3 by 3 box blur, 40 times over, of a random 256 by 150 image; prints a
//! weighted sum of the pixels.

mod common;

use bf::asm::*;
use common::*;

const W: i64 = 256;
const H: i64 = 150;
const PASSES: i64 = 40;

#[test]
fn blur_prints_what_c_does() {
    let cells = W * H;
    let ops = program(|o| {
        let (img, out, i, s, t, k, seed) = (R1, R2, R3, R4, R5, R6, R8);
        set(o, R7, cells as u64);
        heap_alloc(o, img, R7);
        heap_alloc(o, out, R7);
        set(o, seed, 42);
        for_const(o, i, 0, cells, R0, |o| {
            lcg(o, seed);
            mov(o, t, seed);
            rshu_const(o, t, 16);
            and_const(o, t, 255);
            store_index(o, img, i, t);
            store_index(o, out, i, t);
        });
        for_const(o, R9, 0, PASSES, R7, |o| {
            for_const(o, i, W + 1, cells - W - 1, R0, |o| {
                set(o, s, 0);
                for d in [-W - 1, -W, -W + 1, -1, 0, 1, W - 1, W, W + 1] {
                    mov(o, k, i);
                    add_const(o, k, d);
                    load_index(o, t, img, k);
                    add_assign(o, s, t);
                }
                div_const(o, s, 9);
                store_index(o, out, i, s);
            });
            mov(o, t, img);
            mov(o, img, out);
            mov(o, out, t);
        });
        set(o, s, 0);
        for_const(o, i, 0, cells, R0, |o| {
            load_index(o, t, img, i);
            mov(o, k, i);
            rem_const(o, k, 7);
            inc(o, k);
            mul_assign(o, t, k);
            add_assign(o, s, t);
        });
        putint(o, s);
        puts(o, "\n");
    });
    let c = format!(
        r#"{C_HEAD}{LCG_C}
#define W {W}
#define CELLS ({W} * {H})
static int64_t a[CELLS], b[CELLS];
int main(void) {{
    int64_t *img = a, *out = b, seed = 42;
    for (int64_t i = 0; i < CELLS; i++) {{ LCG(seed); img[i] = out[i] = (seed >> 16) & 255; }}
    for (int p = 0; p < {PASSES}; p++) {{
        for (int64_t i = W + 1; i < CELLS - W - 1; i++) {{
            int64_t s = 0;
            for (int dy = -1; dy <= 1; dy++) for (int dx = -1; dx <= 1; dx++) s += img[i + dy * W + dx];
            out[i] = s / 9;
        }}
        int64_t *t = img; img = out; out = t;
    }}
    int64_t sum = 0;
    for (int64_t i = 0; i < CELLS; i++) sum += img[i] * (i % 7 + 1);
    printf("%lld\n", (long long)sum);
}}
"#
    );
    check("blur", &ops, &c);
}
