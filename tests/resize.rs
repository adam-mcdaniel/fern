//! Bilinear resizing of a 200x200 image up to 900x900, in Q8: four reads
//! and three blends per pixel; prints a checksum of the result.

mod common;

use bf::asm::*;
use common::*;

const S: i64 = 200;
const D: i64 = 900;
// the globals
const SUM: i64 = 0;
const YF: i64 = 1;
const XF: i64 = 2;
const IMG: i64 = 3;
const Y: i64 = 4;
const FY: i64 = 5;
const ROW: i64 = 6;

#[test]
fn resize_prints_what_c_does() {
    let ops = program(|o| {
        let (x, sx, fx, a, b, at, t, u) = (R1, R2, R3, R4, R5, R6, R7, R8);
        heap_alloc_const(o, R9, 7);
        heap_alloc_const(o, t, S * S);
        mov(o, &g(IMG), t);
        // the image: rings and stripes
        for_const(o, a, 0, S * S, R0, |o| {
            mov(o, t, a);
            div_const(o, t, S);
            mov(o, u, a);
            rem_const(o, u, S);
            mov(o, b, t);
            mul_assign(o, b, t);
            mov(o, at, u);
            mul_assign(o, at, u);
            add_assign(o, b, at);
            rshu_const(o, b, 5);
            mul_const(o, u, 3);
            add_assign(o, b, u);
            and_const(o, b, 255);
            put(o, IMG, a, b);
        });
        set(o, &g(SUM), 0);
        for_const(o, &g(Y), 0, D, &g(YF), |o| {
            // the source row, and how far between it and the next
            mov(o, t, &g(Y));
            mul_const(o, t, (S - 1) * 256);
            div_const(o, t, D - 1);
            mov(o, &g(FY), t);
            and_const(o, &g(FY), 255);
            rshu_const(o, t, 8);
            mul_const(o, t, S);
            mov(o, &g(ROW), t);
            for_const(o, x, 0, D, &g(XF), |o| {
                mov(o, sx, x);
                mul_const(o, sx, (S - 1) * 256);
                div_const(o, sx, D - 1);
                mov(o, fx, sx);
                and_const(o, fx, 255);
                rshu_const(o, sx, 8);
                // (clamped, at the last column and row)
                set_int(o, t, S - 2);
                min_assign(o, sx, t);
                mov(o, at, &g(ROW));
                set_int(o, t, (S - 2) * S);
                min_assign(o, at, t);
                add_assign(o, at, sx);
                // a = img[at] + (img[at + 1] - img[at]) * fx >> 8, and b the row below
                for (dst, off) in [(a, 0), (b, S)] {
                    mov(o, u, at);
                    add_const(o, u, off);
                    get(o, dst, IMG, u);
                    inc(o, u);
                    get(o, t, IMG, u);
                    sub_assign(o, t, dst);
                    mul_assign(o, t, fx);
                    rsh_const(o, t, 8);
                    add_assign(o, dst, t);
                }
                sub_assign(o, b, a);
                mul_assign(o, b, &g(FY));
                rsh_const(o, b, 8);
                add_assign(o, a, b);
                mov(o, t, x);
                and_const(o, t, 7);
                inc(o, t);
                mul_assign(o, a, t);
                add_assign(o, &g(SUM), a);
            });
        });
        putint(o, &g(SUM));
        puts(o, "\n");
    });
    let c = format!(
        r#"{C_HEAD}
#define S {S}
#define D {D}
static int64_t img[S * S];
int main(void) {{
    for (int64_t k = 0; k < S * S; k++) {{
        int64_t r = k / S, c = k % S;
        img[k] = (((uint64_t)(r * r + c * c) >> 5) + c * 3) & 255;
    }}
    int64_t sum = 0;
    for (int64_t y = 0; y < D; y++) {{
        int64_t t = y * ((S - 1) * 256) / (D - 1);
        int64_t fy = t & 255, row = (t >> 8) * S;
        for (int64_t x = 0; x < D; x++) {{
            int64_t sx = x * ((S - 1) * 256) / (D - 1);
            int64_t fx = sx & 255;
            sx >>= 8;
            if (sx > S - 2) sx = S - 2;
            int64_t at = (row < (S - 2) * S ? row : (S - 2) * S) + sx;
            int64_t a = img[at] + ((img[at + 1] - img[at]) * fx >> 8);
            int64_t b = img[at + S] + ((img[at + S + 1] - img[at + S]) * fx >> 8);
            a += (b - a) * fy >> 8;
            sum += a * ((x & 7) + 1);
        }}
    }}
    printf("%lld\n", (long long)sum);
}}
"#
    );
    check("resize", &ops, &c);
}
