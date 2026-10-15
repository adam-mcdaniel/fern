//! The 8 by 8 DCT (in Q12, by its matrix: rows, then columns) of every
//! block of a random 128 by 96 image, 20 times over; prints a checksum of
//! the coefficients.

mod common;

use bf::asm::*;
use common::*;

const W: i64 = 128;
const H: i64 = 96;
const ROUNDS: i64 = 20;

fn coefficients() -> Vec<i64> {
    let mut c = vec![];
    for u in 0..8 {
        for x in 0..8 {
            let s = if u == 0 { (1.0f64 / 8.0).sqrt() } else { (2.0f64 / 8.0).sqrt() };
            c.push((s * ((2 * x + 1) as f64 * u as f64 * std::f64::consts::PI / 16.0).cos() * 4096.0).round() as i64);
        }
    }
    c
}

#[test]
fn dct_prints_what_c_does() {
    let blocks = (W / 8) * (H / 8);
    let cs = coefficients();
    let ops = program(|o| {
        let (img, coef, tmp, out, b, t, u, s) = (R1, R2, R3, R4, R5, R6, R7, R8);
        heap_alloc_const(o, img, W * H);
        heap_alloc_const(o, coef, 64);
        heap_alloc_const(o, tmp, 64 * blocks);
        heap_alloc_const(o, out, 64 * blocks);
        for (k, c) in cs.iter().enumerate() {
            set(o, t, k as u64);
            set_int(o, u, *c);
            store_index(o, coef, t, u);
        }
        set(o, R9, 5);
        for_const(o, b, 0, W * H, R0, |o| {
            lcg(o, R9);
            mov(o, t, R9);
            rshu_const(o, t, 10);
            and_const(o, t, 255);
            sub_const(o, t, 128);
            store_index(o, img, b, t);
        });
        // each block: rows (u, y) then columns (u, v), in its own part of tmp
        // and out
        // (the round, on the stack: the body's pushes and pops are even)
        push(o, R0);
        for_const(o, &SP.deref().offset(-1), 0, ROUNDS, R0, |o| {
        for_const(o, b, 0, blocks, R0, |o| {
            for_const(o, R9, 0, 64, R0, |o| {
                // tmp[b][y][u] = sum_x coef[u][x] img[block's row y, column x]
                set(o, s, 0);
                for x in 0..8 {
                    mov(o, t, R9);
                    and_const(o, t, 7);
                    mul_const(o, t, 8);
                    add_const(o, t, x);
                    load_index(o, u, coef, t);
                    // the pixel: block b's corner, plus y rows, plus x
                    mov(o, t, b);
                    rem_const(o, t, W / 8);
                    mul_const(o, t, 8);
                    push(o, t);
                    mov(o, t, b);
                    div_const(o, t, W / 8);
                    mul_const(o, t, 8);
                    mov(o, R0, R9);
                    rshu_const(o, R0, 3);
                    add_assign(o, t, R0);
                    mul_const(o, t, W);
                    pop(o, R0);
                    add_assign(o, t, R0);
                    add_const(o, t, x);
                    load_index(o, t, img, t);
                    mul_assign(o, t, u);
                    add_assign(o, s, t);
                }
                rsh_const(o, s, 12);
                mov(o, t, b);
                mul_const(o, t, 64);
                add_assign(o, t, R9);
                store_index(o, tmp, t, s);
            });
            for_const(o, R9, 0, 64, R0, |o| {
                // out[b][v][u] = sum_y coef[v][y] tmp[b][y][u]
                set(o, s, 0);
                for y in 0..8 {
                    mov(o, t, R9);
                    rshu_const(o, t, 3);
                    mul_const(o, t, 8);
                    add_const(o, t, y);
                    load_index(o, u, coef, t);
                    mov(o, t, b);
                    mul_const(o, t, 64);
                    add_const(o, t, y * 8);
                    mov(o, R0, R9);
                    and_const(o, R0, 7);
                    add_assign(o, t, R0);
                    load_index(o, t, tmp, t);
                    mul_assign(o, t, u);
                    add_assign(o, s, t);
                }
                rsh_const(o, s, 12);
                mov(o, t, b);
                mul_const(o, t, 64);
                add_assign(o, t, R9);
                store_index(o, out, t, s);
            });
        });
        });
        pop(o, R0);
        set(o, s, 0);
        for_const(o, b, 0, 64 * blocks, R0, |o| {
            load_index(o, t, out, b);
            mov(o, u, b);
            rem_const(o, u, 11);
            inc(o, u);
            mul_assign(o, t, u);
            add_assign(o, s, t);
        });
        putint(o, s);
        puts(o, "\n");
    });
    let coef: Vec<String> = cs.iter().map(|c| c.to_string()).collect();
    let c = format!(
        r#"{C_HEAD}{LCG_C}
#define W {W}
#define H {H}
#define BLOCKS ((W / 8) * (H / 8))
static const int64_t coef[64] = {{{}}};
static int64_t img[W * H], tmp[64 * BLOCKS], out[64 * BLOCKS];
int main(void) {{
    int64_t seed = 5;
    for (int64_t i = 0; i < W * H; i++) {{ LCG(seed); img[i] = ((seed >> 10) & 255) - 128; }}
    for (int r = 0; r < {ROUNDS}; r++)
    for (int64_t b = 0; b < BLOCKS; b++) {{
        int64_t cx = b % (W / 8) * 8, cy = b / (W / 8) * 8;
        for (int64_t k = 0; k < 64; k++) {{
            int64_t s = 0, y = k >> 3, u = k & 7;
            for (int64_t x = 0; x < 8; x++) s += img[(cy + y) * W + cx + x] * coef[u * 8 + x];
            tmp[b * 64 + k] = s >> 12;
        }}
        for (int64_t k = 0; k < 64; k++) {{
            int64_t s = 0, v = k >> 3, u = k & 7;
            for (int64_t y = 0; y < 8; y++) s += tmp[b * 64 + y * 8 + u] * coef[v * 8 + y];
            out[b * 64 + k] = s >> 12;
        }}
    }}
    int64_t sum = 0;
    for (int64_t i = 0; i < 64 * BLOCKS; i++) sum += out[i] * (i % 11 + 1);
    printf("%lld\n", (long long)sum);
}}
"#,
        coef.join(", ")
    );
    check("dct", &ops, &c);
}
