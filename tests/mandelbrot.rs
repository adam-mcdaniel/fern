//! The Mandelbrot set in fixed point (12 bits of fraction) on a 1280 by 960
//! grid, at most 200 iterations a point: the total of the iterations.

mod common;

use bf::asm::*;
use common::*;

const W: i64 = 1280;
const H: i64 = 960;

#[test]
fn mandelbrot_prints_what_c_does() {
    let (sx, sy) = (3 * 4096 / W, 2 * 4096 / H);
    let ops = program(|o| {
        let (p, cx, cy, zr, zi, zr2, zi2, k, total, t) = (R1, R2, R3, R4, R5, R6, R7, R8, R9, R0);
        set(o, p, 0);
        set(o, total, 0);
        while_loop(o, t, |o| { mov(o, t, p); lt_const(o, t, W * H); }, |o| {
            mov(o, cx, p);
            rem_const(o, cx, W);
            mul_const(o, cx, sx);
            sub_const(o, cx, 8192);
            mov(o, cy, p);
            div_const(o, cy, W);
            mul_const(o, cy, sy);
            sub_const(o, cy, 4096);
            set(o, zr, 0);
            set(o, zi, 0);
            set(o, k, 0);
            begin_loop(o);
            mov(o, zr2, zr);
            mul_assign(o, zr2, zr);
            rsh_const(o, zr2, 12);
            mov(o, zi2, zi);
            mul_assign(o, zi2, zi);
            rsh_const(o, zi2, 12);
            mov(o, t, zr2);
            add_assign(o, t, zi2);
            gt_const(o, t, 4 * 4096);
            break_if(o, t);
            mov(o, t, k);
            ge_const(o, t, 200);
            break_if(o, t);
            mul_assign(o, zi, zr);
            add_assign(o, zi, zi);
            rsh_const(o, zi, 12);
            add_assign(o, zi, cy);
            mov(o, zr, zr2);
            sub_assign(o, zr, zi2);
            add_assign(o, zr, cx);
            inc(o, k);
            end_loop(o);
            add_assign(o, total, k);
            inc(o, p);
        });
        putint(o, total);
        puts(o, "\n");
    });
    let c = format!(
        r#"{C_HEAD}
int main(void) {{
    int64_t total = 0;
    for (int64_t p = 0; p < {W} * {H}; p++) {{
        int64_t cx = p % {W} * {sx} - 8192, cy = p / {W} * {sy} - 4096, zr = 0, zi = 0, k = 0;
        for (;;) {{
            int64_t zr2 = (zr * zr) >> 12, zi2 = (zi * zi) >> 12;
            if (zr2 + zi2 > 4 * 4096) break;
            if (k >= 200) break;
            zi = ((zi * zr * 2) >> 12) + cy;
            zr = zr2 - zi2 + cx;
            k++;
        }}
        total += k;
    }}
    printf("%lld\n", (long long)total);
}}
"#
    );
    check("mandelbrot", &ops, &c);
}
