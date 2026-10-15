//! Value noise: four octaves of bilinearly interpolated hashed lattice
//! values for each pixel of a 768x768 image, a function call per pixel;
//! prints the sum of the values and of their squares.

mod common;

use bf::asm::*;
use common::*;

const SIZE: i64 = 768;
const OCTAVES: i64 = 4;

/// `R1 = hash(ix + dx, iy + dy)` (uses `R2`).
fn hash(o: &mut dyn Program, ix: &Location, dx: i64, iy: &Location, dy: i64) {
    mov(o, R1, ix);
    add_const(o, R1, dx);
    mul_const(o, R1, 374_761_393);
    mov(o, R2, iy);
    add_const(o, R2, dy);
    mul_const(o, R2, 668_265_263);
    add_assign(o, R1, R2);
    mov(o, R2, R1);
    rsh_const(o, R2, 13);
    xor_assign(o, R1, R2);
    mul_const(o, R1, 1_274_126_177);
    mov(o, R2, R1);
    rsh_const(o, R2, 16);
    xor_assign(o, R1, R2);
    and_const(o, R1, 0xffff);
}

#[test]
fn noise_prints_what_c_does() {
    let ops = program(|o| {
        // noise(x, y), into R0 (uses R1 and R2)
        begin_func(o, "noise", 9);
        let (x, y, ix, iy, fx, fy, a, top, total) = (l(0), l(1), l(2), l(3), l(4), l(5), l(6), l(7), l(8));
        mov(o, &x, &arg(0));
        mov(o, &y, &arg(1));
        set(o, &total, 0);
        for oc in 0..OCTAVES {
            let sh = 6 - oc;
            for (i, f, v) in [(&ix, &fx, &x), (&iy, &fy, &y)] {
                mov(o, i, v);
                rsh_const(o, i, sh);
                mov(o, f, v);
                and_const(o, f, (1 << sh) - 1);
                lsh_const(o, f, 2 + oc);
            }
            // a lerp of b, into R1: R1 = a + ((R1 - a) * f >> 8)
            let lerp = |o: &mut dyn Program, a: &Location, f: &Location| {
                sub_assign(o, R1, a);
                mul_assign(o, R1, f);
                rsh_const(o, R1, 8);
                add_assign(o, R1, a);
            };
            hash(o, &ix, 0, &iy, 0);
            mov(o, &a, R1);
            hash(o, &ix, 1, &iy, 0);
            lerp(o, &a, &fx);
            mov(o, &top, R1);
            hash(o, &ix, 0, &iy, 1);
            mov(o, &a, R1);
            hash(o, &ix, 1, &iy, 1);
            lerp(o, &a, &fx);
            lerp(o, &top, &fy);
            rsh_const(o, R1, oc);
            add_assign(o, &total, R1);
        }
        mov(o, R0, &total);
        end_func(o);

        let (y, x, sum, sq, t) = (R5, R6, R7, R8, R9);
        set(o, sum, 0);
        set(o, sq, 0);
        for_const(o, y, 0, SIZE, R4, |o| {
            for_const(o, x, 0, SIZE, R3, |o| {
                call(o, "noise", &[x, y]);
                add_assign(o, sum, R0);
                mov(o, t, R0);
                mul_assign(o, t, t);
                add_assign(o, sq, t);
            });
        });
        putint(o, sum);
        puts(o, " ");
        putint(o, sq);
        puts(o, "\n");
    });
    let c = format!(
        r#"{C_HEAD}
static int64_t h(int64_t x, int64_t y) {{
    int64_t h = x * 374761393 + y * 668265263;
    h = (h ^ (h >> 13)) * 1274126177;
    h ^= h >> 16;
    return h & 0xffff;
}}
static int64_t lerp(int64_t a, int64_t b, int64_t f) {{ return a + ((b - a) * f >> 8); }}
static int64_t noise(int64_t x, int64_t y) {{
    int64_t total = 0;
    for (int oc = 0; oc < {OCTAVES}; oc++) {{
        int sh = 6 - oc;
        int64_t ix = x >> sh, iy = y >> sh;
        int64_t fx = (x & ((1 << sh) - 1)) << (2 + oc), fy = (y & ((1 << sh) - 1)) << (2 + oc);
        int64_t top = lerp(h(ix, iy), h(ix + 1, iy), fx);
        int64_t bot = lerp(h(ix, iy + 1), h(ix + 1, iy + 1), fx);
        total += lerp(top, bot, fy) >> oc;
    }}
    return total;
}}
int main(void) {{
    int64_t sum = 0, sq = 0;
    for (int64_t y = 0; y < {SIZE}; y++)
        for (int64_t x = 0; x < {SIZE}; x++) {{
            int64_t v = noise(x, y);
            sum += v;
            sq += v * v;
        }}
    printf("%lld %lld\n", (long long)sum, (long long)sq);
}}
"#
    );
    check("noise", &ops, &c);
}
