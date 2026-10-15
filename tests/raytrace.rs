//! A ray tracer: five spheres over a checked floor, lit from one direction,
//! with shadows, in Q12. Prints the sum of the pixels and how many are
//! bright.

mod common;

use bf::asm::*;
use bf::Op;
use common::*;

const ONE: i64 = 4096;
const SPHERES: [[i64; 5]; 5] = [
    [0, 0, 20480, 4096, 220],
    [-9000, -1000, 24000, 3000, 180],
    [9000, -1500, 23000, 2500, 200],
    [2500, 3500, 30000, 3500, 160],
    [-4000, 4000, 18000, 1200, 240],
];

fn light() -> [i64; 3] {
    let (x, y, z) = (-1.0f64, 2.0, -1.5);
    let len = (x * x + y * y + z * z).sqrt();
    [x, y, z].map(|c| (c / len * ONE as f64).round() as i64)
}

pub fn raytrace(width: i64, height: i64) -> Vec<Op> {
    let [lx, ly, lz] = light();
    program(|o| {
        isqrt_func(o);

        // hit(ox, oy, oz, dx, dy, dz, k): how far along the ray sphere k is,
        // or -1, into R0
        begin_func(o, "hit", 10);
        mov(o, &l(8), &arg(6));
        mul_const(o, &l(8), 5);
        for (c, a) in [(0, 0), (1, 1), (2, 2)] {
            get(o, &l(c), 0, &l(8));
            sub_assign(o, &l(c), &arg(a));
            inc(o, &l(8));
        }
        get(o, &l(9), 0, &l(8));
        // b = oc.d, c = oc.oc - r^2
        set(o, &l(3), 0);
        set(o, &l(4), 0);
        for (c, a) in [(0, 3), (1, 4), (2, 5)] {
            mov(o, &l(5), &l(c));
            mul_assign(o, &l(5), &arg(a));
            add_assign(o, &l(3), &l(5));
            mov(o, &l(5), &l(c));
            mul_assign(o, &l(5), &l(c));
            add_assign(o, &l(4), &l(5));
        }
        rsh_const(o, &l(3), 12);
        rsh_const(o, &l(4), 12);
        mul_assign(o, &l(9), &l(9));
        rsh_const(o, &l(9), 12);
        sub_assign(o, &l(4), &l(9));
        mov(o, &l(6), &l(3));
        mul_assign(o, &l(6), &l(3));
        rsh_const(o, &l(6), 12);
        sub_assign(o, &l(6), &l(4));
        set_int(o, &l(5), -1);
        mov(o, &l(7), &l(6));
        gt_const(o, &l(7), 0);
        begin_if(o, &l(7));
        lsh_const(o, &l(6), 12);
        call(o, "isqrt", &[&l(6)]);
        mov(o, &l(7), R0);
        mov(o, &l(9), &l(3));
        sub_assign(o, &l(9), &l(7));
        mov(o, &l(4), &l(9));
        le_const(o, &l(4), 64);
        begin_if(o, &l(4));
        mov(o, &l(9), &l(3));
        add_assign(o, &l(9), &l(7));
        end_if(o);
        mov(o, &l(4), &l(9));
        gt_const(o, &l(4), 64);
        begin_if(o, &l(4));
        mov(o, &l(5), &l(9));
        end_if(o);
        end_if(o);
        mov(o, R0, &l(5));
        end_func(o);

        // shadowed(ox, oy, oz): whether a sphere is in the way of the light
        begin_func(o, "shadowed", 5);
        set(o, &l(0), 0);
        set_int(o, &l(1), lx);
        set_int(o, &l(2), ly);
        set_int(o, &l(3), lz);
        for k in 0..SPHERES.len() as u64 {
            set(o, &l(4), k);
            call(o, "hit", &[&arg(0), &arg(1), &arg(2), &l(1), &l(2), &l(3), &l(4)]);
            gt_const(o, R0, 0);
            add_assign(o, &l(0), R0);
        }
        mov(o, R0, &l(0));
        end_func(o);

        // shade(p): pixel p's brightness, into R0
        begin_func(o, "shade", 21);
        mov(o, &l(0), &arg(0));
        rem_const(o, &l(0), width);
        mov(o, &l(1), &arg(0));
        div_const(o, &l(1), width);
        // the ray through the pixel, normalized
        mov(o, &l(2), &l(0));
        add_assign(o, &l(2), &l(2));
        add_const(o, &l(2), 1 - width);
        mul_const(o, &l(2), 32);
        mov(o, &l(3), &l(1));
        add_assign(o, &l(3), &l(3));
        neg_assign(o, &l(3));
        add_const(o, &l(3), height - 1);
        mul_const(o, &l(3), 32);
        set(o, &l(4), (width * 32) as u64);
        set(o, &l(5), 0);
        for d in 2..5 {
            mov(o, &l(18), &l(d));
            mul_assign(o, &l(18), &l(d));
            add_assign(o, &l(5), &l(18));
        }
        call(o, "isqrt", &[&l(5)]);
        mov(o, &l(5), R0);
        for d in 2..5 {
            lsh_const(o, &l(d), 12);
            div_assign(o, &l(d), &l(5));
        }
        // the nearest sphere
        set_int(o, &l(6), 1 << 40);
        set_int(o, &l(7), -1);
        set(o, &l(20), 0);
        for k in 0..SPHERES.len() as u64 {
            set(o, &l(8), k);
            call(o, "hit", &[&l(20), &l(20), &l(20), &l(2), &l(3), &l(4), &l(8)]);
            mov(o, &l(9), R0);
            mov(o, &l(18), &l(9));
            gt_const(o, &l(18), 0);
            mov(o, &l(19), &l(9));
            lt_assign(o, &l(19), &l(6));
            mul_assign(o, &l(18), &l(19));
            begin_if(o, &l(18));
            mov(o, &l(6), &l(9));
            mov(o, &l(7), &l(8));
            end_if(o);
        }
        mov(o, &l(18), &l(7));
        inc(o, &l(18));
        begin_if(o, &l(18));
        // lit by how the normal faces the light, unless in a shadow
        mov(o, &l(19), &l(7));
        mul_const(o, &l(19), 5);
        for (h, d, nrm) in [(10, 2, 13), (11, 3, 14), (12, 4, 15)] {
            mov(o, &l(h), &l(d));
            mul_assign(o, &l(h), &l(6));
            rsh_const(o, &l(h), 12);
            get(o, &l(nrm), 0, &l(19));
            neg_assign(o, &l(nrm));
            add_assign(o, &l(nrm), &l(h));
            lsh_const(o, &l(nrm), 12);
            inc(o, &l(19));
        }
        get(o, &l(17), 0, &l(19));
        for nrm in 13..16 {
            div_assign(o, &l(nrm), &l(17));
        }
        set(o, &l(16), 0);
        for (nrm, c) in [(13, lx), (14, ly), (15, lz)] {
            mov(o, &l(18), &l(nrm));
            mul_const(o, &l(18), c);
            add_assign(o, &l(16), &l(18));
        }
        rsh_const(o, &l(16), 12);
        mov(o, &l(18), &l(16));
        lt_const(o, &l(18), 0);
        begin_if(o, &l(18));
        set(o, &l(16), 0);
        end_if(o);
        for (h, nrm) in [(10, 13), (11, 14), (12, 15)] {
            mov(o, &l(18), &l(nrm));
            rsh_const(o, &l(18), 8);
            add_assign(o, &l(h), &l(18));
        }
        call(o, "shadowed", &[&l(10), &l(11), &l(12)]);
        begin_if(o, R0);
        rsh_const(o, &l(16), 2);
        end_if(o);
        inc(o, &l(19));
        get(o, &l(18), 0, &l(19));
        mul_assign(o, &l(16), &l(18));
        rsh_const(o, &l(16), 12);
        add_const(o, &l(16), 20);
        mov(o, &l(17), &l(16));
        begin_else(o);
        set(o, &l(17), 30);
        // the floor, at y = -1, checked
        mov(o, &l(18), &l(3));
        lt_const(o, &l(18), 0);
        begin_if(o, &l(18));
        set_int(o, &l(9), -ONE << 12);
        div_assign(o, &l(9), &l(3));
        mov(o, &l(10), &l(2));
        mul_assign(o, &l(10), &l(9));
        rsh_const(o, &l(10), 12);
        mov(o, &l(12), &l(4));
        mul_assign(o, &l(12), &l(9));
        rsh_const(o, &l(12), 12);
        mov(o, &l(18), &l(10));
        rsh_const(o, &l(18), 12);
        mov(o, &l(19), &l(12));
        rsh_const(o, &l(19), 12);
        add_assign(o, &l(18), &l(19));
        and_const(o, &l(18), 1);
        mul_const(o, &l(18), 140);
        add_const(o, &l(18), 60);
        mov(o, &l(17), &l(18));
        set_int(o, &l(11), 16 - ONE);
        call(o, "shadowed", &[&l(10), &l(11), &l(12)]);
        begin_if(o, R0);
        rsh_const(o, &l(17), 1);
        end_if(o);
        end_if(o);
        end_if(o);
        mov(o, R0, &l(17));
        end_func(o);

        heap_alloc_const(o, R9, 4);
        heap_alloc_const(o, R1, 5 * SPHERES.len() as i64);
        mov(o, &g(0), R1);
        for (k, s) in SPHERES.iter().flatten().enumerate() {
            set(o, R1, k as u64);
            set_int(o, R2, *s);
            put(o, 0, R1, R2);
        }
        set(o, R1, 0);
        set(o, R3, 0);
        set(o, R4, 0);
        while_loop(o, R0, |o| { mov(o, R0, R1); lt_const(o, R0, width * height); }, |o| {
            call(o, "shade", &[R1]);
            add_assign(o, R3, R0);
            gt_const(o, R0, 150);
            add_assign(o, R4, R0);
            inc(o, R1);
        });
        putint(o, R3);
        puts(o, " ");
        putint(o, R4);
        puts(o, "\n");
    })
}

pub fn raytrace_c(width: i64, height: i64) -> String {
    let [lx, ly, lz] = light();
    let spheres: Vec<String> = SPHERES.iter().flatten().map(|s| s.to_string()).collect();
    format!(
        r#"#include <stdio.h>
#include <stdint.h>
{ISQRT_C}
static const int64_t sph[] = {{{spheres}}};
#define NS {ns}

static int64_t hit(int64_t ox, int64_t oy, int64_t oz, int64_t dx, int64_t dy, int64_t dz, int64_t k) {{
    const int64_t *s = sph + 5 * k;
    int64_t cx = s[0] - ox, cy = s[1] - oy, cz = s[2] - oz, r = s[3];
    int64_t b = (cx * dx + cy * dy + cz * dz) >> 12;
    int64_t c = ((cx * cx + cy * cy + cz * cz) >> 12) - ((r * r) >> 12);
    int64_t disc = ((b * b) >> 12) - c;
    int64_t t = -1;
    if (disc > 0) {{
        int64_t q = isqrt(disc << 12);
        int64_t u = b - q;
        if (u <= 64) u = b + q;
        if (u > 64) t = u;
    }}
    return t;
}}

static int64_t shadowed(int64_t ox, int64_t oy, int64_t oz) {{
    int64_t n = 0;
    for (int k = 0; k < NS; k++) n += hit(ox, oy, oz, {lx}, {ly}, {lz}, k) > 0;
    return n;
}}

static int64_t shade(int64_t p) {{
    int64_t px = p % {width}, py = p / {width};
    int64_t d[3] = {{(2 * px + 1 - {width}) * 32, ({height} - 1 - 2 * py) * 32, {width} * 32}};
    int64_t len = isqrt(d[0] * d[0] + d[1] * d[1] + d[2] * d[2]);
    for (int a = 0; a < 3; a++) d[a] = (d[a] << 12) / len;
    int64_t tmin = (int64_t)1 << 40, hk = -1;
    for (int k = 0; k < NS; k++) {{
        int64_t t = hit(0, 0, 0, d[0], d[1], d[2], k);
        if ((t > 0) * (t < tmin)) {{ tmin = t; hk = k; }}
    }}
    int64_t col;
    if (hk + 1) {{
        const int64_t *s = sph + 5 * hk;
        int64_t h[3], n[3];
        for (int a = 0; a < 3; a++) {{ h[a] = (d[a] * tmin) >> 12; n[a] = (h[a] - s[a]) << 12; }}
        for (int a = 0; a < 3; a++) n[a] /= s[3];
        int64_t diff = (n[0] * {lx} + n[1] * {ly} + n[2] * {lz}) >> 12;
        if (diff < 0) diff = 0;
        for (int a = 0; a < 3; a++) h[a] += n[a] >> 8;
        if (shadowed(h[0], h[1], h[2])) diff >>= 2;
        col = ((diff * s[4]) >> 12) + 20;
    }} else {{
        col = 30;
        if (d[1] < 0) {{
            int64_t t = ({minus_one} << 12) / d[1];
            int64_t hx = (d[0] * t) >> 12, hz = (d[2] * t) >> 12;
            col = (((hx >> 12) + (hz >> 12)) & 1) * 140 + 60;
            if (shadowed(hx, {floor}, hz)) col >>= 1;
        }}
    }}
    return col;
}}

int main(void) {{
    int64_t sum = 0, bright = 0;
    for (int64_t p = 0; p < {width} * {height}; p++) {{
        int64_t c = shade(p);
        sum += c;
        bright += c > 150;
    }}
    printf("%lld %lld\n", (long long)sum, (long long)bright);
    return 0;
}}
"#,
        spheres = spheres.join(", "),
        ns = SPHERES.len(),
        minus_one = -ONE,
        floor = 16 - ONE
    )
}

#[test]
fn raytrace_prints_what_c_does() {
    check("raytrace", &raytrace(1280, 960), &raytrace_c(1280, 960));
}
