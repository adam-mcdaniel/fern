//! N-body: the solar system (the Sun, the planets, and an asteroid belt),
//! with forces worked out by Barnes-Hut on an octree.
//!
//! Lengths are in units of 2^-16 AU (L); positions are kept with 8 more bits
//! (Q8), velocities and accelerations with 16 (Q16), per day. Masses are GM
//! in L^3/day^2. Each step builds the octree (inserting the bodies one at a
//! time), works out each node's mass and centre of mass and threads it (each
//! node knows its first child and the node after its subtree, so it can be
//! walked without a stack), then for each body walks the tree, taking a node
//! as a whole if it's small for how far away it is (s/d < 1/2), and then
//! moves the bodies.

mod common;

use bf::asm::*;
use bf::Op;
use common::*;

const N: i64 = 0;
const X: i64 = 1;
const Y: i64 = 2;
const Z: i64 = 3;
const VX: i64 = 4;
const VY: i64 = 5;
const VZ: i64 = 6;
const GM: i64 = 7;
const W: i64 = 8;
const AX: i64 = 9;
const AY: i64 = 10;
const AZ: i64 = 11;
const NM: i64 = 12;
const NX: i64 = 13;
const NY: i64 = 14;
const NZ: i64 = 15;
const NCX: i64 = 16;
const NCY: i64 = 17;
const NCZ: i64 = 18;
const NH: i64 = 19;
const NCHILD: i64 = 20;
const NFIRST: i64 = 21;
const NNEXT: i64 = 22;
const NBODY: i64 = 23;
const NODES: i64 = 24;
const NW: i64 = 25;
const TRIG: i64 = 26;

/// Half the width of the root node (Q8 L): 128 AU.
const HALF: i64 = 1 << 31;
/// Softening, in L^2.
const EPS2: i64 = 1 << 16;
/// The asteroids' orbits: radii from 2.2 AU to 3.3 AU, within 0.05 AU of the
/// plane (Q8 L).
const RMIN: i64 = 36_909_875;
const RANGE: i64 = 18_454_938;
const ZR: i64 = 1_677_722;

/// GM of the Sun in AU^3/day^2.
const GM_SUN_AU: f64 = 2.959_122_082_855_911_5e-4;

/// The Sun and the planets: GM, position (Q8 L) and velocity (Q16 L/day),
/// on circular orbits.
fn planets() -> Vec<[i64; 7]> {
    // (semi-major axis in AU, mass as a fraction of the Sun's, angle)
    let orbits = [
        (0.387, 1.660e-7, 0.3),
        (0.723, 2.448e-6, 2.1),
        (1.000, 3.003e-6, 4.0),
        (1.524, 3.227e-7, 5.5),
        (5.203, 9.548e-4, 1.2),
        (9.537, 2.859e-4, 3.3),
        (19.19, 4.366e-5, 0.8),
        (30.07, 5.151e-5, 2.7),
    ];
    let gm_sun = GM_SUN_AU * 2f64.powi(48);
    let mut out = vec![[gm_sun.round() as i64, 0, 0, 0, 0, 0, 0]];
    for (a, frac, theta) in orbits {
        let (s, c) = f64::sin_cos(theta);
        let pos = a * 2f64.powi(24);
        let v = (GM_SUN_AU / a).sqrt() * 2f64.powi(32);
        out.push([(gm_sun * frac).round() as i64, (pos * c).round() as i64, (pos * s).round() as i64, 0, (-v * s).round() as i64, (v * c).round() as i64, 0]);
    }
    out
}

/// cos and sin of 64 angles round the circle, in Q16.
fn trig() -> Vec<(i64, i64)> {
    (0..64)
        .map(|k| {
            let (s, c) = f64::sin_cos(k as f64 * std::f64::consts::TAU / 64.0);
            ((c * 65536.0).round() as i64, (s * 65536.0).round() as i64)
        })
        .collect()
}

fn gm_sun() -> i64 {
    planets()[0][0]
}

/// The octant of body `b` in a node centred at `cx`, `cy`, `cz`.
fn octant(o: &mut dyn Program, dst: &Location, t: &Location, b: &Location, cx: &Location, cy: &Location, cz: &Location) {
    get(o, dst, X, b);
    gt_assign(o, dst, cx);
    get(o, t, Y, b);
    gt_assign(o, t, cy);
    add_assign(o, t, t);
    add_assign(o, dst, t);
    get(o, t, Z, b);
    gt_assign(o, t, cz);
    add_assign(o, t, t);
    add_assign(o, t, t);
    add_assign(o, dst, t);
}

pub fn nbody(asteroids: i64, steps: i64) -> Vec<Op> {
    let n = 9 + asteroids;
    let nodes = 3 * n + 64;
    program(|o| {
        isqrt_func(o);

        // newnode(cx, cy, cz, h): a node with no children, into R0
        begin_func(o, "newnode", 3);
        mov(o, &l(0), &g(NODES));
        inc(o, &g(NODES));
        put(o, NCX, &l(0), &arg(0));
        put(o, NCY, &l(0), &arg(1));
        put(o, NCZ, &l(0), &arg(2));
        put(o, NH, &l(0), &arg(3));
        set_int(o, &l(1), -1);
        put(o, NBODY, &l(0), &l(1));
        put(o, NFIRST, &l(0), &l(1));
        mov(o, &l(2), &l(0));
        mul_const(o, &l(2), 8);
        for _ in 0..8 {
            put(o, NCHILD, &l(2), &l(1));
            inc(o, &l(2));
        }
        mov(o, R0, &l(0));
        end_func(o);

        // finish(node, after): the node's mass, centre of mass, first child,
        // and the node after its subtree
        begin_func(o, "finish", 16);
        mov(o, &l(0), &arg(0));
        mov(o, &l(1), &arg(1));
        put(o, NNEXT, &l(0), &l(1));
        get(o, &l(2), NBODY, &l(0));
        mov(o, &l(3), &l(2));
        inc(o, &l(3));
        begin_if(o, &l(3));
        for (from, to) in [(GM, NM), (W, NW), (X, NX), (Y, NY), (Z, NZ)] {
            get(o, &l(4), from, &l(2));
            put(o, to, &l(0), &l(4));
        }
        set_int(o, &l(4), -1);
        put(o, NFIRST, &l(0), &l(4));
        begin_else(o);
        for k in 5..10 {
            set(o, &l(k), 0);
        }
        mov(o, &l(10), &l(1));
        for k in (0..8).rev() {
            mov(o, &l(11), &l(0));
            mul_const(o, &l(11), 8);
            add_const(o, &l(11), k);
            get(o, &l(12), NCHILD, &l(11));
            mov(o, &l(13), &l(12));
            inc(o, &l(13));
            begin_if(o, &l(13));
            call(o, "finish", &[&l(12), &l(10)]);
            get(o, &l(14), NM, &l(12));
            add_assign(o, &l(5), &l(14));
            get(o, &l(14), NW, &l(12));
            add_assign(o, &l(6), &l(14));
            for (from, sum) in [(NX, 7), (NY, 8), (NZ, 9)] {
                get(o, &l(15), from, &l(12));
                mul_assign(o, &l(15), &l(14));
                add_assign(o, &l(sum), &l(15));
            }
            mov(o, &l(10), &l(12));
            end_if(o);
        }
        put(o, NFIRST, &l(0), &l(10));
        put(o, NM, &l(0), &l(5));
        put(o, NW, &l(0), &l(6));
        for (sum, to) in [(7, NX), (8, NY), (9, NZ)] {
            div_assign(o, &l(sum), &l(6));
            put(o, to, &l(0), &l(sum));
        }
        end_if(o);
        end_func(o);

        // build(): the octree of all the bodies
        begin_func(o, "build", 16);
        set(o, &g(NODES), 0);
        set(o, &l(2), 0);
        set_int(o, &l(10), HALF);
        call(o, "newnode", &[&l(2), &l(2), &l(2), &l(10)]);
        set(o, &l(0), 0);
        while_loop(o, R0, |o| { mov(o, R0, &l(0)); lt_assign(o, R0, &g(N)); }, |o| {
            set(o, &l(1), 0);
            begin_loop(o);
            get(o, &l(2), NCX, &l(1));
            get(o, &l(3), NCY, &l(1));
            get(o, &l(4), NCZ, &l(1));
            octant(o, &l(5), &l(11), &l(0), &l(2), &l(3), &l(4));
            mov(o, &l(6), &l(1));
            mul_const(o, &l(6), 8);
            add_assign(o, &l(6), &l(5));
            get(o, &l(7), NCHILD, &l(6));
            // an empty slot: a leaf for the body
            mov(o, &l(8), &l(7));
            inc(o, &l(8));
            lnot_assign(o, &l(8));
            begin_if(o, &l(8));
            call(o, "newnode", &[&l(2), &l(3), &l(4), &l(2)]);
            mov(o, &l(9), R0);
            put(o, NBODY, &l(9), &l(0));
            put(o, NCHILD, &l(6), &l(9));
            break_loop(o);
            end_if(o);
            // a leaf: split it, moving its body down a level, and go on there
            get(o, &l(15), NBODY, &l(7));
            mov(o, &l(8), &l(15));
            inc(o, &l(8));
            begin_if(o, &l(8));
            get(o, &l(10), NH, &l(1));
            rsh_const(o, &l(10), 1);
            mov(o, &l(8), &l(10));
            lnot_assign(o, &l(8));
            break_if(o, &l(8));
            for (axis, (from, to)) in [(2, 12), (3, 13), (4, 14)].into_iter().enumerate() {
                mov(o, &l(11), &l(5));
                if axis > 0 {
                    rsh_const(o, &l(11), axis as i64);
                }
                and_const(o, &l(11), 1);
                add_assign(o, &l(11), &l(11));
                dec(o, &l(11));
                mul_assign(o, &l(11), &l(10));
                mov(o, &l(to), &l(from));
                add_assign(o, &l(to), &l(11));
            }
            call(o, "newnode", &[&l(12), &l(13), &l(14), &l(10)]);
            mov(o, &l(9), R0);
            put(o, NCHILD, &l(6), &l(9));
            octant(o, &l(5), &l(11), &l(15), &l(12), &l(13), &l(14));
            mov(o, &l(6), &l(9));
            mul_const(o, &l(6), 8);
            add_assign(o, &l(6), &l(5));
            put(o, NCHILD, &l(6), &l(7));
            mov(o, &l(1), &l(9));
            begin_else(o);
            mov(o, &l(1), &l(7));
            end_if(o);
            end_loop(o);
            inc(o, &l(0));
        });
        set(o, &l(1), 0);
        set_int(o, &l(2), -1);
        call(o, "finish", &[&l(1), &l(2)]);
        end_func(o);

        // force(i): body i's acceleration
        begin_func(o, "force", 17);
        mov(o, &l(0), &arg(0));
        get(o, &l(1), X, &l(0));
        get(o, &l(2), Y, &l(0));
        get(o, &l(3), Z, &l(0));
        for k in 4..8 {
            set(o, &l(k), 0);
        }
        while_loop(o, R0, |o| { mov(o, R0, &l(7)); inc(o, R0); }, |o| {
            for (d, from, p) in [(8, NX, 1), (9, NY, 2), (10, NZ, 3)] {
                get(o, &l(d), from, &l(7));
                sub_assign(o, &l(d), &l(p));
                rsh_const(o, &l(d), 8);
            }
            mov(o, &l(11), &l(8));
            mul_assign(o, &l(11), &l(8));
            mov(o, &l(12), &l(9));
            mul_assign(o, &l(12), &l(9));
            add_assign(o, &l(11), &l(12));
            mov(o, &l(12), &l(10));
            mul_assign(o, &l(12), &l(10));
            add_assign(o, &l(11), &l(12));
            add_const(o, &l(11), EPS2);
            get(o, &l(16), NH, &l(7));
            rsh_const(o, &l(16), 8);
            mov(o, &l(12), &l(16));
            mul_assign(o, &l(16), &l(12));
            mul_const(o, &l(16), 16);
            // open the node if it has children and is big for how far it is
            get(o, &l(15), NFIRST, &l(7));
            inc(o, &l(15));
            begin_if(o, &l(15));
            mov(o, &l(12), &l(16));
            ge_assign(o, &l(12), &l(11));
            mov(o, &l(15), &l(12));
            end_if(o);
            begin_if(o, &l(15));
            get(o, &l(7), NFIRST, &l(7));
            begin_else(o);
            get(o, &l(12), NBODY, &l(7));
            sub_assign(o, &l(12), &l(0));
            begin_if(o, &l(12));
            get(o, &l(13), NM, &l(7));
            lsh_const(o, &l(13), 16);
            div_assign(o, &l(13), &l(11));
            call(o, "isqrt", &[&l(11)]);
            mov(o, &l(14), R0);
            lsh_const(o, &l(13), 8);
            div_assign(o, &l(13), &l(14));
            for (s, d) in [(4, 8), (5, 9), (6, 10)] {
                mov(o, &l(12), &l(13));
                mul_assign(o, &l(12), &l(d));
                rsh_const(o, &l(12), 8);
                add_assign(o, &l(s), &l(12));
            }
            end_if(o);
            get(o, &l(7), NNEXT, &l(7));
            end_if(o);
        });
        put(o, AX, &l(0), &l(4));
        put(o, AY, &l(0), &l(5));
        put(o, AZ, &l(0), &l(6));
        end_func(o);

        // the globals and the arrays
        heap_alloc_const(o, R9, 32);
        set(o, &g(N), n as u64);
        set(o, R1, n as u64);
        for k in [X, Y, Z, VX, VY, VZ, GM, W, AX, AY, AZ] {
            heap_alloc(o, R2, R1);
            mov(o, &g(k), R2);
        }
        set(o, R1, nodes as u64);
        for k in [NM, NX, NY, NZ, NCX, NCY, NCZ, NH, NFIRST, NNEXT, NBODY, NW] {
            heap_alloc(o, R2, R1);
            mov(o, &g(k), R2);
        }
        heap_alloc_const(o, R2, 8 * nodes);
        mov(o, &g(NCHILD), R2);
        heap_alloc_const(o, R2, 128);
        mov(o, &g(TRIG), R2);
        for (k, (c, s)) in trig().into_iter().enumerate() {
            set(o, R1, 2 * k as u64);
            set_int(o, R2, c);
            put(o, TRIG, R1, R2);
            set(o, R1, 2 * k as u64 + 1);
            set_int(o, R2, s);
            put(o, TRIG, R1, R2);
        }
        for (b, p) in planets().into_iter().enumerate() {
            set(o, R1, b as u64);
            for (k, v) in [GM, X, Y, Z, VX, VY, VZ].into_iter().zip(p) {
                set_int(o, R2, v);
                put(o, k, R1, R2);
            }
            set_int(o, R2, p[0] >> 10);
            put(o, W, R1, R2);
        }
        // the asteroids, on circular orbits at random radii and angles
        set(o, R5, 12345);
        set(o, R1, 9);
        let lcg = |o: &mut dyn Program| {
            mul_const(o, R5, 1_103_515_245);
            add_const(o, R5, 12345);
            and_const(o, R5, 0x7fff_ffff);
        };
        while_loop(o, R0, |o| { mov(o, R0, R1); lt_assign(o, R0, &g(N)); }, |o| {
            lcg(o);
            mov(o, R2, R5);
            and_const(o, R2, 63);
            add_assign(o, R2, R2);
            mov(o, R3, R5);
            rshu_const(o, R3, 6);
            rem_const(o, R3, RANGE);
            add_const(o, R3, RMIN);
            get(o, R4, TRIG, R2);
            mov(o, R6, R3);
            mul_assign(o, R6, R4);
            rsh_const(o, R6, 16);
            put(o, X, R1, R6);
            inc(o, R2);
            get(o, R4, TRIG, R2);
            mov(o, R6, R3);
            mul_assign(o, R6, R4);
            rsh_const(o, R6, 16);
            put(o, Y, R1, R6);
            lcg(o);
            mov(o, R6, R5);
            rem_const(o, R6, ZR);
            sub_const(o, R6, ZR / 2);
            put(o, Z, R1, R6);
            // speed sqrt(GM / r), in Q16
            mov(o, R6, R3);
            rsh_const(o, R6, 8);
            set_int(o, R7, gm_sun() << 20);
            div_assign(o, R7, R6);
            call(o, "isqrt", &[R7]);
            mov(o, R7, R0);
            lsh_const(o, R7, 6);
            get(o, R4, TRIG, R2);
            mov(o, R6, R7);
            mul_assign(o, R6, R4);
            rsh_const(o, R6, 16);
            neg_assign(o, R6);
            put(o, VX, R1, R6);
            dec(o, R2);
            get(o, R4, TRIG, R2);
            mov(o, R6, R7);
            mul_assign(o, R6, R4);
            rsh_const(o, R6, 16);
            put(o, VY, R1, R6);
            set(o, R6, 0);
            put(o, VZ, R1, R6);
            set(o, R6, 1024);
            put(o, GM, R1, R6);
            set(o, R6, 1);
            put(o, W, R1, R6);
            inc(o, R1);
        });

        set(o, R8, 0);
        while_loop(o, R7, |o| { mov(o, R7, R8); lt_const(o, R7, steps); }, |o| {
            call(o, "build", &[]);
            set(o, R1, 0);
            while_loop(o, R0, |o| { mov(o, R0, R1); lt_assign(o, R0, &g(N)); }, |o| {
                call(o, "force", &[R1]);
                inc(o, R1);
            });
            set(o, R1, 0);
            while_loop(o, R0, |o| { mov(o, R0, R1); lt_assign(o, R0, &g(N)); }, |o| {
                for (p, v, a) in [(X, VX, AX), (Y, VY, AY), (Z, VZ, AZ)] {
                    get(o, R2, v, R1);
                    get(o, R3, a, R1);
                    add_assign(o, R2, R3);
                    put(o, v, R1, R2);
                    rsh_const(o, R2, 8);
                    get(o, R3, p, R1);
                    add_assign(o, R3, R2);
                    put(o, p, R1, R3);
                }
                inc(o, R1);
            });
            inc(o, R8);
        });

        // where the Earth is (L), and a checksum of every body's state
        set(o, R1, 3);
        for (k, end) in [(X, " "), (Y, "\n")] {
            get(o, R2, k, R1);
            rsh_const(o, R2, 8);
            putint(o, R2);
            puts(o, end);
        }
        set(o, R3, 0);
        set(o, R1, 0);
        while_loop(o, R0, |o| { mov(o, R0, R1); lt_assign(o, R0, &g(N)); }, |o| {
            for k in [X, Y, Z, VX, VY, VZ] {
                get(o, R2, k, R1);
                add_assign(o, R3, R2);
            }
            inc(o, R1);
        });
        putint(o, R3);
        puts(o, "\n");
    })
}

pub fn nbody_c(asteroids: i64, steps: i64) -> String {
    let n = 9 + asteroids;
    let nodes = 3 * n + 64;
    let mut init = String::new();
    for (k, (c, s)) in trig().into_iter().enumerate() {
        init += &format!("trig[{}] = {c}; trig[{}] = {s};\n", 2 * k, 2 * k + 1);
    }
    for (b, p) in planets().into_iter().enumerate() {
        init += &format!(
            "gm[{b}] = {}; x[{b}] = {}; y[{b}] = {}; z[{b}] = {}; vx[{b}] = {}; vy[{b}] = {}; vz[{b}] = {}; w[{b}] = {};\n",
            p[0],
            p[1],
            p[2],
            p[3],
            p[4],
            p[5],
            p[6],
            p[0] >> 10
        );
    }
    format!(
        r#"#include <stdio.h>
#include <stdint.h>
#define N {n}
#define NODES {nodes}
{ISQRT_C}
static int64_t x[N], y[N], z[N], vx[N], vy[N], vz[N], gm[N], w[N], ax[N], ay[N], az[N];
static int64_t nm[NODES], nx[NODES], ny[NODES], nz[NODES], ncx[NODES], ncy[NODES], ncz[NODES], nh[NODES];
static int64_t nfirst[NODES], nnext[NODES], nbody[NODES], nw[NODES], nchild[8 * NODES], trig[128];
static int64_t count;

static int64_t newnode(int64_t cx, int64_t cy, int64_t cz, int64_t h) {{
    int64_t i = count++;
    ncx[i] = cx; ncy[i] = cy; ncz[i] = cz; nh[i] = h;
    nbody[i] = -1; nfirst[i] = -1;
    for (int k = 0; k < 8; k++) nchild[i * 8 + k] = -1;
    return i;
}}

static int64_t octant(int64_t b, int64_t cx, int64_t cy, int64_t cz) {{
    return (x[b] > cx) + 2 * (y[b] > cy) + 4 * (z[b] > cz);
}}

static void finish(int64_t node, int64_t after) {{
    nnext[node] = after;
    int64_t b = nbody[node];
    if (b != -1) {{
        nm[node] = gm[b]; nw[node] = w[b]; nx[node] = x[b]; ny[node] = y[b]; nz[node] = z[b];
        nfirst[node] = -1;
        return;
    }}
    int64_t m = 0, ws = 0, sx = 0, sy = 0, sz = 0, nxt = after;
    for (int k = 7; k >= 0; k--) {{
        int64_t c = nchild[node * 8 + k];
        if (c != -1) {{
            finish(c, nxt);
            m += nm[c]; ws += nw[c];
            sx += nx[c] * nw[c]; sy += ny[c] * nw[c]; sz += nz[c] * nw[c];
            nxt = c;
        }}
    }}
    nfirst[node] = nxt; nm[node] = m; nw[node] = ws;
    nx[node] = sx / ws; ny[node] = sy / ws; nz[node] = sz / ws;
}}

static void build(void) {{
    count = 0;
    newnode(0, 0, 0, {HALF});
    for (int64_t b = 0; b < N; b++) {{
        int64_t node = 0;
        for (;;) {{
            int64_t cx = ncx[node], cy = ncy[node], cz = ncz[node];
            int64_t oct = octant(b, cx, cy, cz);
            int64_t slot = node * 8 + oct, c = nchild[slot];
            if (c == -1) {{
                int64_t leaf = newnode(cx, cy, cz, cx);
                nbody[leaf] = b; nchild[slot] = leaf;
                break;
            }}
            int64_t ob = nbody[c];
            if (ob != -1) {{
                int64_t h2 = nh[node] >> 1;
                if (h2 == 0) break;
                int64_t c2[3], cc[3] = {{cx, cy, cz}};
                for (int a = 0; a < 3; a++) c2[a] = cc[a] + (2 * ((oct >> a) & 1) - 1) * h2;
                int64_t in = newnode(c2[0], c2[1], c2[2], h2);
                nchild[slot] = in;
                nchild[in * 8 + octant(ob, c2[0], c2[1], c2[2])] = c;
                node = in;
            }} else node = c;
        }}
    }}
    finish(0, -1);
}}

static void force(int64_t i) {{
    int64_t px = x[i], py = y[i], pz = z[i], sx = 0, sy = 0, sz = 0, node = 0;
    while (node != -1) {{
        int64_t dx = (nx[node] - px) >> 8, dy = (ny[node] - py) >> 8, dz = (nz[node] - pz) >> 8;
        int64_t r2 = dx * dx + dy * dy + dz * dz + {EPS2};
        int64_t h = nh[node] >> 8;
        h = h * h * 16;
        int64_t open = nfirst[node] + 1;
        if (open) open = h >= r2;
        if (open) node = nfirst[node];
        else {{
            if (nbody[node] != i) {{
                int64_t f = (nm[node] << 16) / r2;
                int64_t r = isqrt(r2);
                f = (f << 8) / r;
                sx += (f * dx) >> 8; sy += (f * dy) >> 8; sz += (f * dz) >> 8;
            }}
            node = nnext[node];
        }}
    }}
    ax[i] = sx; ay[i] = sy; az[i] = sz;
}}

int main(void) {{
{init}
    int64_t seed = 12345;
#define LCG() (seed = (seed * 1103515245 + 12345) & 0x7fffffff)
    for (int64_t i = 9; i < N; i++) {{
        LCG();
        int64_t k = (seed & 63) * 2;
        int64_t r = ((int64_t)((uint64_t)seed >> 6)) % {RANGE} + {RMIN};
        x[i] = (r * trig[k]) >> 16;
        y[i] = (r * trig[k + 1]) >> 16;
        LCG();
        z[i] = seed % {ZR} - {ZR} / 2;
        int64_t v = isqrt(({gm_sun}ll << 20) / (r >> 8)) << 6;
        vx[i] = -((v * trig[k + 1]) >> 16);
        vy[i] = (v * trig[k]) >> 16;
        vz[i] = 0; gm[i] = 1024; w[i] = 1;
    }}
    for (int s = 0; s < {steps}; s++) {{
        build();
        for (int64_t i = 0; i < N; i++) force(i);
        for (int64_t i = 0; i < N; i++) {{
            vx[i] += ax[i]; x[i] += vx[i] >> 8;
            vy[i] += ay[i]; y[i] += vy[i] >> 8;
            vz[i] += az[i]; z[i] += vz[i] >> 8;
        }}
    }}
    printf("%lld %lld\n", (long long)(x[3] >> 8), (long long)(y[3] >> 8));
    int64_t sum = 0;
    for (int64_t i = 0; i < N; i++) sum += x[i] + y[i] + z[i] + vx[i] + vy[i] + vz[i];
    printf("%lld\n", (long long)sum);
    return 0;
}}
"#,
        gm_sun = gm_sun()
    )
}

#[test]
fn nbody_prints_what_c_does() {
    check("nbody", &nbody(1000, 60), &nbody_c(1000, 60));
}
