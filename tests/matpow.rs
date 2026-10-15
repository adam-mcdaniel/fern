//! 2x2 matrices to the power 2^30 + k, modulo 1000000007, by squaring, for
//! 20000 different matrices (31 squarings each); prints the sum of their
//! corners.

mod common;

use bf::asm::*;
use common::*;

const P: i64 = 1_000_000_007;
const N: i64 = 20_000;

#[test]
fn matpow_prints_what_c_does() {
    let ops = program(|o| {
        // matpow(a, b, c, d, e): the top-left corner plus the bottom-right of
        // [[a, b], [c, d]]^e, into R0 (uses R1 to R4)
        begin_func(o, "matpow", 9);
        let (a, b, c, d, e, ra, rb, rc, rd) = (l(0), l(1), l(2), l(3), l(4), l(5), l(6), l(7), l(8));
        for (k, x) in [&a, &b, &c, &d, &e].into_iter().enumerate() {
            mov(o, x, &arg(k as i64));
        }
        set(o, &ra, 1);
        set(o, &rb, 0);
        set(o, &rc, 0);
        set(o, &rd, 1);
        // [[w, x], [y, z]] = [[w, x], [y, z]] * [[p, q], [r, s]] (mod P)
        let mul = |o: &mut dyn Program, m: [&Location; 4], n: [&Location; 4]| {
            let [w, x, y, z] = m;
            let [p, q, r, s] = n;
            for (dst, (u1, v1), (u2, v2)) in [(R1, (w, p), (x, r)), (R2, (w, q), (x, s)), (R3, (y, p), (z, r)), (R4, (y, q), (z, s))] {
                mov(o, dst, u1);
                mul_assign(o, dst, v1);
                rem_const(o, dst, P);
                mov(o, R0, u2);
                mul_assign(o, R0, v2);
                rem_const(o, R0, P);
                add_assign(o, dst, R0);
                rem_const(o, dst, P);
            }
            mov(o, w, R1);
            mov(o, x, R2);
            mov(o, y, R3);
            mov(o, z, R4);
        };
        while_loop(o, R1, |o| mov(o, R1, &e), |o| {
            mov(o, R1, &e);
            and_const(o, R1, 1);
            begin_if(o, R1);
            mul(o, [&ra, &rb, &rc, &rd], [&a, &b, &c, &d]);
            end_if(o);
            // (squaring: a copy of the matrix as the right side)
            push(o, &a);
            push(o, &b);
            push(o, &c);
            push(o, &d);
            let (pa, pb, pc, pd) = (SP.deref().offset(-4), SP.deref().offset(-3), SP.deref().offset(-2), SP.deref().offset(-1));
            mul(o, [&a, &b, &c, &d], [&pa, &pb, &pc, &pd]);
            pop(o, R1);
            pop(o, R1);
            pop(o, R1);
            pop(o, R1);
            rsh_const(o, &e, 1);
        });
        mov(o, R0, &ra);
        add_assign(o, R0, &rd);
        end_func(o);

        let (k, a, b, c, d, e, sum) = (R5, R6, R7, R8, R9, R2, R3);
        set(o, sum, 0);
        push(o, sum);
        for_const(o, k, 0, N, R0, |o| {
            mov(o, a, k);
            add_const(o, a, 2);
            mov(o, b, k);
            mul_const(o, b, 7);
            inc(o, b);
            mov(o, c, k);
            mul_const(o, c, 13);
            add_const(o, c, 5);
            mov(o, d, k);
            mul_assign(o, d, k);
            rem_const(o, d, P);
            mov(o, e, k);
            add_const(o, e, 1 << 30);
            call(o, "matpow", &[a, b, c, d, e]);
            add_assign(o, &SP.deref().offset(-1), R0);
        });
        pop(o, sum);
        putint(o, sum);
        puts(o, "\n");
    });
    let c = format!(
        r#"{C_HEAD}
#define P {P}
static void mul(int64_t m[4], const int64_t n[4]) {{
    int64_t w = (m[0] * n[0] % P + m[1] * n[2] % P) % P;
    int64_t x = (m[0] * n[1] % P + m[1] * n[3] % P) % P;
    int64_t y = (m[2] * n[0] % P + m[3] * n[2] % P) % P;
    int64_t z = (m[2] * n[1] % P + m[3] * n[3] % P) % P;
    m[0] = w; m[1] = x; m[2] = y; m[3] = z;
}}
int main(void) {{
    int64_t sum = 0;
    for (int64_t k = 0; k < {N}; k++) {{
        int64_t m[4] = {{k + 2, k * 7 + 1, k * 13 + 5, k * k % P}}, r[4] = {{1, 0, 0, 1}};
        for (int64_t e = k + (1 << 30); e; e >>= 1) {{
            if (e & 1) mul(r, m);
            int64_t copy[4] = {{m[0], m[1], m[2], m[3]}};
            mul(m, copy);
        }}
        sum += r[0] + r[3];
    }}
    printf("%lld\n", (long long)sum);
}}
"#
    );
    check("matpow", &ops, &c);
}
