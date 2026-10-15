//! Polynomial multiplication by the number-theoretic transform mod
//! 998244353: two random polynomials of 4096 terms, transformed (bit
//! reversal, then butterflies), multiplied pointwise and transformed back,
//! 30 times.

mod common;

use bf::asm::*;
use common::*;

const P: i64 = 998_244_353;
const N: i64 = 8192;
const ROUNDS: i64 = 30;
// the globals
const A: i64 = 0;
const B: i64 = 1;
const RF: i64 = 2;
const RI: i64 = 3;
const ROUND: i64 = 4;
const SUM: i64 = 5;
const NINV: i64 = 6;
const FLAG: i64 = 7;

#[test]
fn ntt_prints_what_c_does() {
    let ops = program(|o| {
        // powmod(b, e), into R0 (uses R1)
        begin_func(o, "powmod", 3);
        let (base, e, r) = (l(0), l(1), l(2));
        mov(o, &base, &arg(0));
        rem_const(o, &base, P);
        mov(o, &e, &arg(1));
        set(o, &r, 1);
        while_loop(o, R1, |o| mov(o, R1, &e), |o| {
            mov(o, R1, &e);
            and_const(o, R1, 1);
            begin_if(o, R1);
            mul_assign(o, &r, &base);
            rem_const(o, &r, P);
            end_if(o);
            mul_assign(o, &base, &base);
            rem_const(o, &base, P);
            rsh_const(o, &e, 1);
        });
        mov(o, R0, &r);
        end_func(o);

        // ntt(a, roots), in place (uses R0 to R8)
        begin_func(o, "ntt", 5);
        let (len, step, blk, f1, f2) = (l(0), l(1), l(2), l(3), l(4));
        let (a, roots, j, at, u, v, w, x) = (R1, R2, R3, R4, R5, R6, R7, R8);
        mov(o, a, &arg(0));
        mov(o, roots, &arg(1));
        // bit reversal (i in j, j in at, the bit in u)
        set(o, at, 0);
        for_const(o, j, 1, N, R0, |o| {
            set_int(o, u, N / 2);
            while_loop(o, v, |o| { mov(o, v, at); and_assign(o, v, u); }, |o| {
                xor_assign(o, at, u);
                rsh_const(o, u, 1);
            });
            xor_assign(o, at, u);
            mov(o, v, j);
            lt_assign(o, v, at);
            begin_if(o, v);
            load_index(o, w, a, j);
            load_index(o, x, a, at);
            store_index(o, a, j, x);
            store_index(o, a, at, w);
            end_if(o);
        });
        set(o, &len, 1);
        set_int(o, &step, N / 2);
        while_loop(o, &f1, |o| { mov(o, &f1, &len); lt_const(o, &f1, N); }, |o| {
            set(o, &blk, 0);
            while_loop(o, &f2, |o| { mov(o, &f2, &blk); lt_const(o, &f2, N); }, |o| {
                for_range(o, j, 0, &len, R0, |o| {
                    mov(o, w, j);
                    mul_assign(o, w, &step);
                    load_index(o, w, roots, w);
                    mov(o, at, &blk);
                    add_assign(o, at, j);
                    load_index(o, u, a, at);
                    add_assign(o, at, &len);
                    load_index(o, v, a, at);
                    mul_assign(o, v, w);
                    rem_const(o, v, P);
                    mov(o, w, u);
                    sub_assign(o, w, v);
                    mov(o, R0, w);
                    lt_const(o, R0, 0);
                    begin_if(o, R0);
                    add_const(o, w, P);
                    end_if(o);
                    store_index(o, a, at, w);
                    sub_assign(o, at, &len);
                    mov(o, x, u);
                    add_assign(o, x, v);
                    mov(o, R0, x);
                    ge_const(o, R0, P);
                    begin_if(o, R0);
                    sub_const(o, x, P);
                    end_if(o);
                    store_index(o, a, at, x);
                });
                add_assign(o, &blk, &len);
                add_assign(o, &blk, &len);
            });
            lsh_const(o, &len, 1);
            rsh_const(o, &step, 1);
        });
        end_func(o);

        let (i, t, s, seed, w) = (R1, R2, R3, R4, R5);
        heap_alloc_const(o, R9, 8);
        for (array, n) in [(A, N), (B, N), (RF, N / 2), (RI, N / 2)] {
            heap_alloc_const(o, t, n);
            mov(o, &g(array), t);
        }
        // the roots of unity, and their inverses
        set(o, t, 3);
        set_int(o, s, (P - 1) / N);
        call(o, "powmod", &[t, s]);
        mov(o, w, R0);
        set_int(o, s, P - 2);
        call(o, "powmod", &[w, s]);
        push(o, R0);
        for array in [RF, RI] {
            if array == RI {
                pop(o, w);
            }
            set(o, t, 1);
            for_const(o, i, 0, N / 2, R0, |o| {
                put(o, array, i, t);
                mul_assign(o, t, w);
                rem_const(o, t, P);
            });
        }
        set_int(o, t, N);
        set_int(o, s, P - 2);
        call(o, "powmod", &[t, s]);
        mov(o, &g(NINV), R0);
        set(o, seed, 3);
        set(o, &g(SUM), 0);
        for_const(o, &g(ROUND), 0, ROUNDS, &g(FLAG), |o| {
            for array in [A, B] {
                for_const(o, i, 0, N, R0, |o| {
                    set(o, t, 0);
                    mov(o, s, i);
                    lt_const(o, s, N / 2);
                    begin_if(o, s);
                    lcg(o, seed);
                    mov(o, t, seed);
                    rem_const(o, t, P);
                    end_if(o);
                    put(o, array, i, t);
                });
            }
            push(o, seed);
            call(o, "ntt", &[&g(A), &g(RF)]);
            call(o, "ntt", &[&g(B), &g(RF)]);
            for_const(o, i, 0, N, R0, |o| {
                get(o, t, A, i);
                get(o, s, B, i);
                mul_assign(o, t, s);
                rem_const(o, t, P);
                put(o, A, i, t);
            });
            call(o, "ntt", &[&g(A), &g(RI)]);
            pop(o, seed);
            for_const(o, i, 0, N, R0, |o| {
                get(o, t, A, i);
                mul_assign(o, t, &g(NINV));
                rem_const(o, t, P);
                put(o, A, i, t);
                add_assign(o, &g(SUM), t);
            });
        });
        putint(o, &g(SUM));
        puts(o, " ");
        set(o, i, 100);
        get(o, t, A, i);
        putint(o, t);
        puts(o, "\n");
    });
    let c = format!(
        r#"{C_HEAD}{LCG_C}
#define P {P}
#define N {N}
static int64_t a[N], b[N], rf[N / 2], ri[N / 2];
static int64_t powmod(int64_t b, int64_t e) {{
    int64_t r = 1;
    b %= P;
    while (e) {{ if (e & 1) r = r * b % P; b = b * b % P; e >>= 1; }}
    return r;
}}
static void ntt(int64_t *a, const int64_t *roots) {{
    for (int64_t i = 1, j = 0; i < N; i++) {{
        int64_t bit = N / 2;
        while (j & bit) {{ j ^= bit; bit >>= 1; }}
        j ^= bit;
        if (i < j) {{ int64_t t = a[i]; a[i] = a[j]; a[j] = t; }}
    }}
    for (int64_t len = 1, step = N / 2; len < N; len <<= 1, step >>= 1)
        for (int64_t blk = 0; blk < N; blk += 2 * len)
            for (int64_t j = 0; j < len; j++) {{
                int64_t u = a[blk + j], v = a[blk + j + len] * roots[j * step] % P;
                int64_t x = u - v; if (x < 0) x += P; a[blk + j + len] = x;
                x = u + v; if (x >= P) x -= P; a[blk + j] = x;
            }}
}}
int main(void) {{
    int64_t w = powmod(3, (P - 1) / N), wi = powmod(w, P - 2);
    for (int64_t i = 0, t = 1; i < N / 2; i++) {{ rf[i] = t; t = t * w % P; }}
    for (int64_t i = 0, t = 1; i < N / 2; i++) {{ ri[i] = t; t = t * wi % P; }}
    int64_t ninv = powmod(N, P - 2), seed = 3, sum = 0;
    for (int round = 0; round < {ROUNDS}; round++) {{
        for (int64_t i = 0; i < N; i++) {{ a[i] = 0; if (i < N / 2) {{ LCG(seed); a[i] = seed % P; }} }}
        for (int64_t i = 0; i < N; i++) {{ b[i] = 0; if (i < N / 2) {{ LCG(seed); b[i] = seed % P; }} }}
        ntt(a, rf); ntt(b, rf);
        for (int64_t i = 0; i < N; i++) a[i] = a[i] * b[i] % P;
        ntt(a, ri);
        for (int64_t i = 0; i < N; i++) {{ a[i] = a[i] * ninv % P; sum += a[i]; }}
    }}
    printf("%lld %lld\n", (long long)sum, (long long)a[100]);
}}
"#
    );
    check("ntt", &ops, &c);
}
