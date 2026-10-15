//! The product of two polynomials of degree 3000, modulo 998244353, a
//! coefficient at a time (each a sum over as many terms as it has).

mod common;

use bf::asm::*;
use common::*;

const N: i64 = 3000;
const P: i64 = 998_244_353;

#[test]
fn polymul_prints_what_c_does() {
    let ops = program(|o| {
        let (a, b, c, k, i, lo, hi, s, t) = (R1, R2, R3, R4, R5, R6, R7, R8, R9);
        heap_alloc_const(o, a, N);
        heap_alloc_const(o, b, N);
        heap_alloc_const(o, c, 2 * N - 1);
        for_const(o, i, 0, N, R0, |o| {
            mov(o, t, i);
            mul_assign(o, t, t);
            add_const(o, t, 7);
            rem_const(o, t, 1000);
            store_index(o, a, i, t);
            mov(o, t, i);
            mul_const(o, t, 31);
            add_const(o, t, 3);
            rem_const(o, t, 997);
            store_index(o, b, i, t);
        });
        for_const(o, k, 0, 2 * N - 1, R0, |o| {
            // c[k] = sum of a[i] b[k - i], for i from max(0, k - N + 1) to min(k, N - 1)
            mov(o, lo, k);
            sub_const(o, lo, N - 1);
            set(o, t, 0);
            max_assign(o, lo, t);
            mov(o, hi, k);
            set(o, t, (N - 1) as u64);
            min_assign(o, hi, t);
            set(o, s, 0);
            mov(o, i, lo);
            while_loop(o, R0, |o| { mov(o, R0, i); le_assign(o, R0, hi); }, |o| {
                load_index(o, t, a, i);
                mov(o, R0, k);
                sub_assign(o, R0, i);
                load_index(o, R0, b, R0);
                mul_assign(o, t, R0);
                add_assign(o, s, t);
                inc(o, i);
            });
            rem_const(o, s, P);
            store_index(o, c, k, s);
        });
        set(o, s, 0);
        for_const(o, k, 0, 2 * N - 1, R0, |o| {
            load_index(o, t, c, k);
            mov(o, i, k);
            rem_const(o, i, 13);
            inc(o, i);
            mul_assign(o, t, i);
            add_assign(o, s, t);
        });
        putint(o, s);
        puts(o, "\n");
    });
    let c = format!(
        r#"{C_HEAD}
#define N {N}
static int64_t a[N], b[N], c[2 * N - 1];
int main(void) {{
    for (int64_t i = 0; i < N; i++) {{ a[i] = (i * i + 7) % 1000; b[i] = (i * 31 + 3) % 997; }}
    for (int64_t k = 0; k < 2 * N - 1; k++) {{
        int64_t lo = k - (N - 1) > 0 ? k - (N - 1) : 0, hi = k < N - 1 ? k : N - 1, s = 0;
        for (int64_t i = lo; i <= hi; i++) s += a[i] * b[k - i];
        c[k] = s % {P};
    }}
    int64_t sum = 0;
    for (int64_t k = 0; k < 2 * N - 1; k++) sum += c[k] * (k % 13 + 1);
    printf("%lld\n", (long long)sum);
}}
"#
    );
    check("polymul", &ops, &c);
}
