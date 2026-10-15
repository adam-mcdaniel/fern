//! Goldbach partitions: a sieve up to 20000, then for each even number up
//! to it, how many ways it is a sum of two primes (a loop to half of it);
//! prints the total and the number with the most.

mod common;

use bf::asm::*;
use common::*;

const M: i64 = 20_000;

#[test]
fn goldbach_prints_what_c_does() {
    let ops = program(|o| {
        let (isp, i, j, t, n, c, total, best, at) = (R1, R2, R3, R4, R5, R6, R7, R8, R9);
        heap_alloc_const(o, isp, M + 1);
        for_const(o, i, 0, M + 1, R0, |o| {
            mov(o, t, i);
            ge_const(o, t, 2);
            store_index(o, isp, i, t);
        });
        set(o, i, 2);
        while_loop(o, R0, |o| { mov(o, R0, i); mul_assign(o, R0, i); le_const(o, R0, M); }, |o| {
            load_index(o, t, isp, i);
            begin_if(o, t);
            mov(o, j, i);
            mul_assign(o, j, i);
            set(o, t, 0);
            while_loop(o, R0, |o| { mov(o, R0, j); le_const(o, R0, M); }, |o| {
                store_index(o, isp, j, t);
                add_assign(o, j, i);
            });
            end_if(o);
            inc(o, i);
        });
        set(o, total, 0);
        set(o, best, 0);
        set(o, at, 0);
        set(o, n, 4);
        while_loop(o, R0, |o| { mov(o, R0, n); le_const(o, R0, M); }, |o| {
            set(o, c, 0);
            set(o, i, 2);
            while_loop(o, R0, |o| { mov(o, R0, i); add_assign(o, R0, i); le_assign(o, R0, n); }, |o| {
                load_index(o, t, isp, i);
                mov(o, j, n);
                sub_assign(o, j, i);
                load_index(o, j, isp, j);
                mul_assign(o, t, j);
                add_assign(o, c, t);
                inc(o, i);
            });
            add_assign(o, total, c);
            mov(o, t, c);
            gt_assign(o, t, best);
            begin_if(o, t);
            mov(o, best, c);
            mov(o, at, n);
            end_if(o);
            add_const(o, n, 2);
        });
        putint(o, total);
        puts(o, " ");
        putint(o, at);
        puts(o, " ");
        putint(o, best);
        puts(o, "\n");
    });
    let c = format!(
        r#"{C_HEAD}
#define M {M}
static int64_t isp[M + 1];
int main(void) {{
    for (int64_t i = 0; i <= M; i++) isp[i] = i >= 2;
    for (int64_t i = 2; i * i <= M; i++)
        if (isp[i])
            for (int64_t j = i * i; j <= M; j += i) isp[j] = 0;
    int64_t total = 0, best = 0, at = 0;
    for (int64_t n = 4; n <= M; n += 2) {{
        int64_t c = 0;
        for (int64_t i = 2; i + i <= n; i++) c += isp[i] * isp[n - i];
        total += c;
        if (c > best) {{ best = c; at = n; }}
    }}
    printf("%lld %lld %lld\n", (long long)total, (long long)at, (long long)best);
}}
"#
    );
    check("goldbach", &ops, &c);
}
