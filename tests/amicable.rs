//! The sum of the proper divisors of every number up to 60000 (trial
//! division up to the square root, a different count for each), then the
//! amicable pairs among them.

mod common;

use bf::asm::*;
use common::*;

const N: i64 = 60_000;

#[test]
fn amicable_prints_what_c_does() {
    let ops = program(|o| {
        let (s, n, sum, d, t, e, count, total) = (R1, R2, R3, R4, R5, R6, R7, R8);
        heap_alloc_const(o, s, N + 1);
        set(o, t, 0);
        store_index(o, s, t, t);
        for_const(o, n, 1, N + 1, R0, |o| {
            mov(o, sum, n);
            gt_const(o, sum, 1);
            set(o, d, 2);
            while_loop(o, R9, |o| { mov(o, R9, d); mul_assign(o, R9, d); le_assign(o, R9, n); }, |o| {
                mov(o, t, n);
                rem_assign(o, t, d);
                eq_const(o, t, 0);
                begin_if(o, t);
                add_assign(o, sum, d);
                mov(o, e, n);
                div_assign(o, e, d);
                mov(o, t, e);
                ne_assign(o, t, d);
                begin_if(o, t);
                add_assign(o, sum, e);
                end_if(o);
                end_if(o);
                inc(o, d);
            });
            store_index(o, s, n, sum);
        });
        set(o, count, 0);
        set(o, total, 0);
        for_const(o, n, 2, N + 1, R0, |o| {
            load_index(o, d, s, n);
            mov(o, t, d);
            le_const(o, t, N);
            mov(o, e, d);
            ne_assign(o, e, n);
            land_assign(o, t, e);
            begin_if(o, t);
            load_index(o, e, s, d);
            eq_assign(o, e, n);
            begin_if(o, e);
            inc(o, count);
            add_assign(o, total, n);
            end_if(o);
            end_if(o);
        });
        putint(o, count);
        puts(o, " ");
        putint(o, total);
        puts(o, "\n");
    });
    let c = format!(
        r#"{C_HEAD}
#define N {N}
static int64_t s[N + 1];
int main(void) {{
    for (int64_t n = 1; n <= N; n++) {{
        int64_t sum = n > 1;
        for (int64_t d = 2; d * d <= n; d++)
            if (n % d == 0) {{ sum += d; int64_t e = n / d; if (e != d) sum += e; }}
        s[n] = sum;
    }}
    int64_t count = 0, total = 0;
    for (int64_t n = 2; n <= N; n++) {{
        int64_t m = s[n];
        if (m <= N && m != n && s[m] == n) {{ count++; total += n; }}
    }}
    printf("%lld %lld\n", (long long)count, (long long)total);
}}
"#
    );
    check("amicable", &ops, &c);
}
