//! Digit sums of the numbers below 80000, through a function, and their
//! total.

mod common;

use bf::asm::*;
use common::*;

const N: i64 = 80_000;

#[test]
fn digits_prints_what_c_does() {
    let ops = program(|o| {
        let (n, a, i, t, sum, flag) = (R1, R2, R3, R4, R5, R6);
        begin_func(o, "digitsum", 2);
        mov(o, &l(0), &arg(0));
        set(o, &l(1), 0);
        while_loop(o, R7, |o| mov(o, R7, &l(0)), |o| {
            mov(o, R8, &l(0));
            rem_const(o, R8, 10);
            add_assign(o, &l(1), R8);
            div_const(o, &l(0), 10);
        });
        mov(o, R0, &l(1));
        ret(o);
        end_func(o);
        set(o, n, N as u64);
        heap_alloc(o, a, n);
        for_range(o, i, 0, n, flag, |o| {
            call(o, "digitsum", &[i]);
            store_index(o, a, i, R0);
        });
        set(o, sum, 0);
        for_range(o, i, 0, n, flag, |o| {
            load_index(o, t, a, i);
            add_assign(o, sum, t);
        });
        putint(o, sum);
        puts(o, "\n");
    });
    let c = format!(
        r#"{C_HEAD}
static int64_t a[{N}];
static int64_t digitsum(int64_t x) {{
    int64_t s = 0;
    while (x) {{ s += x % 10; x /= 10; }}
    return s;
}}
int main(void) {{
    for (int64_t i = 0; i < {N}; i++) a[i] = digitsum(i);
    int64_t sum = 0;
    for (int64_t i = 0; i < {N}; i++) sum += a[i];
    printf("%lld\n", (long long)sum);
}}
"#
    );
    check("digits", &ops, &c);
}
