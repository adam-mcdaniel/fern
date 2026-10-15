//! 1500! in base 10000, a limb at a time (each carrying into the next);
//! prints how many limbs it takes and their sum.

mod common;

use bf::asm::*;
use common::*;

const K: i64 = 1500;
const LIMBS: i64 = 1200;

#[test]
fn bigfact_prints_what_c_does() {
    let ops = program(|o| {
        let (a, len, k, i, t, carry) = (R1, R2, R3, R4, R5, R6);
        heap_alloc_const(o, a, LIMBS);
        set(o, t, 0);
        for_const(o, i, 0, LIMBS, R0, |o| store_index(o, a, i, t));
        set(o, t, 1);
        set(o, i, 0);
        store_index(o, a, i, t);
        set(o, len, 1);
        for_const(o, k, 2, K + 1, R0, |o| {
            set(o, carry, 0);
            for_range(o, i, 0, len, R0, |o| {
                load_index(o, t, a, i);
                mul_assign(o, t, k);
                add_assign(o, t, carry);
                mov(o, carry, t);
                div_const(o, carry, 10_000);
                rem_const(o, t, 10_000);
                store_index(o, a, i, t);
            });
            while_loop(o, R0, |o| mov(o, R0, carry), |o| {
                mov(o, t, carry);
                rem_const(o, t, 10_000);
                store_index(o, a, len, t);
                inc(o, len);
                div_const(o, carry, 10_000);
            });
        });
        set(o, t, 0);
        for_range(o, i, 0, len, R0, |o| {
            load_index(o, carry, a, i);
            add_assign(o, t, carry);
        });
        putint(o, len);
        puts(o, " ");
        putint(o, t);
        puts(o, "\n");
    });
    let c = format!(
        r#"{C_HEAD}
static int64_t a[{LIMBS}];
int main(void) {{
    int64_t len = 1;
    a[0] = 1;
    for (int64_t k = 2; k <= {K}; k++) {{
        int64_t carry = 0;
        for (int64_t i = 0; i < len; i++) {{ int64_t t = a[i] * k + carry; carry = t / 10000; a[i] = t % 10000; }}
        while (carry) {{ a[len++] = carry % 10000; carry /= 10000; }}
    }}
    int64_t sum = 0;
    for (int64_t i = 0; i < len; i++) sum += a[i];
    printf("%lld %lld\n", (long long)len, (long long)sum);
}}
"#
    );
    check("bigfact", &ops, &c);
}
