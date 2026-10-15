//! How many numbers below 1000000 are prime, each by trial division up to its
//! square root.

mod common;

use bf::asm::*;
use common::*;

const N: i64 = 1_000_000;

#[test]
fn primes_prints_what_c_does() {
    let ops = program(|o| {
        let (n, d, prime, t, count) = (R1, R2, R3, R4, R5);
        set(o, count, 0);
        for_const(o, n, 2, N, R6, |o| {
            set(o, prime, 1);
            set(o, d, 2);
            begin_loop(o);
            mov(o, t, d);
            mul_assign(o, t, d);
            gt_assign(o, t, n);
            break_if(o, t);
            mov(o, t, n);
            rem_assign(o, t, d);
            lnot_assign(o, t);
            begin_if(o, t);
            set(o, prime, 0);
            break_loop(o);
            end_if(o);
            inc(o, d);
            end_loop(o);
            add_assign(o, count, prime);
        });
        putint(o, count);
        puts(o, "\n");
    });
    let c = format!(
        r#"{C_HEAD}
int main(void) {{
    int64_t count = 0;
    for (int64_t n = 2; n < {N}; n++) {{
        int64_t prime = 1;
        for (int64_t d = 2; d * d <= n; d++) if (n % d == 0) {{ prime = 0; break; }}
        count += prime;
    }}
    printf("%lld\n", (long long)count);
}}
"#
    );
    check("primes", &ops, &c);
}
