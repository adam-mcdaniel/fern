//! The primes up to 90000, counted with Eratosthenes' sieve.

mod common;

use bf::asm::*;
use common::*;

const N: i64 = 90_000;

#[test]
fn sieve_prints_what_c_does() {
    let ops = program(|o| {
        let (n, sieve, i, t, j, flag) = (R1, R2, R3, R4, R5, R6);
        set(o, n, N as u64);
        mov(o, t, n);
        inc(o, t);
        heap_alloc(o, sieve, t);
        set(o, i, 0);
        set(o, t, 0);
        while_loop(o, flag, |o| { mov(o, flag, i); le_assign(o, flag, n); }, |o| {
            store_index(o, sieve, i, t);
            inc(o, i);
        });
        set(o, i, 1);
        begin_loop(o);
        inc(o, i);
        mov(o, t, i);
        mul_assign(o, t, i);
        gt_assign(o, t, n);
        break_if(o, t);
        load_index(o, t, sieve, i);
        begin_if(o, t);
        continue_loop(o);
        end_if(o);
        mov(o, j, i);
        mul_assign(o, j, i);
        set(o, t, 1);
        while_loop(o, flag, |o| { mov(o, flag, j); le_assign(o, flag, n); }, |o| {
            store_index(o, sieve, j, t);
            add_assign(o, j, i);
        });
        end_loop(o);
        set(o, i, 2);
        set(o, j, 0);
        while_loop(o, flag, |o| { mov(o, flag, i); le_assign(o, flag, n); }, |o| {
            load_index(o, t, sieve, i);
            lnot_assign(o, t);
            add_assign(o, j, t);
            inc(o, i);
        });
        putint(o, j);
        puts(o, " primes\n");
    });
    let c = format!(
        r#"{C_HEAD}
static int64_t s[{N} + 1];
int main(void) {{
    for (int64_t i = 2; i * i <= {N}; i++)
        if (!s[i])
            for (int64_t j = i * i; j <= {N}; j += i) s[j] = 1;
    int64_t count = 0;
    for (int64_t i = 2; i <= {N}; i++) count += !s[i];
    printf("%lld primes\n", (long long)count);
}}
"#
    );
    check("sieve", &ops, &c);
}
