//! The determinant of a 60 by 60 matrix modulo 1000003, by Gaussian
//! elimination (each pivot's row updates are independent of each other),
//! with inverses by Fermat's little theorem.

mod common;

use bf::asm::*;
use common::*;

const N: i64 = 60;
const P: i64 = 1_000_003;

#[test]
fn gauss_prints_what_c_does() {
    let ops = program(|o| {
        // modinv(a): a^(P - 2) mod P, into R0
        begin_func(o, "modinv", 3);
        mov(o, &l(0), &arg(0));
        set(o, &l(1), 1);
        set_int(o, &l(2), P - 2);
        while_loop(o, R0, |o| mov(o, R0, &l(2)), |o| {
            mov(o, R0, &l(2));
            and_const(o, R0, 1);
            begin_if(o, R0);
            mul_assign(o, &l(1), &l(0));
            rem_const(o, &l(1), P);
            end_if(o);
            mul_assign(o, &l(0), &l(0));
            rem_const(o, &l(0), P);
            rshu_const(o, &l(2), 1);
        });
        mov(o, R0, &l(1));
        end_func(o);

        let (a, c, r, j, f, t, u, det) = (R1, R2, R3, R4, R5, R6, R7, R8);
        heap_alloc_const(o, a, N * N);
        // random entries
        set(o, det, 77);
        for_const(o, r, 0, N * N, R0, |o| {
            lcg(o, det);
            mov(o, t, det);
            rshu_const(o, t, 4);
            rem_const(o, t, P);
            store_index(o, a, r, t);
        });
        set(o, det, 1);
        for_const(o, c, 0, N, R9, |o| {
            // a row from c down with something in column c
            mov(o, r, c);
            begin_loop(o);
            mov(o, t, r);
            mul_const(o, t, N);
            add_assign(o, t, c);
            load_index(o, t, a, t);
            break_if(o, t);
            inc(o, r);
            end_loop(o);
            mov(o, t, r);
            ne_assign(o, t, c);
            begin_if(o, t);
            // swap it up
            for_const(o, j, 0, N, R0, |o| {
                mov(o, t, r);
                mul_const(o, t, N);
                add_assign(o, t, j);
                load_index(o, f, a, t);
                mov(o, u, c);
                mul_const(o, u, N);
                add_assign(o, u, j);
                load_index(o, R0, a, u);
                store_index(o, a, t, R0);
                store_index(o, a, u, f);
            });
            neg_assign(o, det);
            add_const(o, det, P);
            rem_const(o, det, P);
            end_if(o);
            mov(o, t, c);
            mul_const(o, t, N);
            add_assign(o, t, c);
            load_index(o, t, a, t);
            mul_assign(o, det, t);
            rem_const(o, det, P);
            call(o, "modinv", &[t]);
            mov(o, f, R0);
            push(o, f);
            // take the pivot's row out of the rows below
            mov(o, r, c);
            inc(o, r);
            while_loop(o, R0, |o| { mov(o, R0, r); lt_const(o, R0, N); }, |o| {
                pop(o, f);
                push(o, f);
                mov(o, t, r);
                mul_const(o, t, N);
                add_assign(o, t, c);
                load_index(o, t, a, t);
                mul_assign(o, f, t);
                rem_const(o, f, P);
                for_const(o, j, 0, N, R0, |o| {
                    mov(o, t, c);
                    mul_const(o, t, N);
                    add_assign(o, t, j);
                    load_index(o, t, a, t);
                    mul_assign(o, t, f);
                    rem_const(o, t, P);
                    mov(o, u, r);
                    mul_const(o, u, N);
                    add_assign(o, u, j);
                    load_index(o, u, a, u);
                    sub_assign(o, u, t);
                    add_const(o, u, P);
                    rem_const(o, u, P);
                    mov(o, t, r);
                    mul_const(o, t, N);
                    add_assign(o, t, j);
                    store_index(o, a, t, u);
                });
                inc(o, r);
            });
            pop(o, f);
        });
        putint(o, det);
        puts(o, "\n");
    });
    let c = format!(
        r#"{C_HEAD}{LCG_C}
#define N {N}
#define P {P}
static int64_t a[N * N];
static int64_t modinv(int64_t b) {{
    int64_t res = 1, e = P - 2;
    while (e) {{ if (e & 1) res = res * b % P; b = b * b % P; e >>= 1; }}
    return res;
}}
int main(void) {{
    int64_t seed = 77;
    for (int64_t i = 0; i < N * N; i++) {{ LCG(seed); a[i] = (seed >> 4) % P; }}
    int64_t det = 1;
    for (int64_t c = 0; c < N; c++) {{
        int64_t r = c;
        while (!a[r * N + c]) r++;
        if (r != c) {{
            for (int64_t j = 0; j < N; j++) {{ int64_t t = a[r * N + j]; a[r * N + j] = a[c * N + j]; a[c * N + j] = t; }}
            det = (P - det) % P;
        }}
        det = det * a[c * N + c] % P;
        int64_t inv = modinv(a[c * N + c]);
        for (r = c + 1; r < N; r++) {{
            int64_t f = inv * a[r * N + c] % P;
            for (int64_t j = 0; j < N; j++) a[r * N + j] = (a[r * N + j] - a[c * N + j] * f % P + P) % P;
        }}
    }}
    printf("%lld\n", (long long)det);
}}
"#
    );
    check("gauss", &ops, &c);
}
