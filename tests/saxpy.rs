//! `y = a x + y` (in Q8) over 40000 elements, 600 times with a different `a`
//! each time; prints the sum of `y`.

mod common;

use bf::asm::*;
use common::*;

const N: i64 = 40_000;
const ROUNDS: i64 = 600;

#[test]
fn saxpy_prints_what_c_does() {
    let ops = program(|o| {
        let (x, y, i, t, u, a, r) = (R1, R2, R3, R4, R5, R6, R8);
        heap_alloc_const(o, x, N);
        heap_alloc_const(o, y, N);
        for_const(o, i, 0, N, R0, |o| {
            mov(o, t, i);
            rem_const(o, t, 1000);
            store_index(o, x, i, t);
            mov(o, t, i);
            rem_const(o, t, 77);
            store_index(o, y, i, t);
        });
        for_const(o, r, 0, ROUNDS, R7, |o| {
            mov(o, a, r);
            mul_const(o, a, 37);
            rem_const(o, a, 511);
            sub_const(o, a, 255);
            for_const(o, i, 0, N, R0, |o| {
                load_index(o, t, x, i);
                mul_assign(o, t, a);
                rsh_const(o, t, 8);
                load_index(o, u, y, i);
                add_assign(o, t, u);
                store_index(o, y, i, t);
            });
        });
        set(o, u, 0);
        for_const(o, i, 0, N, R0, |o| {
            load_index(o, t, y, i);
            add_assign(o, u, t);
        });
        putint(o, u);
        puts(o, "\n");
    });
    let c = format!(
        r#"{C_HEAD}
#define N {N}
static int64_t x[N], y[N];
int main(void) {{
    for (int64_t i = 0; i < N; i++) {{ x[i] = i % 1000; y[i] = i % 77; }}
    for (int64_t r = 0; r < {ROUNDS}; r++) {{
        int64_t a = r * 37 % 511 - 255;
        for (int64_t i = 0; i < N; i++) y[i] = ((x[i] * a) >> 8) + y[i];
    }}
    int64_t sum = 0;
    for (int64_t i = 0; i < N; i++) sum += y[i];
    printf("%lld\n", (long long)sum);
}}
"#
    );
    check("saxpy", &ops, &c);
}
