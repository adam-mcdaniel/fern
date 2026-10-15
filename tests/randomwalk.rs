//! Random walks: 4096 walkers, each with its own random number generator,
//! taking 3000 steps on a grid; prints the sum of their squared distances
//! from where they started.

mod common;

use bf::asm::*;
use common::*;

const M: i64 = 4096;
const STEPS: i64 = 3000;

#[test]
fn randomwalk_prints_what_c_does() {
    let ops = program(|o| {
        let (state, xs, ys, p, s, x, y, t, d) = (R1, R2, R3, R4, R5, R6, R7, R8, R9);
        for r in [state, xs, ys] {
            heap_alloc_const(o, r, M);
        }
        for_const(o, p, 0, M, R0, |o| {
            mov(o, t, p);
            mul_const(o, t, 7);
            add_const(o, t, 1);
            store_index(o, state, p, t);
            set(o, t, 0);
            store_index(o, xs, p, t);
            store_index(o, ys, p, t);
        });
        for_const(o, p, 0, M, R0, |o| {
            load_index(o, s, state, p);
            load_index(o, x, xs, p);
            load_index(o, y, ys, p);
            for_const(o, d, 0, STEPS, R0, |o| {
                lcg(o, s);
                mov(o, t, s);
                rshu_const(o, t, 16);
                and_const(o, t, 3);
                // 0: right, 1: left, 2: up, 3: down
                push(o, t);
                eq_const(o, t, 0);
                add_assign(o, x, t);
                pop(o, t);
                push(o, t);
                eq_const(o, t, 1);
                sub_assign(o, x, t);
                pop(o, t);
                push(o, t);
                eq_const(o, t, 2);
                add_assign(o, y, t);
                pop(o, t);
                eq_const(o, t, 3);
                sub_assign(o, y, t);
            });
            store_index(o, state, p, s);
            store_index(o, xs, p, x);
            store_index(o, ys, p, y);
        });
        set(o, s, 0);
        for_const(o, p, 0, M, R0, |o| {
            load_index(o, x, xs, p);
            mul_assign(o, x, x);
            add_assign(o, s, x);
            load_index(o, y, ys, p);
            mul_assign(o, y, y);
            add_assign(o, s, y);
        });
        putint(o, s);
        puts(o, "\n");
    });
    let c = format!(
        r#"{C_HEAD}{LCG_C}
#define M {M}
static int64_t state[M], xs[M], ys[M];
int main(void) {{
    for (int64_t p = 0; p < M; p++) {{ state[p] = p * 7 + 1; xs[p] = ys[p] = 0; }}
    for (int64_t p = 0; p < M; p++) {{
        int64_t s = state[p], x = xs[p], y = ys[p];
        for (int d = 0; d < {STEPS}; d++) {{
            LCG(s);
            int64_t t = (s >> 16) & 3;
            x += (t == 0) - (t == 1);
            y += (t == 2) - (t == 3);
        }}
        state[p] = s; xs[p] = x; ys[p] = y;
    }}
    int64_t sum = 0;
    for (int64_t p = 0; p < M; p++) sum += xs[p] * xs[p] + ys[p] * ys[p];
    printf("%lld\n", (long long)sum);
}}
"#
    );
    check("randomwalk", &ops, &c);
}
