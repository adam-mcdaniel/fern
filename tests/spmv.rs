//! A sparse matrix (3000 rows, 1 to 9 entries each, in compressed rows)
//! times a vector, 300 times over, each result squashed into the next
//! vector; prints the last vector's sum.

mod common;

use bf::asm::*;
use common::*;

const N: i64 = 3000;
const ROUNDS: i64 = 300;
// the globals
const ROWS: i64 = 0;
const COLS: i64 = 1;
const VALS: i64 = 2;
const X: i64 = 3;
const Y: i64 = 4;
const ROUND: i64 = 5;
const FLAG: i64 = 6;

#[test]
fn spmv_prints_what_c_does() {
    let ops = program(|o| {
        let (r, e, end, s, t, u, seed, nnz) = (R1, R2, R3, R4, R5, R6, R7, R8);
        heap_alloc_const(o, R9, 7);
        for (array, n) in [(ROWS, N + 1), (COLS, N * 9), (VALS, N * 9), (X, N), (Y, N)] {
            heap_alloc_const(o, t, n);
            mov(o, &g(array), t);
        }
        set(o, seed, 77);
        set(o, nnz, 0);
        for_const(o, r, 0, N, R0, |o| {
            put(o, ROWS, r, nnz);
            lcg(o, seed);
            mov(o, end, seed);
            rshu_const(o, end, 8);
            rem_const(o, end, 9);
            add_assign(o, end, nnz);
            inc(o, end);
            while_loop(o, R0, |o| { mov(o, R0, nnz); lt_assign(o, R0, end); }, |o| {
                lcg(o, seed);
                mov(o, t, seed);
                rshu_const(o, t, 8);
                rem_const(o, t, N);
                put(o, COLS, nnz, t);
                lcg(o, seed);
                mov(o, t, seed);
                rshu_const(o, t, 8);
                rem_const(o, t, 19);
                sub_const(o, t, 9);
                put(o, VALS, nnz, t);
                inc(o, nnz);
            });
        });
        put(o, ROWS, r, nnz);
        for_const(o, r, 0, N, R0, |o| {
            mov(o, t, r);
            rem_const(o, t, 13);
            inc(o, t);
            put(o, X, r, t);
        });
        for_const(o, &g(ROUND), 0, ROUNDS, &g(FLAG), |o| {
            for_const(o, r, 0, N, R0, |o| {
                set(o, s, 0);
                get(o, e, ROWS, r);
                mov(o, end, r);
                inc(o, end);
                get(o, end, ROWS, end);
                while_loop(o, R0, |o| { mov(o, R0, e); lt_assign(o, R0, end); }, |o| {
                    get(o, t, COLS, e);
                    get(o, t, X, t);
                    get(o, u, VALS, e);
                    mul_assign(o, t, u);
                    add_assign(o, s, t);
                    inc(o, e);
                });
                put(o, Y, r, s);
            });
            for_const(o, r, 0, N, R0, |o| {
                get(o, t, Y, r);
                and_const(o, t, 1023);
                inc(o, t);
                put(o, X, r, t);
            });
        });
        set(o, s, 0);
        for_const(o, r, 0, N, R0, |o| {
            get(o, t, Y, r);
            add_assign(o, s, t);
        });
        putint(o, s);
        puts(o, "\n");
    });
    let c = format!(
        r#"{C_HEAD}{LCG_C}
#define N {N}
static int64_t rows[N + 1], cols[N * 9], vals[N * 9], x[N], y[N];
int main(void) {{
    int64_t seed = 77, nnz = 0;
    for (int64_t r = 0; r < N; r++) {{
        rows[r] = nnz;
        LCG(seed);
        int64_t end = nnz + (seed >> 8) % 9 + 1;
        while (nnz < end) {{
            LCG(seed); cols[nnz] = (seed >> 8) % N;
            LCG(seed); vals[nnz] = (seed >> 8) % 19 - 9;
            nnz++;
        }}
    }}
    rows[N] = nnz;
    for (int64_t r = 0; r < N; r++) x[r] = r % 13 + 1;
    for (int round = 0; round < {ROUNDS}; round++) {{
        for (int64_t r = 0; r < N; r++) {{
            int64_t s = 0;
            for (int64_t e = rows[r]; e < rows[r + 1]; e++) s += x[cols[e]] * vals[e];
            y[r] = s;
        }}
        for (int64_t r = 0; r < N; r++) x[r] = (y[r] & 1023) + 1;
    }}
    int64_t s = 0;
    for (int64_t r = 0; r < N; r++) s += y[r];
    printf("%lld\n", (long long)s);
}}
"#
    );
    check("spmv", &ops, &c);
}
