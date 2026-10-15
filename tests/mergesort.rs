//! Bottom-up merge sort of 16000 random numbers (runs of 1, 2, 4, ...,
//! merged from one array into the other); prints a weighted sum.

mod common;

use bf::asm::*;
use common::*;

const N: i64 = 16_000;

#[test]
fn mergesort_prints_what_c_does() {
    let ops = program(|o| {
        // l0 width, l1 lo, l2 mid, l3 hi, l4 i, l5 j, l6 k, l7 and l8 scratch
        let (src, dst) = (R1, R2);
        begin_func(o, "sort", 9);
        set(o, &l(0), 1);
        while_loop(o, R3, |o| { mov(o, R3, &l(0)); lt_const(o, R3, N); }, |o| {
            set(o, &l(1), 0);
            while_loop(o, R4, |o| { mov(o, R4, &l(1)); lt_const(o, R4, N); }, |o| {
                mov(o, &l(2), &l(1));
                add_assign(o, &l(2), &l(0));
                set(o, &l(7), N as u64);
                min_assign(o, &l(2), &l(7));
                mov(o, &l(3), &l(2));
                add_assign(o, &l(3), &l(0));
                min_assign(o, &l(3), &l(7));
                mov(o, &l(4), &l(1));
                mov(o, &l(5), &l(2));
                mov(o, &l(6), &l(1));
                while_loop(o, R5, |o| { mov(o, R5, &l(6)); lt_assign(o, R5, &l(3)); }, |o| {
                    // from the left run if it has one left that's no bigger
                    mov(o, &l(7), &l(4));
                    lt_assign(o, &l(7), &l(2));
                    begin_if(o, &l(7));
                    mov(o, &l(7), &l(5));
                    lt_assign(o, &l(7), &l(3));
                    begin_if(o, &l(7));
                    load_index(o, &l(7), src, &l(4));
                    load_index(o, &l(8), src, &l(5));
                    le_assign(o, &l(7), &l(8));
                    begin_else(o);
                    set(o, &l(7), 1);
                    end_if(o);
                    end_if(o);
                    begin_if(o, &l(7));
                    load_index(o, &l(8), src, &l(4));
                    inc(o, &l(4));
                    begin_else(o);
                    load_index(o, &l(8), src, &l(5));
                    inc(o, &l(5));
                    end_if(o);
                    store_index(o, dst, &l(6), &l(8));
                    inc(o, &l(6));
                });
                mov(o, &l(1), &l(3));
            });
            mov(o, &l(7), src);
            mov(o, src, dst);
            mov(o, dst, &l(7));
            add_assign(o, &l(0), &l(0));
        });
        end_func(o);

        heap_alloc_const(o, src, N);
        heap_alloc_const(o, dst, N);
        set(o, R6, 31);
        for_const(o, R3, 0, N, R0, |o| {
            lcg(o, R6);
            mov(o, R4, R6);
            rshu_const(o, R4, 5);
            rem_const(o, R4, 1_000_000);
            store_index(o, src, R3, R4);
        });
        call(o, "sort", &[]);
        set(o, R5, 0);
        for_const(o, R3, 0, N, R0, |o| {
            load_index(o, R4, src, R3);
            mov(o, R6, R3);
            rem_const(o, R6, 97);
            inc(o, R6);
            mul_assign(o, R4, R6);
            add_assign(o, R5, R4);
        });
        putint(o, R5);
        puts(o, "\n");
    });
    let c = format!(
        r#"{C_HEAD}{LCG_C}
#define N {N}
static int64_t a0[N], a1[N];
int main(void) {{
    int64_t *src = a0, *dst = a1, seed = 31;
    for (int64_t i = 0; i < N; i++) {{ LCG(seed); src[i] = (seed >> 5) % 1000000; }}
    for (int64_t w = 1; w < N; w += w) {{
        for (int64_t lo = 0; lo < N; ) {{
            int64_t mid = lo + w < N ? lo + w : N, hi = mid + w < N ? mid + w : N;
            int64_t i = lo, j = mid;
            for (int64_t k = lo; k < hi; k++) {{
                int64_t left = i < mid ? (j < hi ? src[i] <= src[j] : 1) : 0;
                dst[k] = left ? src[i++] : src[j++];
            }}
            lo = hi;
        }}
        int64_t *t = src; src = dst; dst = t;
    }}
    int64_t sum = 0;
    for (int64_t i = 0; i < N; i++) sum += src[i] * (i % 97 + 1);
    printf("%lld\n", (long long)sum);
}}
"#
    );
    check("mergesort", &ops, &c);
}
