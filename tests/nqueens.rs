//! How many ways 13 queens fit on a 13 by 13 board without attacking each
//! other, by backtracking a row at a time with bit masks (one array of masks
//! per kind of attack, by row).

mod common;

use bf::asm::*;
use common::*;

const N: i64 = 13;

#[test]
fn nqueens_prints_what_c_does() {
    let all = (1i64 << N) - 1;
    let ops = program(|o| {
        let (cl, ld, rd, av, r, bit, t, count, u) = (R1, R2, R3, R4, R5, R6, R7, R8, R9);
        for a in [cl, ld, rd, av] {
            heap_alloc_const(o, a, N + 1);
        }
        set(o, r, 0);
        set(o, count, 0);
        set(o, t, 0);
        store_index(o, cl, r, t);
        store_index(o, ld, r, t);
        store_index(o, rd, r, t);
        set_int(o, t, all);
        store_index(o, av, r, t);
        begin_loop(o);
        load_index(o, t, av, r);
        mov(o, u, t);
        lnot_assign(o, u);
        begin_if(o, u);
        // nowhere left in this row: back up a row (or stop)
        mov(o, u, r);
        lnot_assign(o, u);
        break_if(o, u);
        dec(o, r);
        continue_loop(o);
        end_if(o);
        // the lowest place left
        mov(o, bit, t);
        neg_assign(o, bit);
        and_assign(o, bit, t);
        xor_assign(o, t, bit);
        store_index(o, av, r, t);
        mov(o, u, r);
        eq_const(o, u, N - 1);
        begin_if(o, u);
        inc(o, count);
        continue_loop(o);
        end_if(o);
        // the next row: what's attacked there
        mov(o, u, r);
        inc(o, u);
        load_index(o, t, cl, r);
        or_assign(o, t, bit);
        store_index(o, cl, u, t);
        load_index(o, t, ld, r);
        or_assign(o, t, bit);
        add_assign(o, t, t);
        and_const(o, t, all);
        store_index(o, ld, u, t);
        load_index(o, t, rd, r);
        or_assign(o, t, bit);
        rshu_const(o, t, 1);
        store_index(o, rd, u, t);
        load_index(o, t, cl, u);
        load_index(o, bit, ld, u);
        or_assign(o, t, bit);
        load_index(o, bit, rd, u);
        or_assign(o, t, bit);
        not_assign(o, t);
        and_const(o, t, all);
        store_index(o, av, u, t);
        mov(o, r, u);
        end_loop(o);
        putint(o, count);
        puts(o, "\n");
    });
    let c = format!(
        r#"{C_HEAD}
#define N {N}
static int64_t cl[N + 1], ld[N + 1], rd[N + 1], av[N + 1];
int main(void) {{
    int64_t all = {all}, r = 0, count = 0;
    av[0] = all;
    for (;;) {{
        int64_t t = av[r];
        if (!t) {{ if (!r) break; r--; continue; }}
        int64_t bit = t & -t;
        av[r] = t ^ bit;
        if (r == N - 1) {{ count++; continue; }}
        cl[r + 1] = cl[r] | bit;
        ld[r + 1] = ((ld[r] | bit) << 1) & all;
        rd[r + 1] = (int64_t)((uint64_t)(rd[r] | bit) >> 1);
        av[r + 1] = ~(cl[r + 1] | ld[r + 1] | rd[r + 1]) & all;
        r++;
    }}
    printf("%lld\n", (long long)count);
}}
"#
    );
    check("nqueens", &ops, &c);
}
