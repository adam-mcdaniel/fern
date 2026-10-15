//! Fannkuch-redux (as in the benchmarks game) for 10: over every permutation
//! of 0 to 9, how many prefix reversals it takes to bring 0 to the front;
//! prints the checksum and the most.

mod common;

use bf::asm::*;
use common::*;

const N: i64 = 10;

#[test]
fn fannkuch_prints_what_c_does() {
    let ops = program(|o| {
        let (perm, perm1, count) = (R1, R2, R3);
        // l0 n, l1 r, l2 checksum, l3 most, l4 permutations, l5 i, l6 j,
        // l7 k, l8 flips, l9 and l10 scratch, l11 perm1[0]
        begin_func(o, "fannkuch", 12);
        mov(o, &l(0), &arg(0));
        for_range(o, &l(5), 0, &l(0), R4, |o| store_index(o, perm1, &l(5), &l(5)));
        mov(o, &l(1), &l(0));
        for k in 2..5 {
            set(o, &l(k), 0);
        }
        begin_loop(o);
        while_loop(o, R4, |o| { mov(o, R4, &l(1)); ne_const(o, R4, 1); }, |o| {
            mov(o, &l(9), &l(1));
            dec(o, &l(9));
            store_index(o, count, &l(9), &l(1));
            dec(o, &l(1));
        });
        for_range(o, &l(5), 0, &l(0), R4, |o| {
            load_index(o, &l(9), perm1, &l(5));
            store_index(o, perm, &l(5), &l(9));
        });
        set(o, &l(8), 0);
        while_loop(o, R4, |o| { set(o, &l(9), 0); load_index(o, &l(7), perm, &l(9)); mov(o, R4, &l(7)); }, |o| {
            set(o, &l(5), 0);
            mov(o, &l(6), &l(7));
            while_loop(o, R5, |o| { mov(o, R5, &l(5)); lt_assign(o, R5, &l(6)); }, |o| {
                load_index(o, &l(9), perm, &l(5));
                load_index(o, &l(10), perm, &l(6));
                store_index(o, perm, &l(5), &l(10));
                store_index(o, perm, &l(6), &l(9));
                inc(o, &l(5));
                dec(o, &l(6));
            });
            inc(o, &l(8));
        });
        max_assign(o, &l(3), &l(8));
        mov(o, &l(9), &l(4));
        and_const(o, &l(9), 1);
        begin_if(o, &l(9));
        sub_assign(o, &l(2), &l(8));
        begin_else(o);
        add_assign(o, &l(2), &l(8));
        end_if(o);
        // the next permutation
        begin_loop(o);
        mov(o, &l(9), &l(1));
        eq_assign(o, &l(9), &l(0));
        begin_if(o, &l(9));
        putint(o, &l(2));
        puts(o, "\n");
        putint(o, &l(3));
        puts(o, "\n");
        ret(o);
        end_if(o);
        set(o, &l(9), 0);
        load_index(o, &l(11), perm1, &l(9));
        for_range(o, &l(5), 0, &l(1), R5, |o| {
            mov(o, &l(9), &l(5));
            inc(o, &l(9));
            load_index(o, &l(10), perm1, &l(9));
            store_index(o, perm1, &l(5), &l(10));
        });
        store_index(o, perm1, &l(1), &l(11));
        load_index(o, &l(9), count, &l(1));
        dec(o, &l(9));
        store_index(o, count, &l(1), &l(9));
        gt_const(o, &l(9), 0);
        break_if(o, &l(9));
        inc(o, &l(1));
        end_loop(o);
        inc(o, &l(4));
        end_loop(o);
        end_func(o);

        for r in [perm, perm1, count] {
            heap_alloc_const(o, r, N);
        }
        set(o, R6, N as u64);
        call(o, "fannkuch", &[R6]);
    });
    let c = format!(
        r#"{C_HEAD}
#define N {N}
static int64_t perm[N], perm1[N], count[N];
int main(void) {{
    int64_t n = N, r = n, checksum = 0, most = 0, permutations = 0;
    for (int64_t i = 0; i < n; i++) perm1[i] = i;
    for (;;) {{
        while (r != 1) {{ count[r - 1] = r; r--; }}
        for (int64_t i = 0; i < n; i++) perm[i] = perm1[i];
        int64_t flips = 0, k;
        while ((k = perm[0])) {{
            for (int64_t i = 0, j = k; i < j; i++, j--) {{ int64_t t = perm[i]; perm[i] = perm[j]; perm[j] = t; }}
            flips++;
        }}
        if (flips > most) most = flips;
        if (permutations & 1) checksum -= flips; else checksum += flips;
        for (;;) {{
            if (r == n) {{ printf("%lld\n%lld\n", (long long)checksum, (long long)most); return 0; }}
            int64_t p0 = perm1[0];
            for (int64_t i = 0; i < r; i++) perm1[i] = perm1[i + 1];
            perm1[r] = p0;
            if (--count[r] > 0) break;
            r++;
        }}
        permutations++;
    }}
}}
"#
    );
    check("fannkuch", &ops, &c);
}
