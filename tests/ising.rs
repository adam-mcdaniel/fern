//! The 2D Ising model (periodic, 128 by 128) by Metropolis sweeps, a
//! checkerboard colour at a time, each site's random number a hash of where
//! and when; prints the magnetisation and the energy. (Each site reads its
//! neighbours, of the other colour: the analysis can't tell they aren't the
//! ones being written, so it runs in order.)

mod common;

use bf::asm::*;
use common::*;

const L: i64 = 128;
const SWEEPS: i64 = 40;
// exp(-4 beta) and exp(-8 beta) in Q16, for beta = 0.44
const T4: i64 = 11_268;
const T8: i64 = 1_938;

#[test]
fn ising_prints_what_c_does() {
    let n = L * L;
    let ops = program(|o| {
        let (spin, i, sum, t, u, h, colour, sweep) = (R1, R2, R3, R4, R5, R6, R7, R8);
        heap_alloc_const(o, spin, n);
        for_const(o, i, 0, n, R0, |o| {
            mov(o, t, i);
            mul_const(o, t, 2_654_435_761);
            rshu_const(o, t, 7);
            and_const(o, t, 1);
            add_assign(o, t, t);
            dec(o, t);
            store_index(o, spin, i, t);
        });
        for_const(o, sweep, 0, SWEEPS, R0, |o| {
            for_const(o, colour, 0, 2, R0, |o| {
                for_const(o, i, 0, n, R0, |o| {
                    // this colour's sites: (row + column) % 2
                    mov(o, t, i);
                    rshu_const(o, t, 7);
                    mov(o, u, i);
                    and_const(o, u, L - 1);
                    add_assign(o, t, u);
                    and_const(o, t, 1);
                    eq_assign(o, t, colour);
                    begin_if(o, t);
                    // the neighbours' sum: left, right, up, down
                    set(o, sum, 0);
                    for (dc, dr) in [(L - 1, 0), (1, 0), (0, L - 1), (0, 1)] {
                        mov(o, t, i);
                        and_const(o, t, L - 1);
                        add_const(o, t, dc);
                        and_const(o, t, L - 1);
                        mov(o, u, i);
                        rshu_const(o, u, 7);
                        add_const(o, u, dr);
                        and_const(o, u, L - 1);
                        mul_const(o, u, L);
                        add_assign(o, t, u);
                        load_index(o, t, spin, t);
                        add_assign(o, sum, t);
                    }
                    // the energy it'd take to flip: 2 s sum
                    load_index(o, t, spin, i);
                    mul_assign(o, sum, t);
                    add_assign(o, sum, sum);
                    // a random number from where and when
                    mov(o, h, i);
                    mul_const(o, h, 7919);
                    mov(o, u, sweep);
                    mul_const(o, u, 104_729);
                    add_assign(o, h, u);
                    add_assign(o, h, colour);
                    mul_const(o, h, 0x9E37_79B9_7F4A_7C15_u64 as i64);
                    mov(o, u, h);
                    rshu_const(o, u, 29);
                    xor_assign(o, h, u);
                    rshu_const(o, h, 16);
                    and_const(o, h, 0xFFFF);
                    // flip if that lowers it, or by chance
                    mov(o, u, sum);
                    le_const(o, u, 0);
                    mov(o, R9, sum);
                    eq_const(o, R9, 4);
                    begin_if(o, R9);
                    mov(o, u, h);
                    lt_const(o, u, T4);
                    end_if(o);
                    mov(o, R9, sum);
                    eq_const(o, R9, 8);
                    begin_if(o, R9);
                    mov(o, u, h);
                    lt_const(o, u, T8);
                    end_if(o);
                    begin_if(o, u);
                    neg_assign(o, t);
                    store_index(o, spin, i, t);
                    end_if(o);
                    end_if(o);
                });
            });
        });
        set(o, sum, 0);
        set(o, h, 0);
        for_const(o, i, 0, n, R0, |o| {
            load_index(o, t, spin, i);
            add_assign(o, sum, t);
            mov(o, u, i);
            inc(o, u);
            and_const(o, u, L - 1);
            mov(o, R9, i);
            rshu_const(o, R9, 7);
            mul_const(o, R9, L);
            add_assign(o, u, R9);
            load_index(o, u, spin, u);
            mul_assign(o, u, t);
            sub_assign(o, h, u);
            mov(o, u, i);
            add_const(o, u, L);
            and_const(o, u, n - 1);
            load_index(o, u, spin, u);
            mul_assign(o, u, t);
            sub_assign(o, h, u);
        });
        putint(o, sum);
        puts(o, " ");
        putint(o, h);
        puts(o, "\n");
    });
    let c = format!(
        r#"{C_HEAD}
#define L {L}
#define NN (L * L)
static int64_t spin[NN];
int main(void) {{
    for (int64_t i = 0; i < NN; i++) spin[i] = (int64_t)(((uint64_t)(i * 2654435761ll) >> 7) & 1) * 2 - 1;
    for (int64_t sweep = 0; sweep < {SWEEPS}; sweep++)
        for (int64_t colour = 0; colour < 2; colour++)
            for (int64_t i = 0; i < NN; i++) {{
                int64_t r = (uint64_t)i >> 7, c = i & (L - 1);
                if (((r + c) & 1) != colour) continue;
                int64_t sum = spin[r * L + ((c + L - 1) & (L - 1))] + spin[r * L + ((c + 1) & (L - 1))]
                    + spin[((r + L - 1) & (L - 1)) * L + c] + spin[((r + 1) & (L - 1)) * L + c];
                int64_t s = spin[i];
                sum = 2 * sum * s;
                uint64_t h = (uint64_t)(i * 7919 + sweep * 104729 + colour) * 0x9E3779B97F4A7C15ull;
                h ^= h >> 29;
                int64_t rnd = (h >> 16) & 0xFFFF;
                int64_t flip = sum <= 0;
                if (sum == 4) flip = rnd < {T4};
                if (sum == 8) flip = rnd < {T8};
                if (flip) spin[i] = -s;
            }}
    int64_t m = 0, e = 0;
    for (int64_t i = 0; i < NN; i++) {{
        int64_t s = spin[i];
        m += s;
        e -= s * spin[(((uint64_t)i >> 7) * L) + ((i + 1) & (L - 1))];
        e -= s * spin[(i + L) & (NN - 1)];
    }}
    printf("%lld %lld\n", (long long)m, (long long)e);
}}
"#
    );
    check("ising", &ops, &c);
}
