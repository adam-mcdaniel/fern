//! ChaCha20's block function (20 rounds of quarter-rounds: 32-bit adds,
//! xors and rotations) over 4000 counters; prints a checksum of the output
//! words.

mod common;

use bf::asm::*;
use common::*;

const BLOCKS: i64 = 4000;
const M32: i64 = 0xFFFF_FFFF;

#[test]
fn chacha_prints_what_c_does() {
    let ops = program(|o| {
        // x[16] in the block's own cells of a scratch array, by block
        let (x, n, sum, a, b, t) = (R1, R2, R3, R4, R5, R6);
        heap_alloc_const(o, x, 16);
        // x[i] for the quarter-round's indices
        let get = |o: &mut dyn Program, dst: &Location, i: i64| {
            set(o, R7, i as u64);
            load_index(o, dst, x, R7);
        };
        let put = |o: &mut dyn Program, i: i64, src: &Location| {
            set(o, R7, i as u64);
            store_index(o, x, R7, src);
        };
        // x[a] += x[b]; x[d] ^= x[a]; x[d] <<<= r, with the words kept to 32 bits
        let step = |o: &mut dyn Program, ia: i64, ib: i64, id: i64, r: i64| {
            get(o, a, ia);
            get(o, b, ib);
            add_assign(o, a, b);
            and_const(o, a, M32);
            put(o, ia, a);
            get(o, b, id);
            xor_assign(o, b, a);
            mov(o, t, b);
            lsh_const(o, t, r);
            rshu_const(o, b, 32 - r);
            or_assign(o, b, t);
            and_const(o, b, M32);
            put(o, id, b);
        };
        let qr = |o: &mut dyn Program, i: [i64; 4]| {
            step(o, i[0], i[1], i[3], 16);
            step(o, i[2], i[3], i[1], 12);
            step(o, i[0], i[1], i[3], 8);
            step(o, i[2], i[3], i[1], 7);
        };
        set(o, sum, 0);
        for_const(o, n, 0, BLOCKS, R0, |o| {
            for i in 0..16 {
                set_int(o, a, (0x6170_7865 + 0x0101_0101 * i) & M32);
                if i == 12 {
                    mov(o, a, n);
                }
                put(o, i, a);
            }
            for_const(o, R8, 0, 10, R9, |o| {
                qr(o, [0, 4, 8, 12]);
                qr(o, [1, 5, 9, 13]);
                qr(o, [2, 6, 10, 14]);
                qr(o, [3, 7, 11, 15]);
                qr(o, [0, 5, 10, 15]);
                qr(o, [1, 6, 11, 12]);
                qr(o, [2, 7, 8, 13]);
                qr(o, [3, 4, 9, 14]);
            });
            for i in 0..16 {
                get(o, a, i);
                mul_const(o, a, i + 1);
                add_assign(o, sum, a);
            }
        });
        putint(o, sum);
        puts(o, "\n");
    });
    let c = format!(
        r#"{C_HEAD}
#define ROTL(v, r) ((((v) << (r)) | ((v) >> (32 - (r)))) & 0xFFFFFFFFull)
#define STEP(a, b, d, r) x[a] = (x[a] + x[b]) & 0xFFFFFFFFull; x[d] = ROTL(x[d] ^ x[a], r)
#define QR(a, b, c, d) STEP(a, b, d, 16); STEP(c, d, b, 12); STEP(a, b, d, 8); STEP(c, d, b, 7)
int main(void) {{
    uint64_t x[16];
    int64_t sum = 0;
    for (int64_t n = 0; n < {BLOCKS}; n++) {{
        for (int i = 0; i < 16; i++) x[i] = (0x61707865ull + 0x01010101ull * i) & 0xFFFFFFFFull;
        x[12] = n;
        for (int r = 0; r < 10; r++) {{
            QR(0, 4, 8, 12); QR(1, 5, 9, 13); QR(2, 6, 10, 14); QR(3, 7, 11, 15);
            QR(0, 5, 10, 15); QR(1, 6, 11, 12); QR(2, 7, 8, 13); QR(3, 4, 9, 14);
        }}
        for (int i = 0; i < 16; i++) sum += (int64_t)x[i] * (i + 1);
    }}
    printf("%lld\n", (long long)sum);
}}
"#
    );
    check("chacha", &ops, &c);
}
