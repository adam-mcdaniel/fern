//! CRC-32 (the zlib one, by a table) of 60000 random bytes: each step
//! depends on the last.

mod common;

use bf::asm::*;
use common::*;

const N: i64 = 60_000;
const POLY: i64 = 0xEDB8_8320;

#[test]
fn crc32_prints_what_c_does() {
    let ops = program(|o| {
        let (table, data, i, c, t, crc, seed) = (R1, R2, R3, R4, R5, R6, R7);
        heap_alloc_const(o, table, 256);
        heap_alloc_const(o, data, N);
        for_const(o, i, 0, 256, R0, |o| {
            mov(o, c, i);
            for_const(o, R8, 0, 8, R9, |o| {
                mov(o, t, c);
                and_const(o, t, 1);
                rshu_const(o, c, 1);
                begin_if(o, t);
                xor_const(o, c, POLY);
                end_if(o);
            });
            store_index(o, table, i, c);
        });
        set(o, seed, 1);
        for_const(o, i, 0, N, R0, |o| {
            lcg(o, seed);
            mov(o, t, seed);
            rshu_const(o, t, 16);
            and_const(o, t, 255);
            store_index(o, data, i, t);
        });
        set_int(o, crc, 0xFFFF_FFFF);
        for_const(o, i, 0, N, R0, |o| {
            load_index(o, t, data, i);
            xor_assign(o, t, crc);
            and_const(o, t, 255);
            load_index(o, t, table, t);
            rshu_const(o, crc, 8);
            xor_assign(o, crc, t);
        });
        xor_const(o, crc, 0xFFFF_FFFF);
        putint(o, crc);
        puts(o, "\n");
    });
    let c = format!(
        r#"{C_HEAD}{LCG_C}
static int64_t table[256], data[{N}];
int main(void) {{
    for (int64_t i = 0; i < 256; i++) {{
        uint64_t c = i;
        for (int k = 0; k < 8; k++) c = (c & 1) ? (c >> 1) ^ {POLY}ull : c >> 1;
        table[i] = c;
    }}
    int64_t seed = 1;
    for (int64_t i = 0; i < {N}; i++) {{ LCG(seed); data[i] = (seed >> 16) & 255; }}
    uint64_t crc = 0xFFFFFFFFull;
    for (int64_t i = 0; i < {N}; i++) crc = table[(data[i] ^ crc) & 255] ^ (crc >> 8);
    printf("%lld\n", (long long)(crc ^ 0xFFFFFFFFull));
}}
"#
    );
    check("crc32", &ops, &c);
}
