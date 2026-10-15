//! LZ77 on 20000 bytes of text made of random words: at each position, the
//! longest match (up to 18 bytes) in the 255 before, greedily; prints how
//! many tokens it took and a checksum of them.

mod common;

use bf::asm::*;
use common::*;

const N: i64 = 20_000;
const WINDOW: i64 = 255;
const LONGEST: i64 = 18;
const WORDS: &str = "the quick brown fox jumps over lazy dog and cat sat on mat ";

#[test]
fn lz77_prints_what_c_does() {
    let ops = program(|o| {
        let (text, i, j, len, best, at, t, u) = (R1, R2, R3, R4, R5, R6, R7, R8);
        heap_alloc_const(o, text, N + LONGEST);
        // the words, and where each starts
        let words: Vec<&str> = WORDS.split_inclusive(' ').collect();
        heap_str(o, R9, WORDS);
        set(o, i, 0);
        set(o, at, 99);
        while_loop(o, R0, |o| { mov(o, R0, i); lt_const(o, R0, N); }, |o| {
            lcg(o, at);
            mov(o, t, at);
            rshu_const(o, t, 8);
            rem_const(o, t, words.len() as i64);
            // where word t starts, and how long it is: a chain of ifs
            set(o, u, 0);
            set(o, len, 0);
            let mut start = 0;
            for (k, w) in words.iter().enumerate() {
                mov(o, R0, t);
                eq_const(o, R0, k as i64);
                begin_if(o, R0);
                set_int(o, u, start);
                set_int(o, len, w.len() as i64);
                end_if(o);
                start += w.len() as i64;
            }
            set(o, j, 0);
            while_loop(o, R0, |o| { mov(o, R0, j); lt_assign(o, R0, len); }, |o| {
                mov(o, R0, u);
                add_assign(o, R0, j);
                load_index(o, best, R9, R0);
                mov(o, R0, i);
                add_assign(o, R0, j);
                store_index(o, text, R0, best);
                inc(o, j);
            });
            add_assign(o, i, len);
        });
        // (a sentinel past the end, so matches stop there)
        set(o, t, 0);
        for_const(o, i, N, N + LONGEST, R0, |o| store_index(o, text, i, t));
        // the tokens: R9 counts them, and the checksum is on the stack
        set(o, R9, 0);
        push(o, t);
        set(o, i, 0);
        while_loop(o, R0, |o| { mov(o, R0, i); lt_const(o, R0, N); }, |o| {
            set(o, best, 0);
            set(o, at, 0);
            mov(o, j, i);
            sub_const(o, j, WINDOW);
            set(o, t, 0);
            max_assign(o, j, t);
            while_loop(o, R0, |o| { mov(o, R0, j); lt_assign(o, R0, i); }, |o| {
                set(o, len, 0);
                while_loop(o, R0, |o| {
                    mov(o, t, j);
                    add_assign(o, t, len);
                    load_index(o, t, text, t);
                    mov(o, u, i);
                    add_assign(o, u, len);
                    load_index(o, u, text, u);
                    eq_assign(o, t, u);
                    mov(o, R0, len);
                    lt_const(o, R0, LONGEST);
                    land_assign(o, R0, t);
                    mov(o, t, i);
                    add_assign(o, t, len);
                    lt_const(o, t, N);
                    land_assign(o, R0, t);
                }, |o| inc(o, len));
                mov(o, t, len);
                gt_assign(o, t, best);
                begin_if(o, t);
                mov(o, best, len);
                mov(o, at, i);
                sub_assign(o, at, j);
                end_if(o);
                inc(o, j);
            });
            inc(o, R9);
            mov(o, t, best);
            ge_const(o, t, 3);
            begin_if(o, t);
            mul_const(o, at, 31);
            add_assign(o, at, best);
            add_assign(o, &SP.deref().offset(-1), at);
            add_assign(o, i, best);
            begin_else(o);
            load_index(o, t, text, i);
            add_assign(o, &SP.deref().offset(-1), t);
            inc(o, i);
            end_if(o);
        });
        pop(o, t);
        putint(o, R9);
        puts(o, " ");
        putint(o, t);
        puts(o, "\n");
    });
    let c = format!(
        r#"{C_HEAD}{LCG_C}
#define N {N}
static const char *words = "{WORDS}";
static int64_t text[N + {LONGEST}];
int main(void) {{
    int64_t starts[64], lens[64], nw = 0, at = 99;
    for (int64_t s = 0, k = 0; words[k]; k++)
        if (words[k] == ' ') {{ starts[nw] = s; lens[nw++] = k + 1 - s; s = k + 1; }}
    for (int64_t i = 0; i < N;) {{
        LCG(at);
        int64_t t = (at >> 8) % nw;
        for (int64_t j = 0; j < lens[t]; j++) text[i + j] = words[starts[t] + j];
        i += lens[t];
    }}
    for (int64_t i = N; i < N + {LONGEST}; i++) text[i] = 0;
    int64_t tokens = 0, sum = 0;
    for (int64_t i = 0; i < N;) {{
        int64_t best = 0, off = 0;
        for (int64_t j = i - {WINDOW} > 0 ? i - {WINDOW} : 0; j < i; j++) {{
            int64_t len = 0;
            while (text[j + len] == text[i + len] && len < {LONGEST} && i + len < N) len++;
            if (len > best) {{ best = len; off = i - j; }}
        }}
        tokens++;
        if (best >= 3) {{ sum += off * 31 + best; i += best; }}
        else {{ sum += text[i]; i++; }}
    }}
    printf("%lld %lld\n", (long long)tokens, (long long)sum);
}}
"#
    );
    check("lz77", &ops, &c);
}
