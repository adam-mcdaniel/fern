//! Idioms: functions whose effect is known, so that they can be done with
//! the machine's own instructions instead of the VM's.
//!
//! The VM has no multiplication, division or comparison, so programs do
//! them with loops over bits (the `asm` helpers' routines: `rt_mul`,
//! `rt_divu`, ...), which take about as many passes as the cells have
//! bits. When a function in the program is exactly, op for op, one of
//! those routines as `asm` writes it, it does exactly what that routine
//! does, so the target can do that in a few instructions: the result, and
//! every other cell the routine leaves something in, and acc, as the loop
//! would leave them (see `tests::idioms_do_what_the_routines_do`, which
//! checks each against the routine on all sorts of values). A function
//! that differs at all is compiled as it is.
//!
//! The native code works on `ptr` (where the pointer is when the function
//! is called: cell 0, with the routines' `T` registers at cells 1 to 15)
//! and `acc`. `ORIGINAL` in it stands for the function's own code, for
//! values the native code leaves to it. Each write to a cell is a line of
//! its own starting `ptr[`, and only happens if the routine would write the
//! cell (an iteration running in parallel notes which cells it writes).

use crate::asm::{self, Location};
use crate::Op;
use std::collections::HashMap;

/// A routine `asm` writes: its label, its body, and C that does the same.
pub struct Idiom {
    pub label: String,
    pub body: Vec<Op>,
    pub native: String,
    /// For testing: C that changes the cells `c` (with `bf_rand()`) to
    /// values the routine finishes for (some count down a cell to 0).
    #[cfg_attr(not(test), allow(dead_code))]
    pub tame: &'static str,
}

/// The functions `build` defines in a program, by label: their bodies.
fn defined(build: impl FnOnce(&mut Vec<Op>)) -> HashMap<String, Vec<Op>> {
    let mut ops = vec![];
    build(&mut ops);
    let mut out = HashMap::new();
    for i in 0..ops.len().saturating_sub(1) {
        if let (Op::Label(l), Op::Func) = (ops[i], ops[i + 1]) {
            let mut depth = 0;
            for (j, op) in ops.iter().enumerate().skip(i + 1) {
                match op {
                    Op::Func => depth += 1,
                    Op::EndFunc => {
                        depth -= 1;
                        if depth == 0 {
                            out.insert(super::label_name(&l), ops[i + 2..j].to_vec());
                            break;
                        }
                    }
                    _ => {}
                }
            }
        }
    }
    out
}

/// `rt_mul`: `T2 = T0 * T1`, a bit of `T0` at a time from the top, which
/// shifts `T0` out (to 0), counts the bits out in `T3` (to 0), leaves the
/// last bit it looked at (`T0`'s lowest) in `T4`, and the flag `begin_if`
/// keeps in `T9` set.
const MUL: &str = r#"{
int64_t bf_a = ptr[1], bf_b = ptr[2];
ptr[3] = (int64_t)((uint64_t)bf_a * (uint64_t)bf_b);
ptr[1] = 0;
ptr[4] = 0;
ptr[5] = bf_a & 1;
ptr[10] = 1;
acc = 0;
}
"#;

/// `rt_less`: acc = `T12 < T13`, signed, from their top bits (`T10`,
/// `T11`) and the sign of `T13 - T12`; `T10` is left as twice the
/// difference of the top bits.
const LESS: &str = r#"{
int64_t bf_a = ptr[13], bf_b = ptr[14];
int64_t bf_an = bf_a < 0, bf_bn = bf_b < 0;
int64_t bf_x = 2 * (bf_an - bf_bn);
ptr[11] = bf_x;
ptr[12] = bf_bn;
acc = (((int64_t)((uint64_t)bf_b - (uint64_t)bf_a) > 0) + bf_x) > 0;
}
"#;

/// `rt_lessu`: the same, unsigned (`T11` is left as twice the difference).
const LESSU: &str = r#"{
int64_t bf_a = ptr[13], bf_b = ptr[14];
int64_t bf_an = bf_a < 0, bf_bn = bf_b < 0;
int64_t bf_x = 2 * (bf_bn - bf_an);
ptr[11] = bf_an;
ptr[12] = bf_x;
acc = (((int64_t)((uint64_t)bf_b - (uint64_t)bf_a) > 0) + bf_x) > 0;
}
"#;

/// `rt_divu`: `T14 = T12 / T13` and `T12 = T6 = T12 % T13`, unsigned, a bit
/// at a time after skipping `T12`'s leading zeros. The scratch cells are
/// left as the last pass leaves them: which depends on the remainder before
/// it, `(T12 >> 1) % T13`. Dividing by 0 is left to the routine.
const DIVU: &str = r#"{
uint64_t bf_n = (uint64_t)ptr[13], bf_d = (uint64_t)ptr[14];
if (bf_d == 0) {
ORIGINAL
} else if (bf_n == 0) {
ptr[7] = 0;
ptr[8] = 0;
ptr[9] = 0;
ptr[12] = 0;
ptr[13] = 0;
ptr[15] = 0;
acc = 0;
} else {
uint64_t bf_q = bf_n / bf_d, bf_r = bf_n % bf_d;
/* the remainder before the last pass, rp = (n >> 1) % d, from the last: that
   pass took d off 2 rp + (n & 1) just when it set the quotient's lowest bit */
uint64_t bf_rp = (uint64_t)(((unsigned __int128)bf_r + (bf_q & 1 ? bf_d : 0) - (bf_n & 1)) >> 1);
int64_t bf_carry = (int64_t)bf_rp < 0;
uint64_t bf_r1 = 2 * bf_rp + (bf_n & 1);
int64_t bf_r1n = (int64_t)bf_r1 < 0, bf_dn = (int64_t)bf_d < 0;
int64_t bf_t11 = 2 * (bf_dn - bf_r1n);
int64_t bf_lt = (((int64_t)(bf_d - bf_r1) > 0) + bf_t11) > 0;
ptr[7] = (int64_t)bf_r;
ptr[8] = 0;
ptr[9] = bf_carry + 1 - bf_lt;
ptr[10] = 1;
ptr[11] = -bf_lt;
ptr[12] = bf_t11;
ptr[13] = (int64_t)bf_r;
ptr[15] = (int64_t)bf_q;
acc = (int64_t)bf_r;
}
}
"#;

/// `rt_divuk`: `T14 = T12 / T13` and `T12 = T6 = T12 % T13`, unsigned, for
/// small divisors, a bit at a time after skipping `T12`'s leading zeros.
/// The last pass leaves the bit it shifted in (`T12`'s lowest) in `T11`,
/// whether it subtracted in `T8` (the quotient's lowest bit), and that less
/// 1 in `T10`. Divisors from 2^62 up (whose remainders can overflow), and 0,
/// are left to the routine.
const DIVUK: &str = r#"{
uint64_t bf_n = (uint64_t)ptr[13], bf_d = (uint64_t)ptr[14];
if (bf_d == 0 || bf_d >= ((uint64_t)1 << 62)) {
ORIGINAL
} else if (bf_n == 0) {
ptr[7] = 0;
ptr[8] = 0;
ptr[9] = 0;
ptr[12] = 0;
ptr[13] = 0;
ptr[15] = 0;
acc = 0;
} else {
uint64_t bf_q = bf_n / bf_d, bf_r = bf_n % bf_d;
int64_t bf_sub = (int64_t)(bf_q & 1);
ptr[7] = (int64_t)bf_r;
ptr[8] = 0;
ptr[9] = bf_sub;
ptr[10] = 1;
ptr[11] = bf_sub - 1;
ptr[12] = (int64_t)(bf_n & 1);
ptr[13] = (int64_t)bf_r;
ptr[15] = (int64_t)bf_q;
acc = (int64_t)bf_r;
}
}
"#;

/// `rt_lowbits`: `T4` = its low `T6` bits, by shifting them up to the top
/// and reading them back a bit at a time into `T0`, the last (`T4`'s lowest)
/// through `T3`. A count from 64 up, or below 0, is left to the routine.
const LOWBITS: &str = r#"{
int64_t bf_m = ptr[7];
if (bf_m < 0 || bf_m > 63) {
ORIGINAL
} else {
uint64_t bf_v = (uint64_t)ptr[5];
uint64_t bf_low = bf_v & ((1ull << bf_m) - 1);
ptr[1] = (int64_t)bf_low;
ptr[2] = 0;
ptr[3] = 0;
if (bf_m > 0) {
ptr[4] = (int64_t)(bf_v & 1);
}
ptr[5] = (int64_t)bf_low;
acc = (int64_t)bf_low;
}
}
"#;

/// `rt_rsh` and `rt_rshu`: `T4 >>= T5`, for `T5 > 0`, reading the result's
/// bits from the top (of `!T4`, for a negative one shifted arithmetically)
/// into `T0`, the last through `T3`, while `T1` (2^`T5`) doubles up to 0.
/// Counting `T1` up stops at 64, leaving `T5 - 64`, with `T3` 1 if that's
/// more than 0.
fn rsh(arithmetic: bool) -> String {
    // (`!(!x >> n)` is `x >> n` shifted arithmetically)
    let (neg, u, r) = if arithmetic {
        ("int64_t bf_neg = bf_v < 0;\n", "bf_neg ? ~(uint64_t)bf_v : (uint64_t)bf_v", "bf_c <= 63 ? bf_v >> bf_c : -bf_neg")
    } else {
        ("", "(uint64_t)bf_v", "(int64_t)bf_s")
    };
    format!(
        r#"{{
int64_t bf_v = ptr[5], bf_c = ptr[6];
if (bf_c > 0) {{
{neg}uint64_t bf_u = {u};
uint64_t bf_s = bf_c <= 63 ? bf_u >> bf_c : 0;
int64_t bf_r = {r};
ptr[1] = bf_r;
ptr[2] = 0;
{}ptr[4] = bf_c <= 63 ? (int64_t)(bf_s & 1) : (int64_t)(bf_c > 64);
ptr[5] = bf_r;
ptr[6] = bf_c <= 63 ? 0 : bf_c - 64;
}} else {{
ptr[4] = 0;
}}
ptr[10] = 1;
acc = 0;
}}
"#,
        if arithmetic { "ptr[3] = bf_neg;\n" } else { "" }
    )
}

/// `rt_lsh`: `T0 <<= T1` a doubling at a time, counting `T1` down, while it's
/// above 0 and `T0` isn't 0; `T2` is left as the last check's sum of those
/// two conditions.
const LSH: &str = r#"{
int64_t bf_v = ptr[1], bf_c = ptr[2];
if (bf_c > 0 && bf_v != 0) {
/* (doubling stops once it's 0, which shifting by the count, or more, also
   gives) */
uint64_t bf_w = bf_c >= 64 ? 0 : (uint64_t)bf_v << bf_c;
int64_t bf_most = 64 - __builtin_ctzll((uint64_t)bf_v);
int64_t bf_left = bf_c > bf_most ? bf_c - bf_most : 0;
ptr[1] = (int64_t)bf_w;
ptr[2] = bf_left;
ptr[3] = (int64_t)(bf_left > 0) + (int64_t)(bf_w != 0);
} else {
ptr[3] = (int64_t)(bf_c > 0) + (int64_t)(bf_v != 0);
}
acc = 0;
}
"#;

/// `rt_and`, `rt_or` and `rt_xor`: `T2 = T0 op T1`, a bit at a time from
/// the top, shifting `T0` and `T1` out (to 0); the last pass leaves the two
/// lowest bits' sum combined in `T4`, and `T5` as `T1`'s lowest bit (for
/// `or`) or as `T4`.
fn bitwise(op: &str) -> String {
    let tmp = if op == "|" { "bf_b & 1" } else { "(bf_a OP bf_b) & 1" };
    format!(
        r#"{{
uint64_t bf_a = (uint64_t)ptr[1], bf_b = (uint64_t)ptr[2];
ptr[1] = 0;
ptr[2] = 0;
ptr[3] = (int64_t)(bf_a OP bf_b);
ptr[4] = 0;
ptr[5] = (int64_t)((bf_a OP bf_b) & 1);
ptr[6] = (int64_t)({tmp});
acc = 0;
}}
"#
    )
    .replace("OP", op)
}

/// `rt_andk`, `rt_ork` and `rt_xork`: `T4 op= T5` on the low `T6` bits (the
/// ones above are cleared by `and`, and kept by the others), shifting both
/// up to the top and combining them a bit at a time: `T0` gets `T4`'s low
/// bits, `T8` the combined ones, and the last pass leaves the two lowest
/// bits' sum in `T11` and `T4`'s lowest bit (or, for `xor`, that sum's) in
/// `T3`. A count from 64 up, or below 0, is left to the routine.
fn bits_with_small(op: &str) -> String {
    let top = if op == "^" { "(bf_x ^ bf_k) & 1" } else { "bf_x & 1" };
    let result = if op == "&" { "bf_new" } else { "bf_x - bf_low + bf_new" };
    format!(
        r#"{{
int64_t bf_m = ptr[7];
if (bf_m < 0 || bf_m > 63) {{
ORIGINAL
}} else {{
uint64_t bf_x = (uint64_t)ptr[5], bf_k = (uint64_t)ptr[6];
uint64_t bf_mask = (1ull << bf_m) - 1;
uint64_t bf_low = bf_x & bf_mask, bf_new = (bf_x {op} bf_k) & bf_mask;
int64_t bf_result = (int64_t)({result});
ptr[1] = (int64_t)bf_low;
ptr[2] = 0;
ptr[3] = 0;
if (bf_m > 0) {{
ptr[4] = (int64_t)({top});
ptr[12] = (int64_t)((bf_x & 1) + (bf_k & 1));
}}
ptr[5] = bf_result;
ptr[6] = 0;
ptr[8] = 0;
ptr[9] = (int64_t)bf_new;
acc = bf_result;
}}
}}
"#
    )
}

/// `rt_divs`: `T2 = T0 / T1` and `T0 = T0 % T1`, signed (the remainder
/// with the dividend's sign), by `rt_divu` on the magnitudes (left in `T12`
/// and `T13`, `T1` keeping the divisor's), with the signs in `T3` and `T4`.
/// Dividing by 0 gives -1 and leaves the rest. `T9` is the `if`'s flag.
fn divs() -> String {
    format!(
        r#"{{
int64_t bf_sa = ptr[1], bf_sb = ptr[2];
if (bf_sb == 0) {{
ptr[3] = -1;
ptr[10] = 1;
acc = 0;
}} else {{
int64_t bf_an = bf_sa < 0, bf_bn = bf_sb < 0;
uint64_t bf_ua = bf_an ? 0 - (uint64_t)bf_sa : (uint64_t)bf_sa, bf_ub = bf_bn ? 0 - (uint64_t)bf_sb : (uint64_t)bf_sb;
ptr[2] = (int64_t)bf_ub;
ptr[4] = bf_an;
ptr[5] = bf_bn;
ptr[13] = (int64_t)bf_ua;
ptr[14] = (int64_t)bf_ub;
{}uint64_t bf_q = (uint64_t)ptr[15], bf_r = (uint64_t)ptr[13];
if (bf_an) {{
bf_q = 0 - bf_q;
bf_r = 0 - bf_r;
}}
if (bf_bn) {{
bf_q = 0 - bf_q;
}}
ptr[1] = (int64_t)bf_r;
ptr[3] = (int64_t)bf_q;
ptr[10] = 0;
acc = 0;
}}
}}
"#,
        // (the divisor isn't 0)
        DIVU.replace("ORIGINAL", "__builtin_unreachable();")
    )
}

/// The routines the target knows, as `asm` writes them now.
pub fn idioms() -> Vec<Idiom> {
    let (x, y): (&Location, &Location) = (asm::R1, asm::R2);
    let builds: [fn(&mut Vec<Op>, &Location, &Location); 16] = [
        |o, x, y| asm::mul_assign(o, x, y),
        |o, x, y| asm::lt_assign(o, x, y),
        |o, x, y| asm::ltu_assign(o, x, y),
        |o, x, y| asm::divu_assign(o, x, y),
        |o, x, y| asm::divu_small_assign(o, x, y),
        |o, x, _| asm::and_const(o, x, 255),
        |o, x, _| asm::rsh_const(o, x, 3),
        |o, x, _| asm::rshu_const(o, x, 3),
        |o, x, _| asm::lsh_const(o, x, 20),
        |o, x, y| asm::and_assign(o, x, y),
        |o, x, y| asm::or_assign(o, x, y),
        |o, x, y| asm::xor_assign(o, x, y),
        |o, x, _| asm::and_const(o, x, 5),
        |o, x, _| asm::or_const(o, x, 5),
        |o, x, _| asm::xor_const(o, x, 5),
        |o, x, y| asm::div_assign(o, x, y),
    ];
    let mut routines = HashMap::new();
    for build in builds {
        routines.extend(defined(|o| build(o, x, y)));
    }
    // (counts that are cells the routine counts down to 0 must be small)
    let count7 = "c[7] = (int64_t)(bf_rand() % 72);";
    let natives: [(&str, String, &str); 16] = [
        ("rt_mul", MUL.into(), ""),
        ("rt_less", LESS.into(), ""),
        ("rt_lessu", LESSU.into(), ""),
        ("rt_divu", DIVU.into(), ""),
        ("rt_divuk", DIVUK.into(), ""),
        ("rt_lowbits", LOWBITS.into(), count7),
        ("rt_rsh", rsh(true), ""),
        ("rt_rshu", rsh(false), ""),
        ("rt_lsh", LSH.into(), ""),
        ("rt_and", bitwise("&"), ""),
        ("rt_or", bitwise("|"), ""),
        ("rt_xor", bitwise("^"), ""),
        ("rt_andk", bits_with_small("&"), count7),
        ("rt_ork", bits_with_small("|"), count7),
        ("rt_xork", bits_with_small("^"), count7),
        ("rt_divs", divs(), ""),
    ];
    let mut out = vec![];
    for (label, native, tame) in natives {
        if let Some(body) = routines.remove(label) {
            out.push(Idiom { label: label.to_string(), body, native, tame });
        }
    }
    out
}
