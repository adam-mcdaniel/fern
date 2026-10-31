//! What each operation computes, matching the asm helpers. The interpreter
//! uses this directly, and constant folding uses it where the result doesn't
//! depend on which of the module's target widths the program runs on.

use super::{BinOp, UnOp};

/// Sign-extends the low `xlen` bits of `v`.
pub(super) fn wrap(v: i64, xlen: u32) -> i64 {
    let shift = 64 - xlen;
    (v << shift) >> shift
}

/// The low `xlen` bits of `v`, read as unsigned.
pub(super) fn unsigned(v: i64, xlen: u32) -> u64 {
    (v as u64) & (u64::MAX >> (64 - xlen))
}

/// `a op b` on `xlen`-bit cells, for `a` and `b` already wrapped to `xlen` bits.
pub(super) fn binary(op: BinOp, a: i64, b: i64, xlen: u32) -> i64 {
    use BinOp::*;
    let w = |v: i64| wrap(v, xlen);
    let (ua, ub) = (unsigned(a, xlen), unsigned(b, xlen));
    match op {
        Add => w(a.wrapping_add(b)),
        Sub => w(a.wrapping_sub(b)),
        Mul => w(a.wrapping_mul(b)),
        Div if b == 0 => -1,
        Div => w(a.wrapping_div(b)),
        Rem if b == 0 => a,
        Rem => w(a.wrapping_rem(b)),
        DivU if ub == 0 => -1,
        DivU => w((ua / ub) as i64),
        RemU if ub == 0 => a,
        RemU => w((ua % ub) as i64),
        And => a & b,
        Or => a | b,
        Xor => a ^ b,
        Shl if b <= 0 => a,
        Shl if b >= 64 => 0,
        Shl => w(a << b),
        Shr if b <= 0 => a,
        Shr => a >> b.min(63),
        ShrU if b <= 0 => a,
        ShrU if b >= xlen as i64 => 0,
        ShrU => w((ua >> b) as i64),
        Eq => (a == b) as i64,
        Ne => (a != b) as i64,
        Lt => (a < b) as i64,
        Le => (a <= b) as i64,
        Gt => (a > b) as i64,
        Ge => (a >= b) as i64,
        LtU => (ua < ub) as i64,
        LeU => (ua <= ub) as i64,
        GtU => (ua > ub) as i64,
        GeU => (ua >= ub) as i64,
        Min => a.min(b),
        Max => a.max(b),
        // addresses are cell indices in the interpreter
        Index => w(a.wrapping_add(b)),
    }
}

pub(super) fn unary(op: UnOp, a: i64, xlen: u32) -> i64 {
    match op {
        UnOp::Neg => wrap(a.wrapping_neg(), xlen),
        UnOp::Not => !a,
        UnOp::LNot => (a == 0) as i64,
        UnOp::Abs => wrap(a.wrapping_abs(), xlen),
    }
}

/// Whether `v` means the same thing on every cell width from `bits` up.
fn fits(v: i64, bits: u32) -> bool {
    bits == 64 || (-(1i64 << (bits - 1))..1i64 << (bits - 1)).contains(&v)
}

/// Folds `a op b` if the result is the same on every cell width from
/// `min_width` to 64 bits. Constants are truncated to the cell width at run
/// time, so this holds for ops that work modulo 2^width, and otherwise only
/// for values that fit in the narrowest width.
pub(super) fn fold_binary(op: BinOp, a: i64, b: i64, min_width: u32) -> Option<i64> {
    use BinOp::*;
    let fits = |v: i64| fits(v, min_width);
    match op {
        Index => None,
        Add | Sub | Mul | And | Or | Xor => Some(binary(op, a, b, 64)),
        // modulo 2^width in a, as long as the shift itself means the same
        Shl if fits(b) => Some(binary(op, a, b, 64)),
        _ => {
            let unsigned_op = matches!(op, DivU | RemU | ShrU | LtU | LeU | GtU | GeU);
            if !fits(a) || !fits(b) || (unsigned_op && (a < 0 || b < 0)) {
                return None;
            }
            Some(binary(op, a, b, 64)).filter(|&r| fits(r))
        }
    }
}

pub(super) fn fold_unary(op: UnOp, a: i64, min_width: u32) -> Option<i64> {
    match op {
        UnOp::Neg | UnOp::Not => Some(unary(op, a, 64)),
        UnOp::LNot | UnOp::Abs => {
            Some(unary(op, a, 64)).filter(|&r| fits(a, min_width) && fits(r, min_width))
        }
    }
}
