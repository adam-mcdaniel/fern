//! Backend for the CPU in `hw/`: compiles ops to its byte-coded machine code.
//!
//! Every instruction is one byte: a 4-bit opcode and a 4-bit operand nibble.
//! Wider operands are built up in the CPU's operand register by `PFX`/`NFX`
//! prefix bytes (the Transputer scheme), so most instructions stay one byte.
//! See `hw/README.md` for the full ISA.

use crate::Op;
use std::collections::HashMap;

pub const PFX: u8 = 0x0; // O = (O | n) << 4
pub const NFX: u8 = 0x1; // O = !(O | n) << 4
pub const LIT: u8 = 0x2; // A = O | n
pub const MOV: u8 = 0x3; // P += O | n
pub const JZ: u8 = 0x4; // if A == 0 { PC += O | n }  (relative to the next instruction)
pub const JNZ: u8 = 0x5; // if A != 0 { PC += O | n }
pub const OPR: u8 = 0x6; // operand selects one of the zero-operand ops below

pub const HALT: i64 = 0;
pub const LOAD: i64 = 1; // $
pub const STORE: i64 = 2; // =
pub const ADD: i64 = 3; // +
pub const NEG: i64 = 4; // -
pub const POS: i64 = 5; // #
pub const WHERE: i64 = 6; // ?
pub const DEREF: i64 = 7; // *
pub const REFER: i64 = 8; // &
pub const CALL: i64 = 9; // !
pub const RET: i64 = 10; // ;
pub const READ: i64 = 11; // ,
pub const WRITE: i64 = 12; // .

/// Appends the shortest encoding of `op` with operand `v`.
fn encode(op: u8, v: i64, out: &mut Vec<u8>) {
    if (0..16).contains(&v) {
        out.push(op << 4 | v as u8);
        return;
    }
    if v >= 16 {
        encode(PFX, v >> 4, out);
    } else {
        encode(NFX, !v >> 4, out);
    }
    out.push(op << 4 | (v & 15) as u8);
}

fn encoded_len(op: u8, v: i64) -> usize {
    let mut buf = Vec::new();
    encode(op, v, &mut buf);
    buf.len()
}

enum Operand {
    Imm(i64),
    /// Absolute address of a symbol.
    Abs(usize),
    /// Offset from the end of this instruction to a symbol.
    Rel(usize),
}

enum Item {
    Ins(u8, Operand),
    /// Defines a symbol at the current address.
    Mark(usize),
}

#[derive(Default)]
struct Symbols {
    names: Vec<Option<String>>,
    by_name: HashMap<String, usize>,
    defined: Vec<bool>,
}

impl Symbols {
    fn named(&mut self, name: &str) -> usize {
        if let Some(&id) = self.by_name.get(name) {
            return id;
        }
        let id = self.anon();
        self.names[id] = Some(name.to_string());
        self.by_name.insert(name.to_string(), id);
        id
    }

    fn anon(&mut self) -> usize {
        self.names.push(None);
        self.defined.push(false);
        self.names.len() - 1
    }
}

fn label_name(s: &[u8; 16]) -> String {
    s.iter().take_while(|c| **c != 0).map(|c| *c as char).collect()
}

/// Reinterprets the low `xlen` bits of `v` as a signed value.  The CPU
/// computes operands modulo 2^XLEN, so this picks the shortest encoding
/// (e.g. 0xFFFF on a 16-bit core is encoded as -1).
fn wrap(v: i64, xlen: u32) -> i64 {
    let shift = 64 - xlen;
    (v << shift) >> shift
}

/// Compiles a program to machine code for a CPU with `xlen`-bit cells.
///
/// Layout matches the C backend: top-level code runs first and ends in
/// `HALT`; function bodies (`@name: ... ;`) are placed after it.
pub fn assemble(ops: &[Op], xlen: u32) -> Result<Vec<u8>, String> {
    if !(8..=64).contains(&xlen) {
        return Err(format!("unsupported cell width {xlen} (must be 8 to 64)"));
    }
    use Op::*;
    let mut syms = Symbols::default();
    let mut main = vec![];
    let mut funcs = vec![];
    let mut in_func = false;
    let mut last_label: Option<String> = None;
    let mut loops: Vec<(usize, usize)> = vec![];

    for op in ops {
        let out = if in_func { &mut funcs } else { &mut main };
        let opr = |n| Item::Ins(OPR, Operand::Imm(n));
        match op {
            Deref => out.push(opr(DEREF)),
            Refer => out.push(opr(REFER)),
            Where => out.push(opr(WHERE)),
            Move(n) => out.push(Item::Ins(MOV, Operand::Imm(*n))),
            Set(n) => out.push(Item::Ins(LIT, Operand::Imm(*n as i64))),
            Label(s) => {
                let name = label_name(s);
                out.push(Item::Ins(LIT, Operand::Abs(syms.named(&name))));
                last_label = Some(name);
            }
            Load => out.push(opr(LOAD)),
            Store => out.push(opr(STORE)),
            Call => out.push(opr(CALL)),
            Read => out.push(opr(READ)),
            Write => out.push(opr(WRITE)),
            Add => out.push(opr(ADD)),
            Neg => out.push(opr(NEG)),
            Positive => out.push(opr(POS)),
            While => {
                let (start, end) = (syms.anon(), syms.anon());
                out.push(Item::Ins(JZ, Operand::Rel(end)));
                out.push(Item::Mark(start));
                loops.push((start, end));
            }
            EndWhile => {
                let (start, end) = loops.pop().ok_or("unmatched ']'")?;
                out.push(Item::Ins(JNZ, Operand::Rel(start)));
                out.push(Item::Mark(end));
            }
            Func => {
                if in_func {
                    return Err("nested function definition".into());
                }
                if !loops.is_empty() {
                    return Err("function defined inside a loop".into());
                }
                let name = last_label.clone().ok_or("':' without a preceding @label")?;
                let id = syms.named(&name);
                if syms.defined[id] {
                    return Err(format!("function @{name} defined twice"));
                }
                syms.defined[id] = true;
                funcs.push(Item::Mark(id));
                in_func = true;
            }
            EndFunc => {
                if !in_func {
                    return Err("';' outside a function".into());
                }
                if !loops.is_empty() {
                    return Err("unmatched '[' in function".into());
                }
                funcs.push(opr(RET));
                in_func = false;
            }
        }
    }
    if in_func {
        return Err("unterminated function (missing ';')".into());
    }
    if !loops.is_empty() {
        return Err("unmatched '['".into());
    }
    for item in main.iter().chain(&funcs) {
        if let Item::Mark(id) = item {
            syms.defined[*id] = true;
        }
    }
    let undefined: Vec<_> = (0..syms.names.len())
        .filter(|&id| !syms.defined[id])
        .filter_map(|id| syms.names[id].as_deref().map(|n| format!("@{n}")))
        .collect();
    if !undefined.is_empty() {
        return Err(format!("undefined labels: {}", undefined.join(", ")));
    }

    let mut items = main;
    items.push(Item::Ins(OPR, Operand::Imm(HALT)));
    items.append(&mut funcs);
    let code = link(&items, syms.names.len(), xlen);
    if xlen < 64 && code.len() as u64 > 1 << xlen {
        return Err(format!(
            "program is {} bytes, but {xlen}-bit cells can only address {} bytes of code",
            code.len(),
            1u64 << xlen
        ));
    }
    Ok(code)
}

/// Lays out `items`, growing symbolic operands until every one fits.
fn link(items: &[Item], nsyms: usize, xlen: u32) -> Vec<u8> {
    let mut sizes: Vec<usize> = items
        .iter()
        .map(|item| match item {
            Item::Ins(op, Operand::Imm(v)) => encoded_len(*op, wrap(*v, xlen)),
            Item::Ins(..) => 1,
            Item::Mark(_) => 0,
        })
        .collect();
    let mut addrs = vec![0i64; items.len()];
    let mut sym_addrs = vec![0i64; nsyms];

    let value = |i: usize, operand: &Operand, addrs: &[i64], sizes: &[usize], sym_addrs: &[i64]| {
        let v = match operand {
            Operand::Imm(v) => *v,
            Operand::Abs(s) => sym_addrs[*s],
            Operand::Rel(s) => sym_addrs[*s] - (addrs[i] + sizes[i] as i64),
        };
        wrap(v, xlen)
    };

    // Sizes only ever grow, so this terminates.
    loop {
        let mut addr = 0;
        for (i, item) in items.iter().enumerate() {
            addrs[i] = addr;
            if let Item::Mark(s) = item {
                sym_addrs[*s] = addr;
            }
            addr += sizes[i] as i64;
        }
        let mut changed = false;
        for (i, item) in items.iter().enumerate() {
            if let Item::Ins(op, operand) = item {
                let need = encoded_len(*op, value(i, operand, &addrs, &sizes, &sym_addrs));
                if need > sizes[i] {
                    sizes[i] = need;
                    changed = true;
                }
            }
        }
        if !changed {
            break;
        }
    }

    let mut code = vec![];
    for (i, item) in items.iter().enumerate() {
        if let Item::Ins(op, operand) = item {
            let mut bytes = vec![];
            encode(*op, value(i, operand, &addrs, &sizes, &sym_addrs), &mut bytes);
            // A leading `PFX 0` leaves the operand register at 0, so it pads
            // an encoding out to the size the layout reserved for it.
            code.resize(code.len() + sizes[i] - bytes.len(), PFX << 4);
            code.extend(bytes);
        }
    }
    code
}

/// Formats machine code for Verilog's `$readmemh`, one byte per line.
pub fn to_hex(code: &[u8]) -> String {
    code.iter().map(|b| format!("{b:02x}\n")).collect()
}

#[cfg(test)]
mod tests {
    use super::*;

    /// Decodes a prefix sequence the way the hardware does.
    fn decode(bytes: &[u8]) -> (u8, i64) {
        let mut o: i64 = 0;
        for (i, b) in bytes.iter().enumerate() {
            let (op, n) = (b >> 4, (b & 15) as i64);
            match op {
                PFX => o = (o | n) << 4,
                NFX => o = !(o | n) << 4,
                _ => {
                    assert_eq!(i, bytes.len() - 1);
                    return (op, o | n);
                }
            }
        }
        panic!("no terminating instruction");
    }

    #[test]
    fn operands_round_trip() {
        for v in [0, 1, 15, 16, 255, 256, -1, -15, -16, -17, -300, 1 << 40, i64::MAX, i64::MIN] {
            let mut bytes = vec![];
            encode(LIT, v, &mut bytes);
            assert_eq!(decode(&bytes), (LIT, v), "{v}");
            // Padding with PFX 0 must not change the value.
            bytes.insert(0, 0x00);
            assert_eq!(decode(&bytes), (LIT, v), "padded {v}");
        }
    }

    #[test]
    fn loops_and_functions_link() {
        let ops = crate::parse("@f: 65. ; 3[@f! 1-=$+ $]").unwrap();
        assert!(assemble(&ops, 64).is_ok());
        let ops = crate::parse("@g!").unwrap();
        assert_eq!(assemble(&ops, 64).unwrap_err(), "undefined labels: @g");
    }

    #[test]
    fn narrow_cells_wrap_operands() {
        let ops = crate::parse("0xFFFF").unwrap();
        // PFX F, PFX F, PFX F, LIT F, then HALT.
        assert_eq!(assemble(&ops, 64).unwrap(), vec![0x0f, 0x0f, 0x0f, 0x2f, 0x60]);
        // On a 16-bit core 0xFFFF is -1: NFX 0, LIT 15, then HALT.
        assert_eq!(assemble(&ops, 16).unwrap(), vec![0x10, 0x2f, 0x60]);
        // 300 bytes of code cannot be addressed by 8-bit cells.
        let ops = crate::parse(&"65.".repeat(100)).unwrap();
        assert!(assemble(&ops, 8).is_err());
    }
}
