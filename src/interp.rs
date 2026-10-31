//! A reference interpreter for `Op`, for testing programs without a C compiler
//! or the CPU simulator.
//!
//! Addresses from `?` are `base + index * stride`, so the same program can be
//! checked against the CPU's model (`stride` 1: addresses are cell indices) and
//! the C backend's (`stride` 8: addresses are byte addresses).
//!
//! Cells and the accumulator are `xlen` bits wide, like the CPU's `XLEN`: all
//! arithmetic wraps modulo 2^xlen and `#` compares as a signed xlen-bit value.
//! Values are stored sign-extended to `i64`.
//!
//! A label the program doesn't define names an external function, which the
//! C backend links against: `void name(int64_t **tape, int64_t **ptr,
//! int64_t *acc)`, which `!` calls with the machine's tape, pointer and
//! accumulator. Here, `externs` can give it in Rust instead, as a host
//! function, which gets the same three things. One is always here, as it is
//! in the C backends: `bf_exit`, which stops the program, with the status
//! in the cell the pointer's at (what an aborting program calls: see
//! `ir::Options::exits`).

use crate::ir::EXIT;
use crate::Op;
use std::collections::HashMap;
use std::rc::Rc;

/// Memory, as a host function sees it: by address, in whichever model
/// addresses are.
pub trait Memory {
    fn load(&self, addr: i64) -> Result<i64, String>;
    fn store(&mut self, addr: i64, value: i64) -> Result<(), String>;
    /// The address `i` cells on from `addr`.
    fn index(&self, addr: i64, i: i64) -> i64;
}

/// A call to a host function: what a C function the program calls gets,
/// `void name(int64_t **tape, int64_t **ptr, int64_t *acc)`.
pub struct HostCall<'a> {
    /// The tape, by address.
    pub tape: &'a mut dyn Memory,
    /// The address of the cell the pointer is at, which the function can
    /// move it from.
    pub ptr: i64,
    pub acc: i64,
    /// What the program has printed, which the host function can add to.
    pub output: &'a mut Vec<u8>,
}

impl HostCall<'_> {
    /// The cell `i` cells on from the one the pointer is at: the `i`th
    /// argument, for a call the IR makes.
    pub fn arg(&self, i: i64) -> Result<i64, String> {
        self.tape.load(self.tape.index(self.ptr, i))
    }

    /// The string at `addr`: its length, then a cell for each character.
    pub fn string(&self, addr: i64) -> Result<String, String> {
        let n = self.tape.load(addr)?;
        (1..=n).map(|i| Ok(self.tape.load(self.tape.index(addr, i))? as u8 as char)).collect()
    }

    /// Writes `text` as a string into the cells at `addr`, which has room
    /// for `capacity` characters, and gives how many it wrote.
    pub fn fill(&mut self, addr: i64, capacity: i64, text: &[u8]) -> Result<i64, String> {
        let n = (text.len() as i64).min(capacity);
        self.tape.store(addr, n)?;
        for (i, &b) in text.iter().take(n as usize).enumerate() {
            let at = self.tape.index(addr, i as i64 + 1);
            self.tape.store(at, b as i64)?;
        }
        Ok(n)
    }
}

/// A function written in Rust that a program can call as an external one.
#[derive(Clone)]
pub struct HostFn {
    pub run: Rc<dyn Fn(&mut HostCall) -> Result<(), String>>,
}

impl HostFn {
    pub fn new(run: impl Fn(&mut HostCall) -> Result<(), String> + 'static) -> HostFn {
        HostFn { run: Rc::new(run) }
    }
}

/// The tape, as a host function sees it.
struct Tape<'a> {
    cells: &'a mut [i64],
    base: i64,
    stride: i64,
}

impl Memory for Tape<'_> {
    fn load(&self, addr: i64) -> Result<i64, String> {
        Ok(self.cells[self.cell(addr)?])
    }
    fn store(&mut self, addr: i64, value: i64) -> Result<(), String> {
        let c = self.cell(addr)?;
        self.cells[c] = value;
        Ok(())
    }
    fn index(&self, addr: i64, i: i64) -> i64 {
        addr.wrapping_add(i.wrapping_mul(self.stride))
    }
}

impl Tape<'_> {
    fn cell(&self, addr: i64) -> Result<usize, String> {
        let offset = addr.wrapping_sub(self.base);
        if offset % self.stride != 0 {
            return Err(format!("misaligned address {addr}"));
        }
        usize::try_from(offset / self.stride).ok().filter(|&c| c < self.cells.len()).ok_or(format!("address {addr} off the tape"))
    }
}

pub struct Machine {
    /// Address of cell 0.
    pub base: i64,
    /// Address distance between neighbouring cells.
    pub stride: i64,
    /// Tape length. Capped at 2^xlen, the most cells an address can reach.
    pub cells: usize,
    /// Cell width in bits, 8 to 64.
    pub xlen: u32,
    /// Gives up after this many ops, to catch infinite loops.
    pub max_steps: u64,
    /// External functions, by label.
    pub externs: HashMap<String, HostFn>,
    /// Cells no pointer may lead to: a program that takes the pointer to
    /// one through a `*` (before the `&` that undoes it) stops with an
    /// error. For checking that a program keeps the promise it makes to
    /// `asm::opt` (`Facts::private`).
    pub guarded: std::ops::Range<usize>,
}

impl Machine {
    /// Addresses like the CPU in `hw/`, with 64-bit cells.
    pub fn cpu() -> Self {
        Self { base: 0, stride: 1, cells: 1 << 16, xlen: 64, max_steps: 1 << 28, externs: HashMap::new(), guarded: 0..0 }
    }

    /// The CPU in `hw/` built with `xlen`-bit cells.
    pub fn cpu_xlen(xlen: u32) -> Self {
        Self { xlen, ..Self::cpu() }
    }

    /// Addresses like the C backend's byte addresses for an `int64_t` tape.
    pub fn c() -> Self {
        Self { base: 0x7f00_0000_1000, stride: 8, ..Self::cpu() }
    }

    /// Sign-extends the low `xlen` bits of `v`.
    fn wrap(&self, v: i64) -> i64 {
        let shift = 64 - self.xlen;
        (v << shift) >> shift
    }

    /// The low `xlen` bits of `v`, read as unsigned.
    fn unsigned(&self, v: i64) -> u64 {
        (v as u64) & (u64::MAX >> (64 - self.xlen))
    }

    /// Gives the external function with this label, run by `run`.
    pub fn host(mut self, label: &str, f: HostFn) -> Self {
        self.externs.insert(label.to_string(), f);
        self
    }
}

pub struct Halted {
    pub output: Vec<u8>,
    pub tape: Vec<i64>,
    /// How many ops ran.
    pub steps: u64,
    /// What it stopped with: 0, unless it called `bf_exit`.
    pub status: i64,
}

impl Machine {
    pub fn run(&self, ops: &[Op], input: &[u8]) -> Result<Halted, String> {
        if !(8..=64).contains(&self.xlen) {
            return Err(format!("unsupported cell width {} (must be 8 to 64)", self.xlen));
        }
        let cells = match 1usize.checked_shl(self.xlen) {
            Some(max) => self.cells.min(max),
            None => self.cells,
        };

        // match brackets and function bodies, and find each function's start
        let mut pair = vec![0; ops.len()];
        let mut open = vec![];
        let mut funcs = HashMap::new();
        let mut last_label = None;
        for (i, op) in ops.iter().enumerate() {
            match op {
                Op::While | Op::Func => open.push(i),
                Op::EndWhile | Op::EndFunc => {
                    let j = open.pop().ok_or(format!("unmatched close at op {i}"))?;
                    pair[i] = j;
                    pair[j] = i;
                }
                Op::Label(name) => last_label = Some(*name),
                _ => {}
            }
            if let Op::Func = op {
                let name = last_label.ok_or("function without a label")?;
                if self.unsigned(i as i64 + 1) != i as u64 + 1 {
                    return Err(format!("function at op {i} is past what {}-bit cells can address", self.xlen));
                }
                funcs.insert(name, i + 1);
            }
        }
        if !open.is_empty() {
            return Err("unmatched open".into());
        }

        let mut tape = vec![0i64; cells];
        // (and `bf_exit`, after them, unless the program gives its own)
        let mut externs: Vec<String> = self.externs.keys().cloned().collect();
        if !self.externs.contains_key(EXIT) {
            externs.push(EXIT.to_string());
        }
        let (mut acc, mut p, mut pc) = (0i64, 0usize, 0usize);
        let (mut pointers, mut returns) = (vec![], vec![]);
        let mut input = input.iter();
        let mut output = vec![];
        let mut steps = 0;
        let cell = |p: usize| if p < cells { Ok(p) } else { Err(format!("pointer {p} off the tape")) };

        while pc < ops.len() {
            steps += 1;
            if steps > self.max_steps {
                return Err("step limit reached".into());
            }
            let mut next = pc + 1;
            match &ops[pc] {
                Op::Deref => {
                    pointers.push(p);
                    let offset = self.unsigned(tape[p].wrapping_sub(self.base));
                    if offset % self.stride as u64 != 0 {
                        return Err(format!("misaligned pointer {}", tape[p]));
                    }
                    p = cell((offset / self.stride as u64) as usize)?;
                    if self.guarded.contains(&p) {
                        return Err(format!("a pointer to cell {p}, which no pointer may lead to"));
                    }
                }
                Op::Refer => p = pointers.pop().ok_or("pointer stack underflow")?,
                Op::Where => acc = self.wrap(self.base.wrapping_add(p as i64 * self.stride)),
                Op::Move(n) => {
                    p = cell(p.wrapping_add(*n as usize))?;
                    if !pointers.is_empty() && self.guarded.contains(&p) {
                        return Err(format!("through a pointer to cell {p}, which no pointer may lead to"));
                    }
                }
                Op::Set(n) => acc = self.wrap(*n as i64),
                Op::Label(name) => match funcs.get(name) {
                    Some(start) => acc = self.wrap(*start as i64),
                    // an external function: an address past the program's
                    // end, which no function starts at
                    None => {
                        let text: String = name.iter().take_while(|&&c| c != 0).map(|&c| c as char).collect();
                        let i = externs.iter().position(|e| *e == text).ok_or(format!("call to `{text}`, which isn't defined"))?;
                        let at = (ops.len() + i) as i64;
                        if self.unsigned(at) != at as u64 {
                            return Err(format!("`{text}` is past what {}-bit cells can address", self.xlen));
                        }
                        acc = self.wrap(at);
                    }
                },
                Op::Load => acc = tape[p],
                Op::Store => tape[p] = acc,
                Op::Call if self.unsigned(acc) as usize >= ops.len() => {
                    let i = self.unsigned(acc) as usize - ops.len();
                    let name = externs.get(i).ok_or("call to an address past the program")?;
                    if !self.externs.contains_key(name) {
                        // (`bf_exit`: the status is its argument)
                        return Ok(Halted { output, steps, status: tape[p], tape });
                    }
                    let host = &self.externs[name];
                    let at = self.base.wrapping_add(p as i64 * self.stride);
                    let mut memory = Tape { cells: &mut tape, base: self.base, stride: self.stride };
                    let mut call = HostCall { tape: &mut memory, ptr: at, acc, output: &mut output };
                    (host.run)(&mut call)?;
                    let (ptr, result) = (call.ptr, call.acc);
                    acc = self.wrap(result);
                    p = memory.cell(ptr)?;
                }
                Op::Call => {
                    returns.push(next);
                    next = self.unsigned(acc) as usize;
                }
                Op::Read => acc = self.wrap(input.next().map_or(-1, |b| *b as i64)),
                Op::Write => output.push(acc as u8),
                Op::Add => acc = self.wrap(acc.wrapping_add(tape[p])),
                Op::Neg => acc = self.wrap(acc.wrapping_neg()),
                Op::Positive => acc = (acc > 0) as i64,
                Op::While if acc == 0 => next = pair[pc] + 1,
                Op::EndWhile if acc != 0 => next = pair[pc] + 1,
                Op::While | Op::EndWhile => {}
                // reached by falling through: skip the body
                Op::Func => next = pair[pc] + 1,
                Op::EndFunc => next = returns.pop().ok_or("return outside a call")?,
            }
            pc = next;
        }
        Ok(Halted { output, tape, steps, status: 0 })
    }
}
