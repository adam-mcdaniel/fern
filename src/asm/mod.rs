//! Helpers that build programs out of `Op`s, like an assembler with macros.
//!
//! Locations are cells relative to the start of the tape: the registers
//! (`R0` to `R9`, `SP`, `FP`, `GP`) and cells reached through pointers
//! (`Location::deref`). Every helper starts and ends with the tape pointer at
//! cell 0, so helpers can be combined freely.
//!
//! The private `T` registers are scratch space, and any helper may overwrite
//! them. The heavier helpers (multiplication, division, printing, ...) are
//! shared routines: the first use defines a function in the program, and
//! every use calls it.
//!
//! Control flow (`begin_if`, `begin_loop`, functions) is tracked per thread
//! while a program is built, so build one program at a time on each thread.

use crate::Op;
use std::cell::RefCell;

const fn reg(loc: u64) -> Location {
    Location::Static(StaticLocation(loc))
}

pub const NULL: &Location = &reg(0);
const T0: &Location = &reg(1);
const T1: &Location = &reg(2);
const T2: &Location = &reg(3);
const T3: &Location = &reg(4);
const T4: &Location = &reg(5);
const T5: &Location = &reg(6);
const T6: &Location = &reg(7);
const T7: &Location = &reg(8);
const T8: &Location = &reg(9);
const T9: &Location = &reg(10);
const T10: &Location = &reg(11);
const T11: &Location = &reg(12);
const T12: &Location = &reg(13);
const T13: &Location = &reg(14);
const T14: &Location = &reg(15);
pub const SP: &Location = &reg(16);
pub const FP: &Location = &reg(17);
/// The heap pointer: the lowest cell `heap_alloc` has handed out.
pub const GP: &Location = &reg(18);
pub const R0: &Location = &reg(19);
pub const R1: &Location = &reg(20);
pub const R2: &Location = &reg(21);
pub const R3: &Location = &reg(22);
pub const R4: &Location = &reg(23);
pub const R5: &Location = &reg(24);
pub const R6: &Location = &reg(25);
pub const R7: &Location = &reg(26);
pub const R8: &Location = &reg(27);
pub const R9: &Location = &reg(28);
/// 1 while the current function runs, and 0 once `ret` has been reached.
const FUNC_RUN: &Location = &reg(29);
/// Flags for `begin_loop` loops, two per nesting level within a function:
/// `run`, cleared for the rest of an iteration by break and continue, and
/// `go`, cleared by break.
const LOOP_FLAGS: u64 = 30;
const MAX_LOOP_DEPTH: u64 = 8;
/// The first cell of the stack.
pub(crate) const STACK_BASE: u64 = 48;
pub const STACK_START: &Location = &reg(STACK_BASE);
/// The tape size `init` assumes: the default for the CPU in `hw/`.
pub const DEFAULT_CELLS: u64 = 4096;

/// The header for C functions that programs for the VM call (`bf.h`):
/// `BF_FUNCTION(name)` for ones that use the machine directly, and
/// `BF_EXTERN(ret, name, (type, param)...)` for ones that take the
/// convention the IR calls external functions with (see
/// `ir::Module::external`), around a plain typed C function.
pub const C_HEADER: &str = include_str!("bf.h");

pub trait Program {
    fn op(&mut self, op: Op);
    /// Whether the program already defines a function with this label.
    fn defines(&self, label: &Op) -> bool;
}

impl Program for Vec<Op> {
    fn op(&mut self, op: Op) {
        if peephole(self, &op) {
            return;
        }
        let closes_func = op == Op::EndFunc;
        self.push(op);
        if closes_func {
            hoist_last_func(self);
        }
    }

    fn defines(&self, label: &Op) -> bool {
        self.windows(2).any(|w| &w[0] == label && w[1] == Op::Func)
    }
}

/// Simplifies `op` against the op before it, and returns true if `op` should
/// be dropped. This only ever looks at two neighbouring ops, and jumps only
/// land right after `[`, `]`, `:` or `!`, so nothing can jump between them.
fn peephole(ops: &mut Vec<Op>, op: &Op) -> bool {
    use Op::*;
    // ops whose only effect is setting acc, so they're dead if acc is set again
    let only_sets_acc = |op: &Op| matches!(op, Load | Set(_) | Where);
    let overwrites_acc = matches!(op, Load | Set(_) | Where | Read);
    match (ops.last(), op) {
        (_, Move(0)) => true,
        (Some(&Move(m)), &Move(n)) => {
            ops.pop();
            if m + n != 0 {
                ops.push(Move(m + n));
            }
            true
        }
        // the cell already holds acc
        (Some(Store), Load | Store) | (Some(Load), Store) => true,
        (Some(Positive), Positive) => true,
        (Some(Neg), Neg) => {
            ops.pop();
            true
        }
        (Some(last), _) if only_sets_acc(last) && overwrites_acc => {
            ops.pop();
            peephole(ops, op)
        }
        _ => false,
    }
}

/// Function bodies can only be compiled at the top level, so when a function
/// defined inside a loop, an `if` or another function is closed, this moves
/// it (with its label) to the start of the program. Definitions don't run
/// where they appear, so behavior is unchanged.
fn hoist_last_func(ops: &mut Vec<Op>) {
    let mut depth = 0;
    let mut func = None;
    for i in (0..ops.len()).rev() {
        match &ops[i] {
            Op::EndFunc => depth += 1,
            Op::Func => {
                depth -= 1;
                if depth == 0 {
                    func = Some(i);
                    break;
                }
            }
            _ => {}
        }
    }
    let Some(func) = func else { return };
    let with_label = |i: usize| match i.checked_sub(1).map(|j| &ops[j]) {
        Some(Op::Label(_)) if ops[i] == Op::Func => i - 1,
        _ => i,
    };
    let begin = with_label(func);

    let mut depth = 0i32;
    for op in &ops[..begin] {
        match op {
            Op::While | Op::Func => depth += 1,
            Op::EndWhile | Op::EndFunc => depth -= 1,
            _ => {}
        }
    }
    // The label at the start of a definition sets acc when execution passes
    // it, so it can only go where acc isn't in use: not just before the `[`
    // of a loop or `if` whose condition was just loaded, for instance. The
    // start of the program is always safe.
    if depth > 0 {
        let len = ops.len() - begin;
        ops.rotate_right(len);
    }
}

/// Writes `ops` as source text that `crate::parse` reads back as the same ops.
pub fn to_source(ops: &[Op]) -> String {
    let mut out = String::new();
    let mut line = 0;
    for op in ops {
        let token = match op {
            Op::Deref => "*".to_string(),
            Op::Refer => "&".to_string(),
            Op::Where => "?".to_string(),
            Op::Move(0) => continue,
            Op::Move(n) if *n > 0 => ">".repeat(*n as usize),
            Op::Move(n) => "<".repeat(n.unsigned_abs() as usize),
            Op::Set(n) => n.to_string(),
            Op::Label(name) => {
                let name: String = name.iter().take_while(|c| **c != 0).map(|c| *c as char).collect();
                format!("@{name}")
            }
            Op::Load => "$".to_string(),
            Op::Store => "=".to_string(),
            Op::Call => "!".to_string(),
            Op::Read => ",".to_string(),
            Op::Write => ".".to_string(),
            Op::Add => "+".to_string(),
            Op::Neg => "-".to_string(),
            Op::Positive => "#".to_string(),
            Op::While => "[".to_string(),
            Op::EndWhile => "]".to_string(),
            Op::Func => ":".to_string(),
            Op::EndFunc => ";".to_string(),
        };
        // separate tokens that would otherwise read as one
        let word = |c: char| c.is_ascii_alphanumeric() || c == '_';
        let joins = match (out.chars().last(), token.chars().next()) {
            (Some(a), Some(b)) => (a == b && (a == '>' || a == '<')) || (word(a) && word(b)),
            _ => false,
        };
        if line > 0 && line + token.len() > 79 {
            out.push('\n');
            line = 0;
        } else if joins {
            out.push(' ');
            line += 1;
        }
        out.push_str(&token);
        line += token.len();
    }
    out.push('\n');
    out
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub struct StaticLocation(u64);

impl StaticLocation {
    pub fn to(&self, out: &mut dyn Program) {
        out.op(Op::Move(self.0 as i64))
    }
    pub fn from(&self, out: &mut dyn Program) {
        out.op(Op::Move(-(self.0 as i64)))
    }
}

#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub enum Location {
    Offset(Box<Self>, i64),
    Deref(Box<Self>),
    Static(StaticLocation),
}

impl From<StaticLocation> for Location {
    fn from(value: StaticLocation) -> Self {
        Self::Static(value)
    }
}

impl Location {
    pub fn to(&self, out: &mut dyn Program) {
        use Location::*;
        match self {
            Offset(root, off) => {
                root.to(out);
                out.op(Op::Move(*off))
            }
            Deref(ptr) => {
                ptr.to(out);
                out.op(Op::Deref)
            }
            Static(root) => root.to(out),
        }
    }

    pub fn from(&self, out: &mut dyn Program) {
        use Location::*;
        match self {
            Offset(root, off) => {
                out.op(Op::Move(-*off));
                root.from(out);
            }
            Deref(ptr) => {
                out.op(Op::Refer);
                ptr.from(out);
            }
            Static(root) => root.from(out),
        }
    }

    /// The cell this location's value points to (see `addr_of`).
    pub fn deref(&self) -> Self {
        Location::Deref(Box::new(self.clone()))
    }

    /// The cell `n` cells after this one.
    pub fn offset(&self, n: i64) -> Self {
        Location::Offset(Box::new(self.clone()), n)
    }
}

// Basic moves and arithmetic.

pub fn add_assign(out: &mut dyn Program, dst: &Location, src: &Location) {
    src.to(out);
    out.op(Op::Load);
    src.from(out);
    dst.to(out);
    out.op(Op::Add);
    out.op(Op::Store);
    dst.from(out);
}

pub fn sub_assign(out: &mut dyn Program, dst: &Location, src: &Location) {
    src.to(out);
    out.op(Op::Load);
    out.op(Op::Neg);
    src.from(out);
    dst.to(out);
    out.op(Op::Add);
    out.op(Op::Store);
    dst.from(out);
}

pub fn mov(out: &mut dyn Program, dst: &Location, src: &Location) {
    src.to(out);
    out.op(Op::Load);
    src.from(out);
    dst.to(out);
    out.op(Op::Store);
    dst.from(out);
}

pub fn set(out: &mut dyn Program, dst: &Location, src: u64) {
    dst.to(out);
    out.op(Op::Set(src));
    out.op(Op::Store);
    dst.from(out);
}

/// Like `set`, for signed values.
pub fn set_int(out: &mut dyn Program, dst: &Location, src: i64) {
    dst.to(out);
    set_acc(out, src);
    out.op(Op::Store);
    dst.from(out);
}

pub fn dec(out: &mut dyn Program, dst: &Location) {
    add_const(out, dst, -1);
}

pub fn inc(out: &mut dyn Program, dst: &Location) {
    add_const(out, dst, 1);
}

pub fn add_const(out: &mut dyn Program, dst: &Location, k: i64) {
    dst.to(out);
    set_acc(out, k);
    out.op(Op::Add);
    out.op(Op::Store);
    dst.from(out);
}

pub fn sub_const(out: &mut dyn Program, dst: &Location, k: i64) {
    add_const(out, dst, k.wrapping_neg());
}

/// Multiplies by a constant with a fixed run of doublings and adds, wrapping
/// like `wrapping_mul`.
pub fn mul_const(out: &mut dyn Program, dst: &Location, k: i64) {
    let m = k.unsigned_abs();
    if m == 0 {
        set(out, dst, 0);
        return;
    }
    let (x, result) = (T0, T1);
    mov(out, x, dst);
    mov(out, result, x);
    for i in (0..63 - m.leading_zeros()).rev() {
        add_assign(out, result, result);
        if m >> i & 1 == 1 {
            add_assign(out, result, x);
        }
    }
    if k < 0 {
        neg_assign(out, result);
    }
    mov(out, dst, result);
}

pub fn neg_assign(out: &mut dyn Program, dst: &Location) {
    dst.to(out);
    out.op(Op::Load);
    out.op(Op::Neg);
    out.op(Op::Store);
    dst.from(out);
}

/// Bitwise not, as `-dst - 1` (two's complement).
pub fn not_assign(out: &mut dyn Program, dst: &Location) {
    dst.to(out);
    out.op(Op::Set(1));
    out.op(Op::Add);
    out.op(Op::Neg);
    out.op(Op::Store);
    dst.from(out);
}

/// Wraps like Rust's `wrapping_abs`: the most negative value has no positive
/// counterpart, so it stays as it is.
pub fn abs_assign(out: &mut dyn Program, dst: &Location) {
    is_negative(out, dst, T0);
    begin_if(out, T0);
    neg_assign(out, dst);
    end_if(out);
}

pub fn putchar(out: &mut dyn Program, src: &Location) {
    src.to(out);
    out.op(Op::Load);
    out.op(Op::Write);
    src.from(out);
}

pub fn getchar(out: &mut dyn Program, dst: &Location) {
    dst.to(out);
    out.op(Op::Read);
    out.op(Op::Store);
    dst.from(out);
}

/// Prints a string literal.
pub fn puts(out: &mut dyn Program, s: &str) {
    for b in s.bytes() {
        out.op(Op::Set(b as u64));
        out.op(Op::Write);
    }
}

// Small building blocks.

fn load(out: &mut dyn Program, src: &Location) {
    src.to(out);
    out.op(Op::Load);
    src.from(out);
}

fn store(out: &mut dyn Program, dst: &Location) {
    dst.to(out);
    out.op(Op::Store);
    dst.from(out);
}

/// Sets `acc = v`, including negative values.
fn set_acc(out: &mut dyn Program, v: i64) {
    out.op(Op::Set(v.unsigned_abs()));
    if v < 0 {
        out.op(Op::Neg);
    }
}

/// `flag = if src == 0 { zero } else { nonzero }`, tested exactly with a one-shot loop.
fn test_zero(out: &mut dyn Program, flag: &Location, src: &Location, zero: u64, nonzero: u64) {
    set(out, flag, zero);
    load(out, src);
    out.op(Op::While);
    set(out, flag, nonzero);
    out.op(Op::Set(0));
    out.op(Op::EndWhile);
}

/// `flag = (src < 0)`, exact even for the most negative value.
fn is_negative(out: &mut dyn Program, src: &Location, flag: &Location) {
    // (src != 0) - (src > 0)
    test_zero(out, flag, src, 0, 1);
    load(out, src);
    out.op(Op::Positive);
    out.op(Op::Neg);
    flag.to(out);
    out.op(Op::Add);
    out.op(Op::Store);
    flag.from(out);
}

/// `flag = (lo <= src && src <= hi)`, for small ranges.
fn in_range(out: &mut dyn Program, src: &Location, lo: i64, hi: i64, flag: &Location) {
    // src - lo + 1 > 0
    set_acc(out, 1 - lo);
    src.to(out);
    out.op(Op::Add);
    src.from(out);
    out.op(Op::Positive);
    store(out, flag);
    // hi + 1 - src > 0
    set_acc(out, -(hi + 1));
    src.to(out);
    out.op(Op::Add);
    src.from(out);
    out.op(Op::Neg);
    out.op(Op::Positive);
    // both: the two flags sum to 2
    flag.to(out);
    out.op(Op::Add);
    out.op(Op::Store);
    out.op(Op::Set(1));
    out.op(Op::Neg);
    out.op(Op::Add);
    out.op(Op::Positive);
    out.op(Op::Store);
    flag.from(out);
}

/// Leaves `acc = (a < b)`, comparing as signed or as unsigned values. Exact for
/// all values. Uses T10 and T11.
fn less(out: &mut dyn Program, a: &Location, b: &Location, unsigned: bool) {
    let (a_top, b_top) = (T10, T11);
    is_negative(out, a, a_top);
    is_negative(out, b, b_top);
    // If the top bits differ they decide it, and if they match then b - a
    // can't overflow and its sign decides it. Both at once:
    // (b - a > 0) + 2 * verdict > 0, where verdict is 1 if the top bits say
    // a < b, -1 if they say a > b, and 0 if they match.
    let (x, y) = if unsigned { (b_top, a_top) } else { (a_top, b_top) };
    // x = 2 * verdict = 2 * (x - y)
    load(out, y);
    out.op(Op::Neg);
    x.to(out);
    out.op(Op::Add);
    out.op(Op::Store);
    out.op(Op::Add);
    out.op(Op::Store);
    x.from(out);

    load(out, a);
    out.op(Op::Neg);
    b.to(out);
    out.op(Op::Add);
    b.from(out);
    out.op(Op::Positive);
    x.to(out);
    out.op(Op::Add);
    x.from(out);
    out.op(Op::Positive);
}

/// `acc = 1 - acc`, for a 0 or 1 in acc. Uses T10.
fn not_acc(out: &mut dyn Program) {
    out.op(Op::Neg);
    store(out, T10);
    out.op(Op::Set(1));
    T10.to(out);
    out.op(Op::Add);
    T10.from(out);
}

/// x *= 10, as ((x * 4) + x) * 2.
fn mul10(out: &mut dyn Program, x: &Location, tmp: &Location) {
    mov(out, tmp, x);
    add_assign(out, x, x);
    add_assign(out, x, x);
    add_assign(out, x, tmp);
    add_assign(out, x, x);
}

/// `dst` = how far apart neighbouring cells' addresses are: 1 on the CPU, and
/// 8 in the C backend, where addresses are in bytes.
fn cell_size(out: &mut dyn Program, dst: &Location) {
    dst.to(out);
    out.op(Op::Where);
    out.op(Op::Neg);
    out.op(Op::Store);
    out.op(Op::Move(1));
    out.op(Op::Where);
    out.op(Op::Move(-1));
    out.op(Op::Add);
    out.op(Op::Store);
    dst.from(out);
}

/// `cond` computes `flag`, and the body runs while it's nonzero. Unlike
/// `while_loop` this can't be broken out of, but it needs no loop flags.
fn raw_while(
    out: &mut dyn Program,
    flag: &Location,
    cond: impl Fn(&mut dyn Program),
    body: impl FnOnce(&mut dyn Program),
) {
    cond(out);
    begin_while(out, flag);
    body(out);
    cond(out);
    end_while(out, flag);
}

// Control flow. Open blocks are tracked on a per-thread stack of frames, so
// that `break_loop`, `continue_loop` and `ret` know what they're leaving.
//
// Leaving a block early works with "guards": after a break, the rest of the
// block is wrapped in a one-shot `while (still running)`, and so is the rest
// of every enclosing block up to the loop (or function). Every loop and
// function leaves its flags in their running state when it finishes, so a
// call can't disturb its caller's flags.

#[derive(Clone, Copy, Debug, PartialEq)]
enum Kind {
    If,
    /// A `begin_loop` loop, with its nesting depth within the function.
    Loop(u64),
    /// A `begin_while` loop, which can't be broken out of.
    RawLoop,
    Func,
    Routine,
}

struct Frame {
    kind: Kind,
    /// Guards opened in this block, closed when it ends.
    guards: usize,
    /// Whether this block might have broken out of or continued its loop.
    jumped: bool,
    /// Whether this block might have returned from its function.
    returned: bool,
}

thread_local! {
    static FRAMES: RefCell<Vec<Frame>> = const { RefCell::new(Vec::new()) };
}

fn with_frames<R>(f: impl FnOnce(&mut Vec<Frame>) -> R) -> R {
    FRAMES.with(|frames| f(&mut frames.borrow_mut()))
}

fn push_frame(kind: Kind) {
    with_frames(|f| f.push(Frame { kind, guards: 0, jumped: false, returned: false }));
}

fn close_guards(out: &mut dyn Program) {
    let n = with_frames(|f| f.last_mut().map_or(0, |top| std::mem::take(&mut top.guards)));
    for _ in 0..n {
        out.op(Op::Set(0));
        out.op(Op::EndWhile);
    }
}

/// Closes the innermost block, which must be one that `is` accepts.
fn end_frame(out: &mut dyn Program, what: &str, is: fn(Kind) -> bool) -> Frame {
    close_guards(out);
    with_frames(|f| match f.pop() {
        Some(frame) if is(frame.kind) => frame,
        other => panic!("{what} doesn't match the innermost open block ({:?})", other.map(|f| f.kind)),
    })
}

fn loop_run(depth: u64) -> Location {
    reg(LOOP_FLAGS + 2 * depth)
}

fn loop_go(depth: u64) -> Location {
    reg(LOOP_FLAGS + 2 * depth + 1)
}

/// The flag that's 0 once the current block should stop running: the
/// innermost loop's `run`, or the function's.
fn guard_flag() -> Location {
    with_frames(|f| {
        for frame in f.iter().rev() {
            match frame.kind {
                Kind::If => {}
                Kind::Loop(depth) => return loop_run(depth),
                Kind::Func => return FUNC_RUN.clone(),
                Kind::RawLoop | Kind::Routine => break,
            }
        }
        unreachable!("nothing to guard on")
    })
}

/// Skips the rest of the innermost block if `flag` is 0.
fn open_guard(out: &mut dyn Program, flag: &Location) {
    load(out, flag);
    out.op(Op::While);
    with_frames(|f| f.last_mut().expect("no block to guard").guards += 1);
}

/// Marks the innermost block as maybe left early, and guards the rest of it.
fn left_early(out: &mut dyn Program, jumped: bool, returned: bool) {
    if !(jumped || returned) {
        return;
    }
    with_frames(|f| {
        let top = f.last_mut().expect("no block to leave");
        top.jumped |= jumped;
        top.returned |= returned;
    });
    open_guard(out, &guard_flag());
}

/// The depth of the innermost `begin_loop` loop, for leaving it.
fn innermost_loop(what: &str) -> u64 {
    with_frames(|f| {
        for frame in f.iter().rev() {
            match frame.kind {
                Kind::If => {}
                Kind::Loop(depth) => return depth,
                Kind::RawLoop => panic!("{what} can't leave a begin_while loop: use begin_loop or while_loop"),
                Kind::Func | Kind::Routine => break,
            }
        }
        panic!("{what} outside a loop")
    })
}

pub fn begin_while(out: &mut dyn Program, src: &Location) {
    load(out, src);
    out.op(Op::While);
    push_frame(Kind::RawLoop);
}

pub fn end_while(out: &mut dyn Program, src: &Location) {
    end_frame(out, "end_while", |k| k == Kind::RawLoop);
    load(out, src);
    out.op(Op::EndWhile);
}

/// Starts `if src != 0 { ... }`, closed by `end_if` with an optional
/// `begin_else` in between.
pub fn begin_if(out: &mut dyn Program, src: &Location) {
    // T9 records whether the else branch should run: it's cleared as the
    // last step of the then branch, so the then body is free to clobber it
    set(out, T9, 1);
    load(out, src);
    out.op(Op::While);
    push_frame(Kind::If);
}

pub fn begin_else(out: &mut dyn Program) {
    close_guards(out);
    let in_if = with_frames(|f| f.last().map(|f| f.kind)) == Some(Kind::If);
    assert!(in_if, "begin_else doesn't match the innermost open block");
    // set leaves acc = 0, which ends the then branch's one-shot loop
    set(out, T9, 0);
    out.op(Op::EndWhile);
    load(out, T9);
    out.op(Op::While);
}

pub fn end_if(out: &mut dyn Program) {
    let frame = end_frame(out, "end_if", |k| k == Kind::If);
    out.op(Op::Set(0));
    out.op(Op::EndWhile);
    left_early(out, frame.jumped, frame.returned);
}

/// Starts a loop that runs until `break_loop` or `break_if` leaves it. End it
/// with `end_loop`.
pub fn begin_loop(out: &mut dyn Program) {
    let depth = with_frames(|f| {
        f.iter()
            .rev()
            .take_while(|frame| !matches!(frame.kind, Kind::Func | Kind::Routine))
            .filter(|frame| matches!(frame.kind, Kind::Loop(_)))
            .count() as u64
    });
    assert!(depth < MAX_LOOP_DEPTH, "begin_loop nested more than {MAX_LOOP_DEPTH} deep");
    set(out, &loop_go(depth), 1);
    load(out, &loop_go(depth));
    out.op(Op::While);
    set(out, &loop_run(depth), 1);
    push_frame(Kind::Loop(depth));
}

pub fn end_loop(out: &mut dyn Program) {
    let frame = end_frame(out, "end_loop", |k| matches!(k, Kind::Loop(_)));
    let Kind::Loop(depth) = frame.kind else { unreachable!() };
    load(out, &loop_go(depth));
    out.op(Op::EndWhile);
    // leave the flags as a running loop's (see the note above `Kind`)
    set(out, &loop_run(depth), 1);
    set(out, &loop_go(depth), 1);
    left_early(out, false, frame.returned);
}

/// Leaves the innermost `begin_loop` loop.
pub fn break_loop(out: &mut dyn Program) {
    let depth = innermost_loop("break_loop");
    set(out, &loop_run(depth), 0);
    set(out, &loop_go(depth), 0);
    left_early(out, true, false);
}

/// Leaves the innermost `begin_loop` loop if `flag != 0`.
pub fn break_if(out: &mut dyn Program, flag: &Location) {
    let depth = innermost_loop("break_if");
    test_zero(out, &loop_go(depth), flag, 1, 0);
    mov(out, &loop_run(depth), &loop_go(depth));
    left_early(out, true, false);
}

/// Skips to the next iteration of the innermost `begin_loop` loop.
pub fn continue_loop(out: &mut dyn Program) {
    let depth = innermost_loop("continue_loop");
    set(out, &loop_run(depth), 0);
    left_early(out, true, false);
}

/// `while flag != 0 { body }`, where `cond` recomputes `flag` before every
/// check. `body` can use `break_loop` and `continue_loop`.
pub fn while_loop(
    out: &mut dyn Program,
    flag: &Location,
    cond: impl Fn(&mut dyn Program),
    body: impl FnOnce(&mut dyn Program),
) {
    begin_loop(out);
    cond(out);
    let depth = innermost_loop("while_loop");
    test_zero(out, &loop_go(depth), flag, 0, 1);
    mov(out, &loop_run(depth), &loop_go(depth));
    left_early(out, true, false);
    body(out);
    end_loop(out);
}

// Functions. The caller pushes the arguments and the callee finds them with
// `arg(i)`; `local(i)` is the callee's own stack space. The return value goes
// in R0, and a call may change every register except SP and FP. Calls need
// `init` to have run first.

/// Prefixed to function names in the program, so that in the C backend they
/// can't clash with C's own names like `main` or `puts`.
const FUNC_PREFIX: &str = "f_";

/// Prefixed to the names of the helpers' shared routines.
const ROUTINE_PREFIX: &str = "rt_";

fn make_label(name: &str) -> Op {
    let mut arr = [0u8; 16];
    arr[..name.len()].copy_from_slice(name.as_bytes());
    Op::Label(arr)
}

/// The label of the external function `name`: its name, which the
/// program doesn't define, so in the C backend it's a C function
/// `void name(int64_t **tape, int64_t **ptr, int64_t *acc)`.
pub fn external_label(name: &str) -> Op {
    make_label(name)
}

fn label(name: &str) -> Op {
    let max = 15 - FUNC_PREFIX.len();
    let ok = (1..=max).contains(&name.len())
        && name.chars().all(|c| c.is_ascii_alphanumeric() || c == '_');
    assert!(ok, "function names must be 1 to {max} letters, digits or '_': {name:?}");
    make_label(&format!("{FUNC_PREFIX}{name}"))
}

/// Starts the body of function `name`, with `locals` cells of local storage.
/// End it with `end_func`. A function can be defined anywhere, including
/// inside a loop, an `if` or another function, but it only sees its own
/// arguments and locals.
pub fn begin_func(out: &mut dyn Program, name: &str, locals: i64) {
    out.op(label(name));
    out.op(Op::Func);
    push(out, FP);
    mov(out, FP, SP);
    alloc(out, locals);
    set(out, FUNC_RUN, 1);
    push_frame(Kind::Func);
}

pub fn end_func(out: &mut dyn Program) {
    end_frame(out, "end_func", |k| k == Kind::Func);
    set(out, FUNC_RUN, 1);
    mov(out, SP, FP);
    pop(out, FP);
    out.op(Op::EndFunc);
}

/// Returns from the current function, skipping the rest of its body. Set R0
/// first to return a value.
pub fn ret(out: &mut dyn Program) {
    let loops = with_frames(|f| {
        let mut loops = vec![];
        for frame in f.iter().rev() {
            match frame.kind {
                Kind::If => {}
                Kind::Loop(depth) => loops.push(depth),
                Kind::RawLoop => panic!("ret can't leave a begin_while loop: use begin_loop or while_loop"),
                Kind::Func => return loops,
                Kind::Routine => break,
            }
        }
        panic!("ret outside a function")
    });
    for depth in loops {
        set(out, &loop_run(depth), 0);
        set(out, &loop_go(depth), 0);
    }
    set(out, FUNC_RUN, 0);
    left_early(out, false, true);
}

/// Calls `name` with `args`, which are pushed in reverse so that `args[i]` is
/// the callee's `arg(i)`, and popped again afterwards.
pub fn call(out: &mut dyn Program, name: &str, args: &[&Location]) {
    for a in args.iter().rev() {
        push(out, a);
    }
    out.op(label(name));
    out.op(Op::Call);
    alloc(out, -(args.len() as i64));
}

/// Argument `i` of the current function. The frame is laid out as
/// `[.., arg 1, arg 0, saved FP] [local 0, local 1, ..]`, with FP at local 0.
pub fn arg(i: i64) -> Location {
    FP.deref().offset(-2 - i)
}

/// Local cell `i` of the current function, for `i` below its `locals` count.
pub fn local(i: i64) -> Location {
    FP.deref().offset(i)
}

/// Calls the shared routine `name`, first defining it with `body` if the
/// program doesn't have it yet. Routines take their arguments and leave their
/// results in fixed T registers (or acc).
fn routine(out: &mut dyn Program, name: &str, body: impl FnOnce(&mut dyn Program)) {
    let label = || make_label(&format!("{ROUTINE_PREFIX}{name}"));
    if !out.defines(&label()) {
        out.op(label());
        out.op(Op::Func);
        push_frame(Kind::Routine);
        body(out);
        end_frame(out, "routine", |k| k == Kind::Routine);
        out.op(Op::EndFunc);
    }
    out.op(label());
    out.op(Op::Call);
}

// Multiplication and division.

/// T2 = T0 * T1. Uses T0 to T4 and T9.
fn mul_routine(out: &mut dyn Program) {
    routine(out, "mul", |out| {
        let (a, b, result, bit, top) = (T0, T1, T2, T3, T4);
        set(out, result, 0);
        // one pass per bit of a, from the top: result = result * 2 + top bit * b
        set(out, bit, 1);
        begin_while(out, bit);
        add_assign(out, result, result);
        is_negative(out, a, top);
        begin_if(out, top);
        add_assign(out, result, b);
        end_if(out);
        add_assign(out, a, a);
        add_assign(out, bit, bit);
        end_while(out, bit);
    });
}

/// Multiplication, wrapping like Rust's `wrapping_mul`.
pub fn mul_assign(out: &mut dyn Program, dst: &Location, src: &Location) {
    mov(out, T0, dst);
    mov(out, T1, src);
    mul_routine(out);
    mov(out, dst, T2);
}

/// Unsigned long division, T14 = T12 / T13 and T12 = T12 % T13, one pass per
/// bit from the top. Assumes T13 != 0. Uses T6 to T14.
fn divu_routine(out: &mut dyn Program) {
    routine(out, "divu", |out| {
        let (n, d, q) = (T12, T13, T14);
        let (r, bit, carry, top) = (T6, T7, T8, T11);
        set(out, r, 0);
        set(out, q, 0);
        set(out, bit, 1);
        // While n's top bit is 0 and r is still 0, a pass would only shift n,
        // so skip those passes cheaply: while bit != 0 && n's top bit is 0
        let skip = |out: &mut dyn Program| {
            test_zero(out, carry, bit, 0, 1);
            is_negative(out, n, top);
            load(out, top);
            out.op(Op::Neg);
            carry.to(out);
            out.op(Op::Add);
            out.op(Op::Positive);
            out.op(Op::Store);
            carry.from(out);
        };
        skip(out);
        out.op(Op::While);
        add_assign(out, n, n);
        add_assign(out, bit, bit);
        skip(out);
        out.op(Op::EndWhile);

        begin_while(out, bit);
        // r = r * 2 + the top bit of n, remembering the bit that falls off r
        is_negative(out, r, carry);
        add_assign(out, r, r);
        is_negative(out, n, top);
        add_assign(out, r, top);
        add_assign(out, n, n);
        add_assign(out, q, q);
        // if r overflowed or r >= d, take d out of it and set this quotient bit
        less(out, r, d, true);
        not_acc(out);
        carry.to(out);
        out.op(Op::Add);
        out.op(Op::Store);
        carry.from(out);
        begin_if(out, carry);
        sub_assign(out, r, d);
        inc(out, q);
        end_if(out);
        add_assign(out, bit, bit);
        end_while(out, bit);
        mov(out, n, r);
    });
}

/// `q = n / d` and `n = n % d` as unsigned values, for `d != 0`.
fn divu(out: &mut dyn Program, n: &Location, d: &Location, q: &Location) {
    mov(out, T12, n);
    mov(out, T13, d);
    divu_routine(out);
    mov(out, q, T14);
    mov(out, n, T12);
}

/// Like `divu_routine`, but dividing by 0 gives a quotient of all ones and
/// leaves T12 as it is, as RISC-V does.
fn udiv_routine(out: &mut dyn Program) {
    routine(out, "udiv", |out| {
        begin_if(out, T13);
        divu_routine(out);
        begin_else(out);
        set_int(out, T14, -1);
        end_if(out);
    });
}

/// Signed division rounding toward zero, wrapping like Rust's `wrapping_div`
/// and `wrapping_rem`: T2 = T0 / T1, and T0 = T0 % T1. Dividing by 0 gives a
/// quotient of -1 and leaves T0 as it is, as RISC-V does.
fn divs_routine(out: &mut dyn Program) {
    routine(out, "divs", |out| {
        let (a, b, q, a_neg, b_neg) = (T0, T1, T2, T3, T4);
        begin_if(out, b);
        // divide the magnitudes, then fix the signs: the remainder takes the
        // dividend's sign, and the quotient is negative if exactly one input
        // is. The magnitudes are divided as unsigned, so even |-2^63| works.
        for (x, x_neg) in [(a, a_neg), (b, b_neg)] {
            is_negative(out, x, x_neg);
            begin_if(out, x_neg);
            neg_assign(out, x);
            end_if(out);
        }
        divu(out, a, b, q);
        begin_if(out, a_neg);
        neg_assign(out, a);
        neg_assign(out, q);
        end_if(out);
        begin_if(out, b_neg);
        neg_assign(out, q);
        end_if(out);
        begin_else(out);
        set_int(out, q, -1);
        end_if(out);
    });
}

/// Signed division, rounding toward zero. `x / 0` is -1.
pub fn div_assign(out: &mut dyn Program, dst: &Location, src: &Location) {
    mov(out, T0, dst);
    mov(out, T1, src);
    divs_routine(out);
    mov(out, dst, T2);
}

/// Signed remainder, with the sign of `dst`. `x % 0` is `x`.
pub fn rem_assign(out: &mut dyn Program, dst: &Location, src: &Location) {
    mov(out, T0, dst);
    mov(out, T1, src);
    divs_routine(out);
    mov(out, dst, T0);
}

/// Signed division by a constant, quickest for powers of two and for
/// divisors whose magnitude is below 2^14. `x / 0` is -1.
pub fn div_const(out: &mut dyn Program, dst: &Location, k: i64) {
    div_by_const(out, dst, k, false);
}

/// Signed remainder by a constant, with the sign of `dst`. `x % 0` is `x`.
pub fn rem_const(out: &mut dyn Program, dst: &Location, k: i64) {
    div_by_const(out, dst, k, true);
}

/// Unsigned division. `x / 0` is all ones.
pub fn divu_assign(out: &mut dyn Program, dst: &Location, src: &Location) {
    mov(out, T12, dst);
    mov(out, T13, src);
    udiv_routine(out);
    mov(out, dst, T14);
}

/// Unsigned remainder. `x % 0` is `x`.
pub fn remu_assign(out: &mut dyn Program, dst: &Location, src: &Location) {
    mov(out, T12, dst);
    mov(out, T13, src);
    udiv_routine(out);
    mov(out, dst, T12);
}

// Shifts and bitwise ops.

/// T0 <<= T1, stopping early once T0 is 0 so that huge counts are quick.
/// Does nothing if T1 <= 0. Uses T0 to T2.
/// Leaves `acc = (count > 0 && value != 0)`, using `flag` as scratch.
fn counting_nonzero(out: &mut dyn Program, count: &Location, value: &Location, flag: &Location) {
    // (count > 0) + (value != 0) - 1 > 0
    test_zero(out, flag, value, 0, 1);
    load(out, count);
    out.op(Op::Positive);
    flag.to(out);
    out.op(Op::Add);
    out.op(Op::Store);
    out.op(Op::Set(1));
    out.op(Op::Neg);
    out.op(Op::Add);
    out.op(Op::Positive);
    flag.from(out);
}

/// Doubles `value` while `count > 0`, counting down, and stops early once
/// it's 0.
fn double_while_counting(out: &mut dyn Program, value: &Location, count: &Location, flag: &Location) {
    counting_nonzero(out, count, value, flag);
    out.op(Op::While);
    add_assign(out, value, value);
    dec(out, count);
    counting_nonzero(out, count, value, flag);
    out.op(Op::EndWhile);
}

fn lsh_routine(out: &mut dyn Program) {
    routine(out, "lsh", |out| double_while_counting(out, T0, T1, T2));
}

/// Shifts left by `src` bits; does nothing if `src <= 0`.
pub fn lsh_assign(out: &mut dyn Program, dst: &Location, src: &Location) {
    mov(out, T0, dst);
    mov(out, T1, src);
    lsh_routine(out);
    mov(out, dst, T0);
}

/// T4 >>= T5, arithmetic or logical. Does nothing if T5 <= 0; shifting by the
/// cell width or more gives 0, or -1 for an arithmetic shift of a negative
/// value. Uses T0 to T5 and T9.
fn rsh_routine(out: &mut dyn Program, arithmetic: bool) {
    routine(out, if arithmetic { "rsh" } else { "rshu" }, |out| {
        let (result, bit, neg, top, value, count) = (T0, T1, T2, T3, T4, T5);
        load(out, count);
        out.op(Op::Positive);
        store(out, top);
        begin_if(out, top);
        if arithmetic {
            // shift !value instead when value < 0, since !(!x >> n) == x >> n
            is_negative(out, value, neg);
            begin_if(out, neg);
            not_assign(out, value);
            end_if(out);
        }
        // bit = 2^count, or 0 once that's past the top of the cell
        set(out, bit, 1);
        double_while_counting(out, bit, count, top);
        // the result is the bits above `count`, read from the top while bit
        // doubles up to 0
        set(out, result, 0);
        begin_while(out, bit);
        add_assign(out, result, result);
        is_negative(out, value, top);
        add_assign(out, result, top);
        add_assign(out, value, value);
        add_assign(out, bit, bit);
        end_while(out, bit);
        if arithmetic {
            begin_if(out, neg);
            not_assign(out, result);
            end_if(out);
        }
        mov(out, value, result);
        end_if(out);
    });
}

/// Arithmetic shift right by `src` bits, rounding toward negative infinity
/// like Rust's `>>` on signed values. Does nothing if `src <= 0`; shifting by
/// the cell width or more gives 0, or -1 for negative values.
pub fn rsh_assign(out: &mut dyn Program, dst: &Location, src: &Location) {
    mov(out, T4, dst);
    mov(out, T5, src);
    rsh_routine(out, true);
    mov(out, dst, T4);
}

/// Logical shift right by `src` bits, filling with zeros. Does nothing if
/// `src <= 0`, and shifting by the cell width or more gives 0.
pub fn rshu_assign(out: &mut dyn Program, dst: &Location, src: &Location) {
    mov(out, T4, dst);
    mov(out, T5, src);
    rsh_routine(out, false);
    mov(out, dst, T4);
}

/// Shifts left by a constant.
pub fn lsh_const(out: &mut dyn Program, dst: &Location, k: i64) {
    match k {
        ..=0 => {}
        1..=8 => (0..k).for_each(|_| add_assign(out, dst, dst)),
        _ => {
            mov(out, T0, dst);
            set_int(out, T1, k);
            lsh_routine(out);
            mov(out, dst, T0);
        }
    }
}

/// Arithmetic shift right by a constant.
pub fn rsh_const(out: &mut dyn Program, dst: &Location, k: i64) {
    if k > 0 {
        mov(out, T4, dst);
        set_int(out, T5, k);
        rsh_routine(out, true);
        mov(out, dst, T4);
    }
}

/// Logical shift right by a constant.
pub fn rshu_const(out: &mut dyn Program, dst: &Location, k: i64) {
    if k > 0 {
        mov(out, T4, dst);
        set_int(out, T5, k);
        rsh_routine(out, false);
        mov(out, dst, T4);
    }
}

/// `bit = 2^m`, for `m` in a cell, counting it down to 0.
fn power_of_two(out: &mut dyn Program, bit: &Location, m: &Location) {
    set(out, bit, 1);
    load(out, m);
    out.op(Op::While);
    add_assign(out, bit, bit);
    dec(out, m);
    load(out, m);
    out.op(Op::EndWhile);
}

/// T4 = the low T6 bits of T4, for 0 <= T6 < 16. The bits above them only
/// need a doubling each, to move the low ones up to the top of the cell,
/// where they're read back. Uses T0 to T6 and T9.
fn low_bits_routine(out: &mut dyn Program) {
    routine(out, "lowbits", |out| {
        let (low, bit, count, top, value, m) = (T0, T1, T2, T3, T4, T6);
        mov(out, count, m);
        power_of_two(out, bit, count);
        begin_while(out, bit);
        add_assign(out, value, value);
        add_assign(out, bit, bit);
        end_while(out, bit);
        set(out, low, 0);
        mov(out, count, m);
        begin_while(out, count);
        add_assign(out, low, low);
        is_negative(out, value, top);
        add_assign(out, low, top);
        add_assign(out, value, value);
        dec(out, count);
        end_while(out, count);
        mov(out, value, low);
    });
}

/// `dst` = its low `m` bits, for `m` from 0 to 15.
fn low_bits(out: &mut dyn Program, dst: &Location, m: u32) {
    mov(out, T4, dst);
    set(out, T6, m as u64);
    low_bits_routine(out);
    mov(out, dst, T4);
}

#[derive(Clone, Copy, PartialEq)]
enum BitOp {
    And,
    Or,
    Xor,
}

/// T4 = T4 op T5, for 0 <= T5 < 2^T6 and T6 < 16: only the low T6 bits of T4
/// need combining, and the ones above them are kept (by `or` and `xor`) or
/// cleared (by `and`). Uses T0 to T8, T9 and T11.
fn bits_with_small_routine(out: &mut dyn Program, op: BitOp) {
    let name = match op {
        BitOp::And => "andk",
        BitOp::Or => "ork",
        BitOp::Xor => "xork",
    };
    routine(out, name, |out| {
        let (low, bit, count, top, x, k, m, y, new, k_top) = (T0, T1, T2, T3, T4, T5, T6, T7, T8, T11);
        // move the low m bits of x and of k up to the top of the cell
        mov(out, y, x);
        mov(out, count, m);
        power_of_two(out, bit, count);
        begin_while(out, bit);
        add_assign(out, y, y);
        add_assign(out, k, k);
        add_assign(out, bit, bit);
        end_while(out, bit);
        // combine them a bit at a time, from the top
        set(out, low, 0);
        set(out, new, 0);
        mov(out, count, m);
        begin_while(out, count);
        is_negative(out, y, top);
        is_negative(out, k, k_top);
        add_assign(out, low, low);
        add_assign(out, low, top);
        add_assign(out, new, new);
        // the two bits' sum is 0, 1 or 2
        add_assign(out, k_top, top);
        match op {
            BitOp::And => {
                k_top.to(out);
                set_acc(out, -1);
                out.op(Op::Add);
                out.op(Op::Positive);
                k_top.from(out);
            }
            BitOp::Or => {
                load(out, k_top);
                out.op(Op::Positive);
            }
            BitOp::Xor => {
                in_range(out, k_top, 1, 1, top);
                load(out, top);
            }
        }
        new.to(out);
        out.op(Op::Add);
        out.op(Op::Store);
        new.from(out);
        add_assign(out, y, y);
        add_assign(out, k, k);
        dec(out, count);
        end_while(out, count);
        if op == BitOp::And {
            mov(out, x, new);
        } else {
            sub_assign(out, x, low);
            add_assign(out, x, new);
        }
    });
}

/// Whether `k` is small enough for the routines that take a small constant.
fn is_small(k: i64) -> bool {
    (1..1 << 15).contains(&k)
}

/// The number of bits in `k`, for `k > 0`.
fn bit_length(k: i64) -> u32 {
    64 - k.leading_zeros()
}

/// `dst op= k` for `k` with `0 < k < 2^15`.
fn bits_with_small(out: &mut dyn Program, dst: &Location, k: i64, op: BitOp) {
    let m = bit_length(k);
    if op == BitOp::And && k == (1 << m) - 1 {
        return low_bits(out, dst, m);
    }
    mov(out, T4, dst);
    set_int(out, T5, k);
    set(out, T6, m as u64);
    bits_with_small_routine(out, op);
    mov(out, dst, T4);
}

/// `dst &= k`. Much quicker than `and_assign` when `k` or `!k` is below 2^15,
/// since then only the low bits take real work.
pub fn and_const(out: &mut dyn Program, dst: &Location, k: i64) {
    match k {
        0 => set(out, dst, 0),
        -1 => {}
        _ if is_small(k) => bits_with_small(out, dst, k, BitOp::And),
        // x & k = x - (x & !k)
        _ if is_small(!k) => {
            mov(out, T12, dst);
            bits_with_small(out, T12, !k, BitOp::And);
            sub_assign(out, dst, T12);
        }
        _ => {
            mov(out, T0, dst);
            set_int(out, T1, k);
            bitwise_routine(out, "and", and_bit);
            mov(out, dst, T2);
        }
    }
}

/// `dst |= k`. Much quicker than `or_assign` when `k` or `!k` is below 2^15.
pub fn or_const(out: &mut dyn Program, dst: &Location, k: i64) {
    match k {
        0 => {}
        -1 => set_int(out, dst, -1),
        _ if is_small(k) => bits_with_small(out, dst, k, BitOp::Or),
        // x | k = !(!x & !k)
        _ if is_small(!k) => {
            not_assign(out, dst);
            and_const(out, dst, !k);
            not_assign(out, dst);
        }
        _ => {
            mov(out, T0, dst);
            set_int(out, T1, k);
            bitwise_routine(out, "or", or_bit);
            mov(out, dst, T2);
        }
    }
}

/// `dst ^= k`. Much quicker than `xor_assign` when `k` or `!k` is below 2^15.
pub fn xor_const(out: &mut dyn Program, dst: &Location, k: i64) {
    match k {
        0 => {}
        -1 => not_assign(out, dst),
        _ if is_small(k) => bits_with_small(out, dst, k, BitOp::Xor),
        // x ^ k = !(x ^ !k)
        _ if is_small(!k) => {
            xor_const(out, dst, !k);
            not_assign(out, dst);
        }
        _ => {
            mov(out, T0, dst);
            set_int(out, T1, k);
            bitwise_routine(out, "xor", xor_bit);
            mov(out, dst, T2);
        }
    }
}

/// Whether `k` is a power of two with an exponent below 15.
fn small_power_of_two(k: i64) -> Option<u32> {
    (is_small(k) && k & (k - 1) == 0).then(|| k.trailing_zeros())
}

/// T14 = T12 / T13 and T12 = T12 % T13 as unsigned, for 0 < T13 < 2^14. The
/// remainder stays below 2 * T13, so comparing it is cheap. Uses T6 to T14.
fn divu_small_routine(out: &mut dyn Program) {
    routine(out, "divuk", |out| {
        let (n, d, q) = (T12, T13, T14);
        let (r, bit, flag, top) = (T6, T7, T8, T11);
        set(out, r, 0);
        set(out, q, 0);
        set(out, bit, 1);
        // skip n's leading zeros, which can't change r or q
        let skip = |out: &mut dyn Program| {
            test_zero(out, flag, bit, 0, 1);
            is_negative(out, n, top);
            load(out, top);
            out.op(Op::Neg);
            flag.to(out);
            out.op(Op::Add);
            out.op(Op::Positive);
            out.op(Op::Store);
            flag.from(out);
        };
        skip(out);
        out.op(Op::While);
        add_assign(out, n, n);
        add_assign(out, bit, bit);
        skip(out);
        out.op(Op::EndWhile);

        begin_while(out, bit);
        add_assign(out, r, r);
        is_negative(out, n, top);
        add_assign(out, r, top);
        add_assign(out, n, n);
        add_assign(out, q, q);
        mov(out, flag, r);
        ge_small(out, flag, d);
        begin_if(out, flag);
        sub_assign(out, r, d);
        inc(out, q);
        end_if(out);
        add_assign(out, bit, bit);
        end_while(out, bit);
        mov(out, n, r);
    });
}

/// Unsigned division or remainder of `dst` by a constant, quickest for powers
/// of two and for divisors below 2^14.
fn divu_by_const(out: &mut dyn Program, dst: &Location, k: i64, remainder: bool) {
    if let Some(m) = small_power_of_two(k) {
        if remainder {
            low_bits(out, dst, m);
        } else {
            rshu_const(out, dst, m as i64);
        }
        return;
    }
    mov(out, T12, dst);
    set_int(out, T13, k);
    if is_small(k) && k < 1 << 14 {
        divu_small_routine(out);
    } else {
        udiv_routine(out);
    }
    mov(out, dst, if remainder { T12 } else { T14 });
}

/// Unsigned division by a constant. `x / 0` is all ones.
pub fn divu_const(out: &mut dyn Program, dst: &Location, k: i64) {
    divu_by_const(out, dst, k, false);
}

/// Unsigned remainder by a constant. `x % 0` is `x`.
pub fn remu_const(out: &mut dyn Program, dst: &Location, k: i64) {
    divu_by_const(out, dst, k, true);
}

/// Signed division or remainder of `dst` by a constant, rounding toward zero:
/// divides the magnitudes as unsigned, then fixes the signs.
fn div_by_const(out: &mut dyn Program, dst: &Location, k: i64, remainder: bool) {
    let d = k.unsigned_abs() as i64;
    if k == 0 || k == i64::MIN || !(is_small(d) && d < 1 << 14) {
        mov(out, T0, dst);
        set_int(out, T1, k);
        divs_routine(out);
        return mov(out, dst, if remainder { T0 } else { T2 });
    }
    if small_power_of_two(d).is_none() {
        small_divide(out, dst, Divisor::Const(d), true, remainder);
        if !remainder && k < 0 {
            neg_assign(out, dst);
        }
        return;
    }
    let (neg, magnitude) = (T12, T13);
    is_negative(out, dst, neg);
    mov(out, magnitude, dst);
    begin_if(out, neg);
    neg_assign(out, magnitude);
    end_if(out);
    // the shift and mask leave T12 and T13 alone
    divu_by_const(out, magnitude, d, remainder);
    // the remainder takes the dividend's sign, and the quotient is negative
    // if exactly one of the dividend and the divisor is
    begin_if(out, neg);
    neg_assign(out, magnitude);
    end_if(out);
    if !remainder && k < 0 {
        neg_assign(out, magnitude);
    }
    mov(out, dst, magnitude);
}

enum Divisor<'a> {
    Const(i64),
    At(&'a Location),
}

/// Divides `dst` by a divisor from 1 to 2^14 - 1, as signed or unsigned
/// values, leaving the quotient or the remainder.
fn small_divide(out: &mut dyn Program, dst: &Location, divisor: Divisor, signed: bool, remainder: bool) {
    let negative = T5;
    if signed {
        // divide the magnitude, then give the results the dividend's sign
        is_negative(out, dst, negative);
        mov(out, T12, dst);
        begin_if(out, negative);
        neg_assign(out, T12);
        end_if(out);
    } else {
        mov(out, T12, dst);
    }
    match divisor {
        Divisor::Const(d) => set_int(out, T13, d),
        Divisor::At(src) => mov(out, T13, src),
    }
    divu_small_routine(out);
    let result = if remainder { T12 } else { T14 };
    if signed {
        begin_if(out, negative);
        neg_assign(out, result);
        end_if(out);
    }
    mov(out, dst, result);
}

/// Signed division by `src`, which must be from 1 to 2^14 - 1. Quicker than
/// `div_assign`, since the remainder stays small.
pub fn div_small_assign(out: &mut dyn Program, dst: &Location, src: &Location) {
    small_divide(out, dst, Divisor::At(src), true, false);
}

/// Signed remainder by `src`, which must be from 1 to 2^14 - 1.
pub fn rem_small_assign(out: &mut dyn Program, dst: &Location, src: &Location) {
    small_divide(out, dst, Divisor::At(src), true, true);
}

/// Unsigned division by `src`, which must be from 1 to 2^14 - 1.
pub fn divu_small_assign(out: &mut dyn Program, dst: &Location, src: &Location) {
    small_divide(out, dst, Divisor::At(src), false, false);
}

/// Unsigned remainder by `src`, which must be from 1 to 2^14 - 1.
pub fn remu_small_assign(out: &mut dyn Program, dst: &Location, src: &Location) {
    small_divide(out, dst, Divisor::At(src), false, true);
}

/// T2 = T0 op T1, one bit at a time from the top. `bit_op` gets `sum`, the
/// two input bits added together (0, 1 or 2), and must leave the output bit
/// (0 or 1) in `sum`. It may use `tmp` as scratch. Uses T0 to T5.
fn bitwise_routine(out: &mut dyn Program, name: &str, bit_op: fn(&mut dyn Program, &Location, &Location)) {
    routine(out, name, |out| {
        let (a, b, result, bit, sum, tmp) = (T0, T1, T2, T3, T4, T5);
        set(out, result, 0);
        // one pass per bit: result = result * 2 + op(top bit of a, top bit of b)
        set(out, bit, 1);
        begin_while(out, bit);
        add_assign(out, result, result);
        is_negative(out, a, sum);
        is_negative(out, b, tmp);
        add_assign(out, sum, tmp);
        bit_op(out, sum, tmp);
        add_assign(out, result, sum);
        add_assign(out, a, a);
        add_assign(out, b, b);
        add_assign(out, bit, bit);
        end_while(out, bit);
    });
}

fn bitwise(
    out: &mut dyn Program,
    dst: &Location,
    src: &Location,
    name: &str,
    bit_op: fn(&mut dyn Program, &Location, &Location),
) {
    mov(out, T0, dst);
    mov(out, T1, src);
    bitwise_routine(out, name, bit_op);
    mov(out, dst, T2);
}

fn xor_bit(out: &mut dyn Program, sum: &Location, tmp: &Location) {
    in_range(out, sum, 1, 1, tmp);
    mov(out, sum, tmp);
}

fn and_bit(out: &mut dyn Program, sum: &Location, tmp: &Location) {
    in_range(out, sum, 2, 2, tmp);
    mov(out, sum, tmp);
}

fn or_bit(out: &mut dyn Program, sum: &Location, _: &Location) {
    sum.to(out);
    out.op(Op::Load);
    out.op(Op::Positive);
    out.op(Op::Store);
    sum.from(out);
}

pub fn xor_assign(out: &mut dyn Program, dst: &Location, src: &Location) {
    bitwise(out, dst, src, "xor", xor_bit);
}

pub fn and_assign(out: &mut dyn Program, dst: &Location, src: &Location) {
    bitwise(out, dst, src, "and", and_bit);
}

pub fn or_assign(out: &mut dyn Program, dst: &Location, src: &Location) {
    bitwise(out, dst, src, "or", or_bit);
}

// Comparisons store 1 for true and 0 for false, and are exact for all values.

/// acc = T12 < T13, signed or unsigned. Uses T10 to T13.
fn less_routine(out: &mut dyn Program, unsigned: bool) {
    routine(out, if unsigned { "lessu" } else { "less" }, |out| less(out, T12, T13, unsigned));
}

/// dst = T12 < T13, or with `negate`, dst = T12 >= T13.
fn store_less(out: &mut dyn Program, dst: &Location, unsigned: bool, negate: bool) {
    less_routine(out, unsigned);
    if negate {
        not_acc(out);
    }
    store(out, dst);
}

/// Compares `a` with `b` into `dst`: `a < b`, or with `negate`, `a >= b`.
fn compare(out: &mut dyn Program, dst: &Location, a: &Location, b: &Location, unsigned: bool, negate: bool) {
    mov(out, T12, a);
    mov(out, T13, b);
    store_less(out, dst, unsigned, negate);
}

pub fn lt_assign(out: &mut dyn Program, dst: &Location, src: &Location) {
    compare(out, dst, dst, src, false, false);
}

pub fn gt_assign(out: &mut dyn Program, dst: &Location, src: &Location) {
    compare(out, dst, src, dst, false, false);
}

pub fn le_assign(out: &mut dyn Program, dst: &Location, src: &Location) {
    compare(out, dst, src, dst, false, true);
}

pub fn ge_assign(out: &mut dyn Program, dst: &Location, src: &Location) {
    compare(out, dst, dst, src, false, true);
}

pub fn ltu_assign(out: &mut dyn Program, dst: &Location, src: &Location) {
    compare(out, dst, dst, src, true, false);
}

pub fn gtu_assign(out: &mut dyn Program, dst: &Location, src: &Location) {
    compare(out, dst, src, dst, true, false);
}

pub fn leu_assign(out: &mut dyn Program, dst: &Location, src: &Location) {
    compare(out, dst, src, dst, true, true);
}

pub fn geu_assign(out: &mut dyn Program, dst: &Location, src: &Location) {
    compare(out, dst, dst, src, true, true);
}

pub fn eq_assign(out: &mut dyn Program, dst: &Location, src: &Location) {
    mov(out, T0, dst);
    sub_assign(out, T0, src);
    test_zero(out, dst, T0, 1, 0);
}

pub fn ne_assign(out: &mut dyn Program, dst: &Location, src: &Location) {
    mov(out, T0, dst);
    sub_assign(out, T0, src);
    test_zero(out, dst, T0, 0, 1);
}

/// Whether `k` is the same on every cell width (it fits in 16 bits).
fn fits_16(k: i64) -> bool {
    (-(1 << 15)..1 << 15).contains(&k)
}

/// `dst = dst < k`, exactly, for a `k` that fits in 16 bits. When `dst` has
/// the same sign as `k`, `k - dst` can't overflow, so `#` decides it; when
/// it doesn't, the signs do.
fn lt_const_exact(out: &mut dyn Program, dst: &Location, k: i64) {
    let negative = T11;
    is_negative(out, dst, negative);
    begin_if(out, negative);
    if k >= 0 {
        set(out, dst, 1);
        begin_else(out);
        lt_const_small(out, dst, k);
    } else {
        lt_const_small(out, dst, k);
        begin_else(out);
        set(out, dst, 0);
    }
    end_if(out);
}

pub fn lt_const(out: &mut dyn Program, dst: &Location, k: i64) {
    if fits_16(k) {
        return lt_const_exact(out, dst, k);
    }
    mov(out, T12, dst);
    set_int(out, T13, k);
    store_less(out, dst, false, false);
}

pub fn gt_const(out: &mut dyn Program, dst: &Location, k: i64) {
    // x > 0 is what `#` tests
    if k == 0 {
        load(out, dst);
        out.op(Op::Positive);
        return store(out, dst);
    }
    // x > k is !(x < k + 1)
    if fits_16(k) && fits_16(k + 1) {
        lt_const_exact(out, dst, k + 1);
        return lnot_assign(out, dst);
    }
    set_int(out, T12, k);
    mov(out, T13, dst);
    store_less(out, dst, false, false);
}

pub fn le_const(out: &mut dyn Program, dst: &Location, k: i64) {
    // x <= 0 is 1 - (x > 0)
    if k == 0 {
        load(out, dst);
        out.op(Op::Positive);
        out.op(Op::Neg);
        store(out, dst);
        out.op(Op::Set(1));
        dst.to(out);
        out.op(Op::Add);
        dst.from(out);
        return store(out, dst);
    }
    if fits_16(k) && fits_16(k + 1) {
        return lt_const_exact(out, dst, k + 1);
    }
    set_int(out, T12, k);
    mov(out, T13, dst);
    store_less(out, dst, false, true);
}

pub fn ge_const(out: &mut dyn Program, dst: &Location, k: i64) {
    if fits_16(k) {
        lt_const_exact(out, dst, k);
        return lnot_assign(out, dst);
    }
    mov(out, T12, dst);
    set_int(out, T13, k);
    store_less(out, dst, false, true);
}

// Comparisons for values known to be close together: each is only correct
// when `dst - src` (or `dst - k`) fits in the narrowest cell width the
// program runs on (16 bits, for programs that run on anything), so that it
// can't overflow. Then `#` on the difference decides it, in a handful of ops.

/// acc = (a - b > 0), for a difference that fits in the narrowest width.
fn difference_positive(out: &mut dyn Program, a: &Location, b: &Location) {
    load(out, b);
    out.op(Op::Neg);
    a.to(out);
    out.op(Op::Add);
    a.from(out);
    out.op(Op::Positive);
}

/// `dst = dst < src`, if `dst - src` fits in the narrowest width.
pub fn lt_small(out: &mut dyn Program, dst: &Location, src: &Location) {
    difference_positive(out, src, dst);
    store(out, dst);
}

/// `dst = dst > src`, if `dst - src` fits in the narrowest width.
pub fn gt_small(out: &mut dyn Program, dst: &Location, src: &Location) {
    difference_positive(out, dst, src);
    store(out, dst);
}

/// `dst = dst <= src`, if `dst - src` fits in the narrowest width.
pub fn le_small(out: &mut dyn Program, dst: &Location, src: &Location) {
    difference_positive(out, dst, src);
    not_acc(out);
    store(out, dst);
}

/// `dst = dst >= src`, if `dst - src` fits in the narrowest width.
pub fn ge_small(out: &mut dyn Program, dst: &Location, src: &Location) {
    difference_positive(out, src, dst);
    not_acc(out);
    store(out, dst);
}

/// `dst = dst > k`, if `dst - k` fits in the narrowest width.
pub fn gt_const_small(out: &mut dyn Program, dst: &Location, k: i64) {
    dst.to(out);
    set_acc(out, k.wrapping_neg());
    out.op(Op::Add);
    out.op(Op::Positive);
    out.op(Op::Store);
    dst.from(out);
}

/// `dst = dst < k`, if `dst - k` fits in the narrowest width.
pub fn lt_const_small(out: &mut dyn Program, dst: &Location, k: i64) {
    // k - dst > 0
    dst.to(out);
    out.op(Op::Load);
    out.op(Op::Neg);
    out.op(Op::Store);
    set_acc(out, k);
    out.op(Op::Add);
    out.op(Op::Positive);
    out.op(Op::Store);
    dst.from(out);
}

/// `dst = dst <= k`, if `dst - k` fits in the narrowest width.
pub fn le_const_small(out: &mut dyn Program, dst: &Location, k: i64) {
    gt_const_small(out, dst, k);
    lnot_assign(out, dst);
}

/// `dst = dst >= k`, if `dst - k` fits in the narrowest width.
pub fn ge_const_small(out: &mut dyn Program, dst: &Location, k: i64) {
    lt_const_small(out, dst, k);
    lnot_assign(out, dst);
}

/// T2 = T0 * T1 by adding T0 T1 times, for T1 >= 0. Uses T0 to T2.
fn mul_small_routine(out: &mut dyn Program) {
    routine(out, "muls", |out| {
        set(out, T2, 0);
        let more = |out: &mut dyn Program| {
            load(out, T1);
            out.op(Op::Positive);
        };
        more(out);
        out.op(Op::While);
        add_assign(out, T2, T0);
        dec(out, T1);
        more(out);
        out.op(Op::EndWhile);
    });
}

/// Multiplies by repeated addition: `src` must be at least 0, and this takes
/// `src` passes, so it's only quicker than `mul_assign` when `src` is small.
pub fn mul_small_assign(out: &mut dyn Program, dst: &Location, src: &Location) {
    mov(out, T0, dst);
    mov(out, T1, src);
    mul_small_routine(out);
    mov(out, dst, T2);
}

pub fn eq_const(out: &mut dyn Program, dst: &Location, k: i64) {
    mov(out, T0, dst);
    sub_const(out, T0, k);
    test_zero(out, dst, T0, 1, 0);
}

pub fn ne_const(out: &mut dyn Program, dst: &Location, k: i64) {
    mov(out, T0, dst);
    sub_const(out, T0, k);
    test_zero(out, dst, T0, 0, 1);
}

pub fn min_assign(out: &mut dyn Program, dst: &Location, src: &Location) {
    compare(out, T0, src, dst, false, false);
    begin_if(out, T0);
    mov(out, dst, src);
    end_if(out);
}

pub fn max_assign(out: &mut dyn Program, dst: &Location, src: &Location) {
    compare(out, T0, dst, src, false, false);
    begin_if(out, T0);
    mov(out, dst, src);
    end_if(out);
}

// Logical ops treat any nonzero value as true, and store 1 or 0.

pub fn lnot_assign(out: &mut dyn Program, dst: &Location) {
    mov(out, T0, dst);
    test_zero(out, dst, T0, 1, 0);
}

pub fn land_assign(out: &mut dyn Program, dst: &Location, src: &Location) {
    test_zero(out, T0, dst, 0, 1);
    test_zero(out, T1, src, 0, 1);
    // T0 + T1 - 1 > 0
    set_acc(out, -1);
    for x in [T0, T1] {
        x.to(out);
        out.op(Op::Add);
        x.from(out);
    }
    out.op(Op::Positive);
    store(out, dst);
}

pub fn lor_assign(out: &mut dyn Program, dst: &Location, src: &Location) {
    test_zero(out, T0, dst, 0, 1);
    test_zero(out, T1, src, 0, 1);
    load(out, T0);
    T1.to(out);
    out.op(Op::Add);
    T1.from(out);
    out.op(Op::Positive);
    store(out, dst);
}

// Numbers in decimal.

/// Prints T0 as an unsigned decimal. Uses T0 to T14.
fn putu_routine(out: &mut dyn Program) {
    routine(out, "putu", |out| {
        let (n, p, digit, ten, tmp, count, t) = (T0, T1, T2, T3, T4, T5, T6);
        // count = the number of digits: 1 plus how many times p can be
        // multiplied by 10 while staying <= n / 10. Comparing against n / 10
        // rather than 10 * p against n keeps 10 * p from overflowing.
        set(out, ten, 10);
        mov(out, tmp, n);
        divu(out, tmp, ten, digit);
        set(out, p, 1);
        set(out, count, 1);
        let p_le_tenth = |out: &mut dyn Program| {
            less(out, digit, p, true);
            not_acc(out);
        };
        p_le_tenth(out);
        out.op(Op::While);
        mul10(out, p, tmp);
        inc(out, count);
        p_le_tenth(out);
        out.op(Op::EndWhile);

        // print the digits from the most significant. Each digit is at most
        // 9, so it's found by subtracting p = 10^count rather than dividing.
        begin_while(out, count);
        dec(out, count);
        set(out, p, 1);
        mov(out, t, count);
        begin_while(out, t);
        mul10(out, p, tmp);
        dec(out, t);
        end_while(out, t);

        set(out, digit, 0);
        let n_ge_p = |out: &mut dyn Program| {
            less(out, n, p, true);
            not_acc(out);
        };
        n_ge_p(out);
        out.op(Op::While);
        sub_assign(out, n, p);
        inc(out, digit);
        n_ge_p(out);
        out.op(Op::EndWhile);

        digit.to(out);
        out.op(Op::Set(b'0' as u64));
        out.op(Op::Add);
        digit.from(out);
        out.op(Op::Write);
        end_while(out, count);
    });
}

/// Prints `src` in decimal.
pub fn putint(out: &mut dyn Program, src: &Location) {
    mov(out, T0, src);
    routine(out, "puti", |out| {
        is_negative(out, T0, T2);
        begin_if(out, T2);
        puts(out, "-");
        neg_assign(out, T0);
        end_if(out);
        // T0 is now the magnitude, which is right even for -2^63 when read
        // as unsigned
        putu_routine(out);
    });
}

/// Prints `src` in decimal as an unsigned value.
pub fn putuint(out: &mut dyn Program, src: &Location) {
    mov(out, T0, src);
    putu_routine(out);
}

/// Reads a decimal integer: skips leading whitespace, takes an optional `-`,
/// then digits. Consumes the first character after them, and reads 0 if there
/// are no digits.
pub fn getint(out: &mut dyn Program, dst: &Location) {
    routine(out, "geti", |out| {
        let (n, c, flag, tmp, neg) = (T0, T1, T2, T3, T4);
        let read = |out: &mut dyn Program| getchar(out, c);
        set(out, n, 0);
        set(out, neg, 0);

        // whitespace is 1 to 32; EOF is -1
        read(out);
        raw_while(out, flag, |out| in_range(out, c, 1, 32, flag), |out| read(out));

        in_range(out, c, b'-' as i64, b'-' as i64, flag);
        begin_if(out, flag);
        set(out, neg, 1);
        read(out);
        end_if(out);

        raw_while(
            out,
            flag,
            |out| in_range(out, c, b'0' as i64, b'9' as i64, flag),
            |out| {
                mul10(out, n, tmp);
                set_acc(out, -(b'0' as i64));
                c.to(out);
                out.op(Op::Add);
                c.from(out);
                n.to(out);
                out.op(Op::Add);
                out.op(Op::Store);
                n.from(out);
                read(out);
            },
        );

        begin_if(out, neg);
        neg_assign(out, n);
        end_if(out);
    });
    mov(out, dst, T0);
}

// Pointers, the stack and the heap.

/// Stores the address of `loc` in `dst`, so that `dst.deref()` is `loc`.
pub fn addr_of(out: &mut dyn Program, dst: &Location, loc: &Location) {
    loc.to(out);
    out.op(Op::Where);
    loc.from(out);
    store(out, dst);
}

/// T2 = the address of element T8 of the array at address T7. Uses T0 to T5
/// and T9.
fn index_routine(out: &mut dyn Program) {
    routine(out, "index", |out| {
        // the cell size is small (1 or 8), so add i that many times rather
        // than multiplying
        cell_size(out, T5);
        set(out, T2, 0);
        begin_while(out, T5);
        add_assign(out, T2, T8);
        dec(out, T5);
        end_while(out, T5);
        add_assign(out, T2, T7);
    });
}

/// `dst` = the address of element `i` of the array that `base` points to.
pub fn index(out: &mut dyn Program, dst: &Location, base: &Location, i: &Location) {
    mov(out, T7, base);
    mov(out, T8, i);
    index_routine(out);
    mov(out, dst, T2);
}

/// `dst = base[i]`, where `base` holds an address.
pub fn load_index(out: &mut dyn Program, dst: &Location, base: &Location, i: &Location) {
    index(out, T2, base, i);
    mov(out, dst, &T2.deref());
}

/// `base[i] = src`, where `base` holds an address.
pub fn store_index(out: &mut dyn Program, base: &Location, i: &Location, src: &Location) {
    index(out, T2, base, i);
    mov(out, &T2.deref(), src);
}

/// Sets up the stack and the heap for a tape of `DEFAULT_CELLS` cells. Run
/// this (or `init_with`) once before using the stack, the heap or functions.
pub fn init(out: &mut dyn Program) {
    init_with(out, DEFAULT_CELLS);
}

/// Sets up the stack and the heap for a tape of `cells` cells. The stack grows
/// up from `STACK_START` and the heap grows down from the end of the tape.
pub fn init_with(out: &mut dyn Program, cells: u64) {
    addr_of(out, SP, STACK_START);
    mov(out, FP, SP);
    // GP = the address just past the last cell, without moving off the tape
    addr_of(out, GP, &reg(cells - 1));
    cell_size(out, T0);
    add_assign(out, GP, T0);
}

/// Moves SP by `n` cells: reserves stack space if positive, frees it if negative.
pub fn alloc(out: &mut dyn Program, n: i64) {
    // SP = &SP[n], moving by whole cells so it works with either address unit
    addr_of(out, SP, &SP.deref().offset(n));
}

pub fn push(out: &mut dyn Program, src: &Location) {
    mov(out, &SP.deref(), src);
    alloc(out, 1);
}

pub fn pop(out: &mut dyn Program, dst: &Location) {
    alloc(out, -1);
    mov(out, dst, &SP.deref());
}

/// Allocates `n` cells on the heap and stores their address in `dst`. The heap
/// only grows, and nothing checks that it stays clear of the stack.
pub fn heap_alloc(out: &mut dyn Program, dst: &Location, n: &Location) {
    // GP = &GP[-n]
    mov(out, T7, GP);
    mov(out, T8, n);
    neg_assign(out, T8);
    index_routine(out);
    mov(out, GP, T2);
    mov(out, dst, GP);
}

/// Like `heap_alloc`, for a constant number of cells.
pub fn heap_alloc_const(out: &mut dyn Program, dst: &Location, n: i64) {
    mov(out, T7, GP);
    set_int(out, T8, -n);
    index_routine(out);
    mov(out, GP, T2);
    mov(out, dst, GP);
}

// Strings: one character per cell, ending with a 0.

/// Writes `s` and its terminating 0 to the cells that `ptr` points to.
pub fn store_str(out: &mut dyn Program, ptr: &Location, s: &str) {
    for (i, b) in s.bytes().chain([0]).enumerate() {
        set(out, &ptr.deref().offset(i as i64), b as u64);
    }
}

/// Allocates `s` on the heap and stores its address in `dst`.
pub fn heap_str(out: &mut dyn Program, dst: &Location, s: &str) {
    heap_alloc_const(out, dst, s.len() as i64 + 1);
    store_str(out, dst, s);
}

/// Moves the pointer in `ptr` to the next cell.
fn advance(out: &mut dyn Program, ptr: &Location) {
    addr_of(out, ptr, &ptr.deref().offset(1));
}

/// Prints the string that `ptr` points to.
pub fn print_str(out: &mut dyn Program, ptr: &Location) {
    mov(out, T12, ptr);
    routine(out, "prints", |out| {
        load(out, &T12.deref());
        out.op(Op::While);
        out.op(Op::Write);
        advance(out, T12);
        load(out, &T12.deref());
        out.op(Op::EndWhile);
    });
}

/// `dst` = the length of the string that `ptr` points to.
pub fn str_len(out: &mut dyn Program, dst: &Location, ptr: &Location) {
    mov(out, T12, ptr);
    routine(out, "strlen", |out| {
        set(out, T14, 0);
        load(out, &T12.deref());
        out.op(Op::While);
        inc(out, T14);
        advance(out, T12);
        load(out, &T12.deref());
        out.op(Op::EndWhile);
    });
    mov(out, dst, T14);
}

/// Compares the strings that `a` and `b` point to, like C's `strcmp`: `dst`
/// is -1, 0 or 1 as `a` sorts before, the same as, or after `b`.
pub fn str_cmp(out: &mut dyn Program, dst: &Location, a: &Location, b: &Location) {
    mov(out, T12, a);
    mov(out, T13, b);
    routine(out, "strcmp", |out| {
        let (go, ca, cb, diff, d) = (T5, T6, T7, T8, T14);
        set(out, go, 1);
        begin_while(out, go);
        mov(out, ca, &T12.deref());
        mov(out, cb, &T13.deref());
        mov(out, d, ca);
        sub_assign(out, d, cb);
        // keep going while the characters match and the string goes on:
        // (ca != 0) - (d != 0) > 0
        test_zero(out, diff, d, 0, 1);
        test_zero(out, go, ca, 0, 1);
        load(out, diff);
        out.op(Op::Neg);
        go.to(out);
        out.op(Op::Add);
        out.op(Op::Positive);
        out.op(Op::Store);
        go.from(out);
        advance(out, T12);
        advance(out, T13);
        end_while(out, go);
        // d = sign(d) = (d > 0) - (-d > 0)
        load(out, d);
        out.op(Op::Neg);
        out.op(Op::Positive);
        out.op(Op::Neg);
        store(out, ca);
        load(out, d);
        out.op(Op::Positive);
        ca.to(out);
        out.op(Op::Add);
        ca.from(out);
        store(out, d);
    });
    mov(out, dst, T14);
}

/// Reads a line into the buffer that `buf` points to, which has room for
/// `cap` cells. Stops at a newline (which isn't stored), at the end of input,
/// or when the buffer is full, and always ends the string with a 0. `dst` is
/// set to the number of characters stored.
pub fn read_line(out: &mut dyn Program, dst: &Location, buf: &Location, cap: &Location) {
    mov(out, T12, buf);
    mov(out, T13, cap);
    routine(out, "getline", |out| {
        let (p, room, count, go, c, stop, eof) = (T12, T13, T14, T5, T6, T7, T8);
        set(out, count, 0);
        // leave room for the 0
        dec(out, room);
        let room_left = |out: &mut dyn Program| {
            load(out, room);
            out.op(Op::Positive);
            store(out, go);
        };
        room_left(out);
        begin_while(out, go);
        getchar(out, c);
        in_range(out, c, b'\n' as i64, b'\n' as i64, stop);
        is_negative(out, c, eof);
        add_assign(out, stop, eof);
        begin_if(out, stop);
        set(out, go, 0);
        begin_else(out);
        mov(out, &p.deref(), c);
        advance(out, p);
        dec(out, room);
        inc(out, count);
        room_left(out);
        end_if(out);
        end_while(out, go);
        set(out, &p.deref(), 0);
    });
    mov(out, dst, T14);
}

pub mod ir;
pub mod llvm;
pub mod opt;

#[cfg(test)]
mod tests;
