//! Writing programs for the VM the easy way: variables, expressions, and
//! `if`/`while`/`loop` as closures.
//!
//! ```
//! use bf::ir::Program;
//!
//! let mut p = Program::new();
//! p.function("fib", &["n"], |f| {
//!     let n = f.arg("n");
//!     f.if_(n.lt(2), |f| f.ret(n));
//!     let a = f.call("fib", n - 1);
//!     let b = f.call("fib", n - 2);
//!     f.ret(a + b);
//! });
//! p.main(|f| {
//!     let n = f.read_int();
//!     let r = f.call("fib", n);
//!     f.print_int(r);
//! });
//! assert_eq!(p.run(b"10"), "55");
//! let ops = p.compile(); // VM ops, optimized: what `bf` turns into C
//! ```
//!
//! **Variables** (`f.var(..)`, `f.arg(..)`) are what change: `f.set(x, x + 1)`.
//! (`f.once(e)` fixes a value that never changes, without a variable.)
//! **Expressions** (`Expr`) are formulas built from variables, numbers and
//! operators: `x + 1`, `a.lt(b)`, `arr.at(i)`. An expression is worked out
//! where it's used, every time it's used, like a C expression. Things that
//! do something (calls, reading input, allocating) happen where they're
//! written, and give their result as a variable. A call's arguments are a
//! tuple: `f.call("gcd", (a, b))`, or one on its own: `f.call("fib", n - 1)`.
//!
//! Every value is a cell: a whole number (64 bits in the C backends, at
//! least 16 on the CPU), and true is 1, false 0. Comparisons and division
//! are signed; `ltu` and friends compare unsigned.
//!
//! **Memory** is arrays of cells: `f.array(n)` (on the stack, for the rest
//! of the call), `f.alloc(n)` (on the heap, for good) or `f.gc_alloc(n)`
//! (freed by a garbage collector once nothing points to it; a program uses
//! `alloc` or `gc_alloc`, not both), and `p.global(..)`. They're addresses:
//! `a.at(i)` reads element `i`, `f.set(a.at(i), v)` writes it, and
//! `a.index(i)` is element `i`'s address (never `a + i`: an address isn't
//! the number of a cell). `f.addr(x)` is a variable's address, a pointer to
//! it.
//!
//! **C functions** are declared with `p.external(name, params)` and called
//! like any other. In C they're written with `bf.h` (`C_HEADER`):
//!
//! ```c
//! #include "bf.h"
//! BF_FUNCTION(clamp) {
//!     int64_t x = BF_ARG(0), lo = BF_ARG(1), hi = BF_ARG(2);
//!     BF_RETURN(x < lo ? lo : x > hi ? hi : x);
//! }
//! ```
//!
//! and compiled with the C that `bf` makes of the program. For `run`, give
//! them as Rust with `p.host(name, |args| ...)`.

use super::{lower_with, optimize_with, BinOp, Block, Function, Module, Options, Passes, UnOp, Value};
use crate::interp::{HostFn, Machine};
use crate::Op;
use std::collections::HashMap;
use std::rc::Rc;

/// The C header for writing external functions.
pub const C_HEADER: &str = include_str!("bf.h");

/// The tape the programs are for: the C backends'.
const CELLS: u64 = 100_000;

/// A program being written: its functions, globals and external functions.
pub struct Program {
    module: Module,
    /// The functions outside the program, with how many parameters each.
    externals: HashMap<String, usize>,
    hosts: HashMap<String, Rc<dyn Fn(&[i64]) -> i64>>,
    /// How many functions have been written, to tell their variables apart.
    written: usize,
    mode: Mode,
    /// Which of the optimizer's passes run (as `mode` says, unless
    /// `set_passes` says otherwise).
    passes: Passes,
    /// The tape's size, in cells: the stack and the heap share it.
    cells: u64,
    /// Whether an abort stops the program with a status of 1, through the
    /// external function `bf_exit` (see `Options::exits`).
    exits: bool,
}

/// How a program is compiled: quickly, or into fast code.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub enum Mode {
    /// No optimizing: compiles in a fraction of the time, into bigger,
    /// slower ops. (The checks for the stack running into the heap are on
    /// either way.)
    Debug,
    /// Everything: the IR's optimizer, and the ops' (`asm::opt`): every
    /// pass in `ir::PASSES`.
    #[default]
    Release,
}

impl Default for Program {
    fn default() -> Self {
        Self::new()
    }
}

impl Program {
    pub fn new() -> Self {
        Program { module: Module::new(), externals: HashMap::new(), hosts: HashMap::new(), written: 0, mode: Mode::Release, passes: Passes::all(), cells: CELLS, exits: false }
    }

    /// How `compile` and `run` compile it (Release, unless this says): its
    /// passes as the mode has them (all, or none).
    pub fn set_mode(&mut self, mode: Mode) {
        self.mode = mode;
        self.passes = match mode {
            Mode::Release => Passes::all(),
            Mode::Debug => Passes::none(),
        };
    }

    /// Which of the optimizer's passes run (see `ir::PASSES`), whatever the
    /// mode would have.
    pub fn set_passes(&mut self, passes: Passes) {
        self.passes = passes;
    }

    pub fn passes(&self) -> &Passes {
        &self.passes
    }

    /// Whether an abort (a failed check, `panic`, ...) stops the program
    /// then and there, with a status of 1, by calling the external function
    /// `bf_exit`, which the C backends and the interpreter have; or (the
    /// default, for the CPU in hw/, which has no external functions) returns
    /// call by call to `main`, which ends as if all went well.
    pub fn set_exits(&mut self, exits: bool) {
        self.exits = exits;
    }

    pub fn mode(&self) -> Mode {
        self.mode
    }

    /// How many cells of memory the program has, its stack and its heap
    /// (100,000 unless this says: the VM's interpreter keeps them all). A
    /// program compiled to C needs a tape this big: `-DBF_CELLS=` it.
    pub fn set_cells(&mut self, cells: u64) {
        self.cells = cells;
    }

    pub fn cells(&self) -> u64 {
        self.cells
    }

    /// Writes the program's main code, which runs when it starts.
    pub fn main(&mut self, body: impl FnOnce(&mut Func)) {
        self.written += 1;
        let id = self.written;
        let f = self.module.main();
        Func::write(f, id, true, &[], &self.externals, body);
    }

    /// Writes the function `name`, with parameters named `params` (read
    /// with `f.arg(name)`). It gives back what `f.ret` says, or 0 if it gets
    /// to the end. Functions can call each other in any order.
    pub fn function(&mut self, name: &str, params: &[&str], body: impl FnOnce(&mut Func)) {
        assert!(!self.externals.contains_key(name), "{name} is already an external function");
        self.written += 1;
        let id = self.written;
        let f = self.module.function(name, params.len());
        Func::write(f, id, false, params, &self.externals, body);
    }

    /// Declares `name` as a function outside the program, in C, taking
    /// `params` arguments (see the module's documentation).
    pub fn external(&mut self, name: &str, params: usize) {
        self.module.external(name);
        self.externals.insert(name.to_string(), params);
    }

    /// The external function `name`, as Rust, for `run`.
    pub fn host(&mut self, name: &str, f: impl Fn(&[i64]) -> i64 + 'static) {
        assert!(self.externals.contains_key(name), "{name} isn't declared with `external`");
        self.hosts.insert(name.to_string(), Rc::new(f));
    }

    /// A global array of `cells` cells, all 0 at the start: its address.
    pub fn global(&mut self, cells: u32) -> Expr {
        Expr::global(self.module.add_globals(cells))
    }

    /// The program as VM ops, with the passes it has on (see `set_mode`
    /// and `set_passes`). For C, it's better without `asm-opt`, the ops'
    /// own optimizer: that makes for fewer of the VM's steps, which a C
    /// compiler finds for itself, and what it leaves is C that compiles to
    /// slower code (a frame of a game drew in 13 ms with it and 4.9 ms
    /// without), and it takes time to run.
    pub fn compile(&self) -> Vec<Op> {
        let mut phase = crate::asm::log::phase(crate::asm::log::INFO, "IR to VM ops");
        let mut m = self.module.clone();
        if self.passes.any_ir() {
            optimize_with(&mut m, &self.passes);
        }
        let ops = lower_with(&m, &Options { cells: self.cells, optimize: self.passes.on("asm-opt"), exits: self.exits, ..Options::default() }).unwrap_or_else(|e| panic!("{e}"));
        phase.done(format!("{} ops", ops.len()));
        ops
    }

    /// Runs the compiled program on `input`, giving what it prints.
    pub fn run(&self, input: &[u8]) -> String {
        self.run_status(input).0
    }

    /// Runs the compiled program on `input`, giving what it prints, and the
    /// status it stopped with (see `set_exits`).
    pub fn run_status(&self, input: &[u8]) -> (String, i64) {
        let mut machine = Machine { cells: self.cells as usize + 64, max_steps: u64::MAX, ..Machine::c() };
        for (name, &params) in &self.externals {
            let f = self.hosts.get(name).unwrap_or_else(|| panic!("no `host` for the external function {name}")).clone();
            machine = machine.host(
                name,
                HostFn::new(move |c| {
                    let args = (0..params as i64).map(|i| c.arg(i)).collect::<Result<Vec<_>, _>>()?;
                    c.acc = f(&args);
                    Ok(())
                }),
            );
        }
        let ops = self.compile();
        let mut phase = crate::asm::log::phase(crate::asm::log::INFO, "run on the VM");
        let halted = machine.run(&ops, input).unwrap_or_else(|e| panic!("{e}"));
        phase.done(format!("{} bytes of output, in {} steps", halted.output.len(), halted.steps));
        (String::from_utf8_lossy(&halted.output).into_owned(), halted.status)
    }

    /// The program in the representation underneath, as written and after
    /// optimizing, for seeing what it became.
    pub fn ir(&self) -> (String, String) {
        let mut m = self.module.clone();
        optimize_with(&mut m, &self.passes);
        (self.module.to_string(), m.to_string())
    }
}

/// A variable: a cell that `f.set` changes. Read it by using it in an
/// expression.
#[derive(Clone, Copy, Debug)]
pub struct Var {
    /// Its cell (an alloca), in the function `func`.
    cell: Value,
    func: usize,
}

/// An expression: a formula that's worked out where it's used.
#[derive(Clone, Debug)]
pub struct Expr(Rc<Node>);

#[derive(Debug)]
enum Node {
    Int(i64),
    Var(Var),
    Unary(UnOp, Expr),
    Binary(BinOp, Expr, Expr),
    /// Both nonzero, or either (as 1 or 0).
    And(Expr, Expr),
    Or(Expr, Expr),
    /// The cell at an address.
    Load(Expr),
    /// The cell at an address, which never changes (see `Node::Fixed`).
    Fixed(Expr),
    Global(u32),
    FuncAddr(String),
    /// A variable's address.
    Addr(Var),
    /// A value worked out already (`Func::once`), in function `func`.
    Once(Value, usize),
}

impl Expr {
    fn new(n: Node) -> Expr {
        Expr(Rc::new(n))
    }

    fn global(i: u32) -> Expr {
        Expr::new(Node::Global(i))
    }

    fn binary(&self, op: BinOp, b: impl Into<Expr>) -> Expr {
        Expr::new(Node::Binary(op, self.clone(), b.into()))
    }

    /// Element `i` of the array this is the address of: to read, or to
    /// `set`.
    pub fn at(&self, i: impl Into<Expr>) -> Expr {
        Expr::new(Node::Load(self.index(i)))
    }

    /// Element `i`, which never changes once anything can read it: written
    /// when the array was made (its length, say). It's read once for all
    /// the stores and calls after (see the IR's `Node::Fixed`).
    pub fn fixed_at(&self, i: impl Into<Expr>) -> Expr {
        Expr::new(Node::Fixed(self.index(i)))
    }

    /// The address of element `i` of the array this is the address of.
    pub fn index(&self, i: impl Into<Expr>) -> Expr {
        self.binary(BinOp::Index, i)
    }

    pub fn lt(&self, b: impl Into<Expr>) -> Expr {
        self.binary(BinOp::Lt, b)
    }
    pub fn le(&self, b: impl Into<Expr>) -> Expr {
        self.binary(BinOp::Le, b)
    }
    pub fn gt(&self, b: impl Into<Expr>) -> Expr {
        self.binary(BinOp::Gt, b)
    }
    pub fn ge(&self, b: impl Into<Expr>) -> Expr {
        self.binary(BinOp::Ge, b)
    }
    pub fn eq(&self, b: impl Into<Expr>) -> Expr {
        self.binary(BinOp::Eq, b)
    }
    pub fn ne(&self, b: impl Into<Expr>) -> Expr {
        self.binary(BinOp::Ne, b)
    }
    /// The comparisons, of the cells as unsigned numbers.
    pub fn ltu(&self, b: impl Into<Expr>) -> Expr {
        self.binary(BinOp::LtU, b)
    }
    pub fn leu(&self, b: impl Into<Expr>) -> Expr {
        self.binary(BinOp::LeU, b)
    }
    pub fn gtu(&self, b: impl Into<Expr>) -> Expr {
        self.binary(BinOp::GtU, b)
    }
    pub fn geu(&self, b: impl Into<Expr>) -> Expr {
        self.binary(BinOp::GeU, b)
    }
    /// Unsigned division and remainder (`/` and `%` are signed).
    pub fn divu(&self, b: impl Into<Expr>) -> Expr {
        self.binary(BinOp::DivU, b)
    }
    pub fn remu(&self, b: impl Into<Expr>) -> Expr {
        self.binary(BinOp::RemU, b)
    }
    /// Shifting right, filling with 0s (`>>` copies the sign).
    pub fn shru(&self, b: impl Into<Expr>) -> Expr {
        self.binary(BinOp::ShrU, b)
    }
    pub fn min(&self, b: impl Into<Expr>) -> Expr {
        self.binary(BinOp::Min, b)
    }
    pub fn max(&self, b: impl Into<Expr>) -> Expr {
        self.binary(BinOp::Max, b)
    }
    pub fn abs(&self) -> Expr {
        Expr::new(Node::Unary(UnOp::Abs, self.clone()))
    }
    /// Every bit flipped (`!` is logical: 1 for 0, else 0).
    pub fn bitnot(&self) -> Expr {
        Expr::new(Node::Unary(UnOp::Not, self.clone()))
    }
    /// Logical and, or: 1 or 0. (Both sides are always worked out.)
    pub fn and(&self, b: impl Into<Expr>) -> Expr {
        Expr::new(Node::And(self.clone(), b.into()))
    }
    pub fn or(&self, b: impl Into<Expr>) -> Expr {
        Expr::new(Node::Or(self.clone(), b.into()))
    }
}

// (Vars have the same methods, for convenience.)
macro_rules! var_methods {
    ($($name:ident),*) => {
        impl Var {
            $(pub fn $name(&self, b: impl Into<Expr>) -> Expr {
                Expr::from(*self).$name(b)
            })*
            pub fn abs(&self) -> Expr {
                Expr::from(*self).abs()
            }
            pub fn bitnot(&self) -> Expr {
                Expr::from(*self).bitnot()
            }
        }
    };
}
var_methods!(at, fixed_at, index, lt, le, gt, ge, eq, ne, ltu, leu, gtu, geu, divu, remu, shru, min, max, and, or);

impl From<i64> for Expr {
    fn from(k: i64) -> Expr {
        Expr::new(Node::Int(k))
    }
}

impl From<Var> for Expr {
    fn from(v: Var) -> Expr {
        Expr::new(Node::Var(v))
    }
}

impl From<&Expr> for Expr {
    fn from(e: &Expr) -> Expr {
        e.clone()
    }
}

impl From<&Var> for Expr {
    fn from(v: &Var) -> Expr {
        Expr::from(*v)
    }
}

impl From<char> for Expr {
    fn from(c: char) -> Expr {
        Expr::from(c as i64)
    }
}

macro_rules! operators {
    ($($trait:ident $method:ident $op:ident),*) => {$(
        impl<T: Into<Expr>> std::ops::$trait<T> for Expr {
            type Output = Expr;
            fn $method(self, b: T) -> Expr {
                self.binary(BinOp::$op, b)
            }
        }
        impl<T: Into<Expr>> std::ops::$trait<T> for &Expr {
            type Output = Expr;
            fn $method(self, b: T) -> Expr {
                self.binary(BinOp::$op, b)
            }
        }
        impl<T: Into<Expr>> std::ops::$trait<T> for Var {
            type Output = Expr;
            fn $method(self, b: T) -> Expr {
                Expr::from(self).binary(BinOp::$op, b)
            }
        }
        impl std::ops::$trait<Expr> for i64 {
            type Output = Expr;
            fn $method(self, b: Expr) -> Expr {
                Expr::from(self).binary(BinOp::$op, b)
            }
        }
        impl std::ops::$trait<Var> for i64 {
            type Output = Expr;
            fn $method(self, b: Var) -> Expr {
                Expr::from(self).binary(BinOp::$op, b)
            }
        }
    )*};
}
operators!(Add add Add, Sub sub Sub, Mul mul Mul, Div div Div, Rem rem Rem, BitAnd bitand And, BitOr bitor Or, BitXor bitxor Xor, Shl shl Shl, Shr shr Shr);

impl std::ops::Neg for Expr {
    type Output = Expr;
    fn neg(self) -> Expr {
        Expr::new(Node::Unary(UnOp::Neg, self))
    }
}

impl std::ops::Neg for Var {
    type Output = Expr;
    fn neg(self) -> Expr {
        -Expr::from(self)
    }
}

/// Logical not: 1 for 0, else 0.
impl std::ops::Not for Expr {
    type Output = Expr;
    fn not(self) -> Expr {
        Expr::new(Node::Unary(UnOp::LNot, self))
    }
}

impl std::ops::Not for Var {
    type Output = Expr;
    fn not(self) -> Expr {
        !Expr::from(self)
    }
}

/// A call's arguments: none `()`, one, a tuple of up to 8, or a `Vec<Expr>`.
pub trait Args {
    fn exprs(self) -> Vec<Expr>;
}

impl Args for () {
    fn exprs(self) -> Vec<Expr> {
        vec![]
    }
}

impl<T: Into<Expr>> Args for T {
    fn exprs(self) -> Vec<Expr> {
        vec![self.into()]
    }
}

impl Args for Vec<Expr> {
    fn exprs(self) -> Vec<Expr> {
        self
    }
}

macro_rules! tuple_args {
    ($($t:ident),*) => {
        impl<$($t: Into<Expr>),*> Args for ($($t,)*) {
            #[allow(non_snake_case)]
            fn exprs(self) -> Vec<Expr> {
                let ($($t,)*) = self;
                vec![$($t.into()),*]
            }
        }
    };
}
tuple_args!(A, B);
tuple_args!(A, B, C);
tuple_args!(A, B, C, D);
tuple_args!(A, B, C, D, E);
tuple_args!(A, B, C, D, E, F);
tuple_args!(A, B, C, D, E, F, G);
tuple_args!(A, B, C, D, E, F, G, H);

/// What `set` can change: a variable, or a cell `a.at(i)`.
pub enum Place {
    Var(Var),
    Cell(Expr),
}

impl From<Var> for Place {
    fn from(v: Var) -> Place {
        Place::Var(v)
    }
}

impl From<Expr> for Place {
    fn from(e: Expr) -> Place {
        match &*e.0 {
            Node::Load(addr) => Place::Cell(addr.clone()),
            Node::Var(v) => Place::Var(*v),
            _ => panic!("only a variable or a cell (`a.at(i)`) can be set"),
        }
    }
}

impl From<&Expr> for Place {
    fn from(e: &Expr) -> Place {
        Place::from(e.clone())
    }
}

/// A function being written.
pub struct Func<'a> {
    f: &'a mut Function,
    id: usize,
    main: bool,
    /// The first block, which only allocates the variables (it's ended
    /// when the function is finished), and the parameters, as variables.
    entry: Block,
    params: Vec<(String, Var)>,
    externals: &'a HashMap<String, usize>,
    /// The loops being written: where `continue` and `break` go.
    loops: Vec<(Block, Block)>,
}

impl<'a> Func<'a> {
    fn write(f: &'a mut Function, id: usize, main: bool, params: &[&str], externals: &'a HashMap<String, usize>, body: impl FnOnce(&mut Func)) {
        let entry = f.entry();
        let start = f.new_block(0);
        let mut func = Func { f, id, main, entry, params: vec![], externals, loops: vec![] };
        func.f.switch_to(start);
        for (i, name) in params.iter().enumerate() {
            let value = func.f.param(i);
            let v = func.new_var();
            func.f.store(v.cell, value);
            func.params.push((name.to_string(), v));
        }
        body(&mut func);
        if !func.ended() {
            func.ret(0);
        }
        func.f.switch_to(entry);
        func.f.jump(start, &[]);
    }

    fn ended(&self) -> bool {
        self.f.terminator(self.f.current()).is_some()
    }

    /// Carries on in a new block nothing jumps to, after `ret`, `break` and
    /// `continue` (so code after them is allowed, and never runs).
    fn after_end(&mut self) {
        let dead = self.f.new_block(0);
        self.f.switch_to(dead);
    }

    fn new_var(&mut self) -> Var {
        let here = self.f.current();
        self.f.switch_to(self.entry);
        let cell = self.f.alloca(1);
        self.f.switch_to(here);
        Var { cell, func: self.id }
    }

    fn eval(&mut self, e: &Expr) -> Value {
        match &*e.0 {
            Node::Int(k) => self.f.int(*k),
            Node::Var(v) => {
                assert_eq!(v.func, self.id, "a variable used outside the function it belongs to");
                self.f.load(v.cell)
            }
            Node::Unary(op, a) => {
                let a = self.eval(a);
                self.f.unary(*op, a)
            }
            Node::Binary(op, a, b) => {
                let (a, b) = (self.eval(a), self.eval(b));
                self.f.binary(*op, a, b)
            }
            Node::And(a, b) | Node::Or(a, b) => {
                let zero = self.f.int(0);
                let a = self.eval(a);
                let a = self.f.ne(a, zero);
                let b = self.eval(b);
                let b = self.f.ne(b, zero);
                if matches!(&*e.0, Node::And(..)) { self.f.and(a, b) } else { self.f.or(a, b) }
            }
            Node::Load(addr) => {
                let addr = self.eval(addr);
                self.f.load(addr)
            }
            Node::Fixed(addr) => {
                let addr = self.eval(addr);
                self.f.load_fixed(addr)
            }
            Node::Global(i) => self.f.global_addr(*i),
            Node::FuncAddr(name) => self.f.func_addr(name),
            Node::Addr(v) => {
                assert_eq!(v.func, self.id, "a variable used outside the function it belongs to");
                v.cell
            }
            Node::Once(v, func) => {
                assert_eq!(*func, self.id, "a value used outside the function it belongs to");
                *v
            }
        }
    }

    /// A result, kept in a new variable.
    fn keep(&mut self, value: Value) -> Var {
        let v = self.new_var();
        self.f.store(v.cell, value);
        v
    }

    /// `e`, worked out here, once: its value, which can be used in the code
    /// after this, in the same branch (or one inside it), without being
    /// worked out again (unlike an expression, which is worked out wherever
    /// it's used). Cheaper than a variable, for a value that never changes;
    /// using it where this code doesn't always run first (after an `if` it's
    /// inside, say) is an error when the program's compiled.
    pub fn once(&mut self, e: impl Into<Expr>) -> Expr {
        let v = self.eval(&e.into());
        Expr::new(Node::Once(v, self.id))
    }

    /// A new variable, set to `init`.
    pub fn var(&mut self, init: impl Into<Expr>) -> Var {
        let value = self.eval(&init.into());
        let v = self.new_var();
        self.f.store(v.cell, value);
        v
    }

    /// The address of variable `v`, as a pointer to it: `p.at(0)` reads it,
    /// `f.set(p.at(0), x)` sets it, and it can be passed to other
    /// functions. (A variable whose address is taken stays in memory; the
    /// others are kept in registers.)
    pub fn addr(&self, v: Var) -> Expr {
        Expr::new(Node::Addr(v))
    }

    /// The parameter `name`, as a variable (which the function can change).
    pub fn arg(&self, name: &str) -> Var {
        match self.params.iter().find(|(n, _)| n == name) {
            Some((_, v)) => *v,
            None => panic!("no parameter called {name}"),
        }
    }

    /// Sets a variable, or a cell (`a.at(i)`), to `value`.
    pub fn set(&mut self, place: impl Into<Place>, value: impl Into<Expr>) {
        let value = self.eval(&value.into());
        match place.into() {
            Place::Var(v) => {
                assert_eq!(v.func, self.id, "a variable used outside the function it belongs to");
                self.f.store(v.cell, value)
            }
            Place::Cell(addr) => {
                let addr = self.eval(&addr);
                self.f.store(addr, value)
            }
        }
    }

    /// `if cond { then }`
    pub fn if_(&mut self, cond: impl Into<Expr>, then: impl FnOnce(&mut Func)) {
        self.if_else(cond, then, |_| {});
    }

    /// `if cond { then } else { otherwise }`
    pub fn if_else(&mut self, cond: impl Into<Expr>, then: impl FnOnce(&mut Func), otherwise: impl FnOnce(&mut Func)) {
        let c = self.eval(&cond.into());
        let (yes, no, after) = (self.f.new_block(0), self.f.new_block(0), self.f.new_block(0));
        self.f.branch(c, yes, &[], no, &[]);
        self.f.switch_to(yes);
        then(self);
        if !self.ended() {
            self.f.jump(after, &[]);
        }
        self.f.switch_to(no);
        otherwise(self);
        if !self.ended() {
            self.f.jump(after, &[]);
        }
        self.f.switch_to(after);
    }

    /// `while cond { body }`: `cond` is worked out again before every time
    /// round.
    pub fn while_(&mut self, cond: impl Into<Expr>, body: impl FnOnce(&mut Func)) {
        let cond = cond.into();
        let (head, inside, after) = (self.f.new_block(0), self.f.new_block(0), self.f.new_block(0));
        self.f.jump(head, &[]);
        self.f.switch_to(head);
        let c = self.eval(&cond);
        self.f.branch(c, inside, &[], after, &[]);
        self.f.switch_to(inside);
        self.in_loop(head, after, body);
        self.f.switch_to(after);
    }

    /// `loop { body }`, which only `break` (or `ret`) leaves.
    pub fn loop_(&mut self, body: impl FnOnce(&mut Func)) {
        let (head, after) = (self.f.new_block(0), self.f.new_block(0));
        self.f.jump(head, &[]);
        self.f.switch_to(head);
        self.in_loop(head, after, body);
        self.f.switch_to(after);
    }

    /// `for i in from..to { body }`, with `i` a new variable.
    pub fn for_(&mut self, from: impl Into<Expr>, to: impl Into<Expr>, body: impl FnOnce(&mut Func, Var)) {
        let i = self.var(from);
        let to = to.into();
        let (head, inside, step, after) = (self.f.new_block(0), self.f.new_block(0), self.f.new_block(0), self.f.new_block(0));
        self.f.jump(head, &[]);
        self.f.switch_to(head);
        let c = self.eval(&i.lt(to));
        self.f.branch(c, inside, &[], after, &[]);
        self.f.switch_to(inside);
        // (`continue` goes on to the next i)
        self.in_loop(step, after, |f| body(f, i));
        self.f.switch_to(step);
        self.set(i, i + 1);
        self.f.jump(head, &[]);
        self.f.switch_to(after);
    }

    fn in_loop(&mut self, next: Block, after: Block, body: impl FnOnce(&mut Func)) {
        self.loops.push((next, after));
        body(self);
        self.loops.pop();
        if !self.ended() {
            self.f.jump(next, &[]);
        }
    }

    /// Leaves the innermost loop.
    pub fn break_(&mut self) {
        let (_, after) = *self.loops.last().expect("break outside a loop");
        self.f.jump(after, &[]);
        self.after_end();
    }

    /// Goes on to the next time round the innermost loop.
    pub fn continue_(&mut self) {
        let (next, _) = *self.loops.last().expect("continue outside a loop");
        self.f.jump(next, &[]);
        self.after_end();
    }

    /// Returns `value` from the function (or, in `main`, stops the program).
    pub fn ret(&mut self, value: impl Into<Expr>) {
        let v = self.eval(&value.into());
        if self.main {
            self.f.ret_void();
        } else {
            self.f.ret(v);
        }
        self.after_end();
    }

    /// Calls `name`, a function of the program or an external one, giving
    /// what it returns.
    pub fn call(&mut self, name: &str, args: impl Args) -> Var {
        let args: Vec<Value> = args.exprs().iter().map(|a| self.eval(a)).collect();
        let r = match self.externals.get(name) {
            Some(&n) => {
                assert_eq!(n, args.len(), "{name} takes {n} arguments");
                self.f.call_extern(name, &args)
            }
            None => self.f.call(name, &args),
        };
        self.keep(r)
    }

    /// The address of the function `name`, for `call_at`.
    pub fn func_addr(&mut self, name: &str) -> Expr {
        Expr::new(Node::FuncAddr(name.to_string()))
    }

    /// Calls the function whose address `f` is (from `func_addr`).
    pub fn call_at(&mut self, f: impl Into<Expr>, args: impl Args) -> Var {
        let f = self.eval(&f.into());
        let args: Vec<Value> = args.exprs().iter().map(|a| self.eval(a)).collect();
        let r = self.f.call_indirect(f, &args);
        self.keep(r)
    }

    /// An array of `cells` cells on the stack, for the rest of this call: its
    /// address.
    pub fn array(&mut self, cells: u64) -> Var {
        let here = self.f.current();
        self.f.switch_to(self.entry);
        let a = self.f.alloca(cells);
        self.f.switch_to(here);
        self.keep(a)
    }

    /// An array of `cells` cells on the heap, never freed: its address.
    pub fn alloc(&mut self, cells: impl Into<Expr>) -> Var {
        let n = self.eval(&cells.into());
        let a = self.f.heap_alloc(n);
        self.keep(a)
    }

    /// An array of `cells` cells, all 0, that's freed once nothing points
    /// into it: its address.
    pub fn gc_alloc(&mut self, cells: impl Into<Expr>) -> Var {
        let n = self.eval(&cells.into());
        let a = self.f.gc_alloc(n);
        self.keep(a)
    }

    /// Like `gc_alloc`, for an array that will only ever hold numbers (never
    /// an address): the collector doesn't look in it.
    pub fn gc_alloc_data(&mut self, cells: impl Into<Expr>) -> Var {
        let n = self.eval(&cells.into());
        let a = self.f.gc_alloc_data(n);
        self.keep(a)
    }

    pub fn print(&mut self, s: &str) {
        self.f.puts(s);
    }

    pub fn print_int(&mut self, x: impl Into<Expr>) {
        let v = self.eval(&x.into());
        self.f.put_int(v);
    }

    /// Prints a cell as a character (its low byte).
    pub fn print_char(&mut self, c: impl Into<Expr>) {
        let v = self.eval(&c.into());
        self.f.put_char(v);
    }

    /// The next byte of input, or -1 at the end.
    pub fn read_char(&mut self) -> Var {
        let c = self.f.get_char();
        self.keep(c)
    }

    /// A number from the input, in decimal.
    pub fn read_int(&mut self) -> Var {
        let n = self.f.get_int();
        self.keep(n)
    }

    /// Stops the program.
    pub fn abort(&mut self) {
        self.f.abort();
        // (the block still needs an end, which never runs)
        if self.main {
            self.f.ret_void();
        } else {
            let zero = self.f.int(0);
            self.f.ret(zero);
        }
        self.after_end();
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn variables_and_loops() {
        let mut p = Program::new();
        p.main(|f| {
            // the sum of the squares up to 10, the odd numbers below 10, and
            // the first square over 50
            let s = f.var(0);
            f.for_(1, 11, |f, i| f.set(s, s + i * i));
            f.print_int(s);
            f.print(" ");
            f.for_(0, 100, |f, i| {
                f.if_(i.ge(10), |f| f.break_());
                f.if_((i % 2).eq(0), |f| f.continue_());
                f.print_int(i);
            });
            f.print(" ");
            let n = f.var(1);
            f.while_((n * n).le(50), |f| f.set(n, n + 1));
            f.print_int(n * n);
            f.print(" ");
            let k = f.var(0);
            f.loop_(|f| {
                f.set(k, k + 3);
                f.if_else(k.gt(20), |f| f.break_(), |f| f.print_char('.'));
            });
            f.print_int(k);
        });
        assert_eq!(p.run(b""), "385 13579 64 ......21");
    }

    #[test]
    fn functions_recursion_and_arguments() {
        let mut p = Program::new();
        p.function("gcd", &["a", "b"], |f| {
            let (a, b) = (f.arg("a"), f.arg("b"));
            f.while_(b.ne(0), |f| {
                let t = f.var(b);
                f.set(b, a % b);
                f.set(a, t);
            });
            f.ret(a);
        });
        p.function("ack", &["m", "n"], |f| {
            let (m, n) = (f.arg("m"), f.arg("n"));
            f.if_(m.eq(0), |f| f.ret(n + 1));
            f.if_(n.eq(0), |f| {
                let r = f.call("ack", (m - 1, 1));
                f.ret(r);
            });
            let inner = f.call("ack", (m, n - 1));
            let r = f.call("ack", (m - 1, inner));
            f.ret(r);
        });
        p.function("nothing", &[], |_| {});
        p.main(|f| {
            let a = f.read_int();
            let b = f.read_int();
            let g = f.call("gcd", (a, b));
            let r = f.call("ack", (2, 3));
            let z = f.call("nothing", ());
            f.print_int(g);
            f.print(" ");
            f.print_int(r);
            f.print(" ");
            f.print_int(z);
        });
        assert_eq!(p.run(b"1071 462"), "21 9 0");
    }

    #[test]
    fn arrays_globals_and_function_addresses() {
        let mut p = Program::new();
        let counter = p.global(1);
        let c = counter.clone();
        p.function("bump", &["by"], move |f| {
            f.set(c.at(0), c.at(0) + f.arg("by"));
            f.ret(c.at(0));
        });
        p.function("twice", &["x"], |f| f.ret(f.arg("x") * 2));
        p.main(move |f| {
            // a sieve on the heap, and the primes kept in an array on the stack
            let n = 50;
            let sieve = f.alloc(n);
            f.for_(0, n, |f, i| f.set(sieve.at(i), 1));
            let primes = f.array(20);
            let count = f.var(0);
            f.for_(2, n, |f, i| {
                f.if_(sieve.at(i), |f| {
                    f.set(primes.at(count), i);
                    f.set(count, count + 1);
                    let j = f.var(i * i);
                    f.while_(j.lt(n), |f| {
                        f.set(sieve.at(j), 0);
                        f.set(j, j + i);
                    });
                });
            });
            f.for_(0, count, |f, k| {
                f.print_int(primes.at(k));
                f.print_char(' ');
            });
            f.call("bump", 5);
            f.call("bump", 7);
            f.print_int(counter.at(0));
            f.print(" ");
            let g = f.func_addr("twice");
            let r = f.call_at(g, 21);
            f.print_int(r);
        });
        assert_eq!(p.run(b""), "2 3 5 7 11 13 17 19 23 29 31 37 41 43 47 12 42");
    }

    #[test]
    fn garbage_collected_lists() {
        // a million cells' worth of short lists, on a tape of 100000: only
        // because the collector frees the old ones
        let mut p = Program::new();
        p.function("cons", &["head", "tail"], |f| {
            let c = f.gc_alloc(2);
            f.set(c.at(0), f.arg("head"));
            f.set(c.at(1), f.arg("tail"));
            f.ret(c);
        });
        p.function("sum", &["l"], |f| {
            let (l, s) = (f.arg("l"), f.var(0));
            f.while_(l.ne(0), |f| {
                f.set(s, s + l.at(0));
                f.set(l, l.at(1));
            });
            f.ret(s);
        });
        p.main(|f| {
            let total = f.var(0);
            f.for_(0, 5000, |f, _| {
                let l = f.var(0);
                f.for_(1, 101, |f, i| {
                    let c = f.call("cons", (i, l));
                    f.set(l, c);
                });
                let s = f.call("sum", l);
                f.set(total, total + s);
            });
            f.print_int(total);
        });
        assert_eq!(p.run(b""), (5000 * 5050).to_string());
    }

    #[test]
    fn reading_input_and_stopping() {
        let mut p = Program::new();
        p.main(|f| {
            // echoes the input in upper case, up to a '!'
            f.loop_(|f| {
                let c = f.read_char();
                f.if_(c.eq(-1), |f| f.break_());
                f.if_(c.eq('!'), |f| f.abort());
                f.if_else(c.ge('a').and(c.le('z')), |f| f.print_char(c - 32), |f| f.print_char(c));
            });
            f.print("never");
        });
        assert_eq!(p.run(b"hi there! not this"), "HI THERE");
    }

    #[test]
    fn external_functions() {
        let mut p = Program::new();
        p.external("clamp", 3);
        p.external("total", 2);
        p.main(|f| {
            let a = f.alloc(3);
            f.for_(0, 3, |f, i| f.set(a.at(i), i * 10 + 1));
            let x = f.read_int();
            let c = f.call("clamp", (x, 0, 10));
            let t = f.call("total", (a, 3));
            f.print_int(c);
            f.print(" ");
            f.print_int(t);
        });
        p.host("clamp", |a| a[0].clamp(a[1], a[2]));
        let total = |_: &[i64]| 0;
        // (`run` can't see memory through a host function's arguments, so
        // total is checked in C below)
        p.host("total", total);
        assert_eq!(p.run(b"42"), "10 0");
        // in C, with bf.h, through the C backend
        let Some(clang) = ["/opt/homebrew/opt/llvm/bin/clang", "clang"]
            .into_iter()
            .find(|c| std::process::Command::new(c).arg("--version").output().is_ok_and(|o| o.status.success()))
        else {
            return eprintln!("skipped: no clang");
        };
        let dir = std::env::temp_dir().join(format!("bf-ir-ffi-{}", std::process::id()));
        std::fs::create_dir_all(&dir).unwrap();
        std::fs::write(dir.join("bf.h"), C_HEADER).unwrap();
        std::fs::write(
            dir.join("lib.c"),
            "#include \"bf.h\"\n\
             BF_FUNCTION(clamp) { int64_t x = BF_ARG(0), lo = BF_ARG(1), hi = BF_ARG(2); BF_RETURN(x < lo ? lo : x > hi ? hi : x); }\n\
             BF_FUNCTION(total) { int64_t *a = BF_POINTER(0), s = 0; for (int64_t i = 0; i < BF_ARG(1); i++) s += a[i]; BF_RETURN(s); }\n",
        )
        .unwrap();
        use crate::Target;
        std::fs::write(dir.join("p.c"), crate::backends::LiteralC.compile(&p.compile())).unwrap();
        let built = std::process::Command::new(clang)
            .args(["-O2", "-fwrapv", "-w", "-o"])
            .arg(dir.join("p"))
            .arg(dir.join("p.c"))
            .arg(dir.join("lib.c"))
            .output()
            .unwrap();
        assert!(built.status.success(), "{}", String::from_utf8_lossy(&built.stderr));
        use std::io::Write;
        let mut child = std::process::Command::new(dir.join("p")).stdin(std::process::Stdio::piped()).stdout(std::process::Stdio::piped()).spawn().unwrap();
        child.stdin.take().unwrap().write_all(b"42").unwrap();
        assert_eq!(String::from_utf8(child.wait_with_output().unwrap().stdout).unwrap(), "10 33");
        let _ = std::fs::remove_dir_all(&dir);
    }

    #[test]
    fn variables_become_registers() {
        // after optimizing, a loop on variables has no loads or stores left
        let mut p = Program::new();
        p.main(|f| {
            let s = f.var(0);
            let n = f.read_int();
            f.for_(0, n, |f, i| f.set(s, s + i));
            f.print_int(s);
        });
        let (_, optimized) = p.ir();
        assert!(!optimized.contains("load") && !optimized.contains("store") && !optimized.contains("alloca"), "{optimized}");
        assert_eq!(p.run(b"100"), "4950");
    }

    #[test]
    fn pointers_to_variables() {
        let mut p = Program::new();
        p.function("swap", &["a", "b"], |f| {
            let (a, b) = (f.arg("a"), f.arg("b"));
            let t = f.var(a.at(0));
            f.set(a.at(0), b.at(0));
            f.set(b.at(0), t);
        });
        p.main(|f| {
            let x = f.var(1);
            let y = f.var(2);
            let (px, py) = (f.addr(x), f.addr(y));
            f.call("swap", (px.clone(), py));
            f.print_int(x);
            f.print_int(y);
            f.set(px.at(0), 7);
            f.print_int(x);
        });
        assert_eq!(p.run(b""), "217");
    }

    #[test]
    fn returning_from_inside_a_loop() {
        // (the first difference of two arrays, compared: like comparing strings)
        let mut p = Program::new();
        p.function("less", &["a", "b"], |f| {
            let (a, b) = (f.arg("a"), f.arg("b"));
            let n = f.var(a.at(0).min(b.at(0)));
            f.for_(0, n, |f, i| f.if_(a.at(i + 1).ne(b.at(i + 1)), |f| f.ret(a.at(i + 1).lt(b.at(i + 1)))));
            f.ret(a.at(0).lt(b.at(0)));
        });
        p.main(|f| {
            let (a, b) = (f.alloc(4), f.alloc(4));
            for (i, (x, y)) in [(3, 3), (1, 1), (2, 5), (9, 0)].iter().enumerate() {
                f.set(a.at(i as i64), *x);
                f.set(b.at(i as i64), *y);
            }
            let r = f.call("less", (a, b));
            f.print_int(r);
        });
        assert_eq!(p.run(b""), "1");
    }

    #[test]
    fn negative_numbers_in_loops() {
        // digits of a number, the way fern's runtime makes a string of one
        let mut p = Program::new();
        p.function("digits", &["n"], |f| {
            let n = f.arg("n");
            let negative = f.var(n.lt(0));
            let m = f.var(n);
            f.if_(negative, |f| f.set(m, -m));
            let len = f.var(0);
            f.loop_(|f| {
                f.print_int(m % 10);
                f.set(len, len + 1);
                f.set(m, m / 10);
                f.if_(m.eq(0), |f| f.break_());
            });
            f.ret(len);
        });
        p.main(|f| {
            let r = f.call("digits", -42);
            f.print_char(' ');
            f.print_int(r);
        });
        assert_eq!(p.run(b""), "24 2");
    }

    #[test]
    fn numbers_to_strings_with_a_constant() {
        // fern's runtime's int-to-string, given a constant
        let mut p = Program::new();
        p.function("itos", &["n"], |f| {
            let n = f.arg("n");
            let digits = f.array(24);
            let negative = f.var(n.lt(0));
            let m = f.var(n);
            f.if_(negative, |f| f.set(m, -m));
            let len = f.var(0);
            f.loop_(|f| {
                f.set(digits.at(len), m % 10 + 48);
                f.set(len, len + 1);
                f.set(m, m / 10);
                f.if_(m.eq(0), |f| f.break_());
            });
            let total = f.var(len + negative);
            let r = f.gc_alloc(total + 1);
            f.set(r.at(0), total);
            f.if_(negative, |f| f.set(r.at(1), '-'));
            f.for_(0, len, |f, i| f.set(r.at(total - i), digits.at(i)));
            f.ret(r);
        });
        p.main(|f| {
            for k in [4, -4, 1234] {
                let s = f.call("itos", k);
                f.for_(0, s.at(0), |f, i| f.print_char(s.at(i + 1)));
                f.print(" ");
            }
        });
        assert_eq!(p.run(b""), "4 -4 1234 ");
    }
}
