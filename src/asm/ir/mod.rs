//! An SSA intermediate representation that lowers to the `asm` helpers.
//!
//! A [`Module`] holds functions, the first of which is the program itself,
//! `main`. A function is a control-flow graph of blocks, and its values are in
//! SSA form: each is defined exactly once. Instead of phi nodes, blocks take
//! parameters, and every jump to a block passes it arguments.
//!
//! Within a block, values form a DAG. Pure operations (arithmetic, comparisons
//! and address arithmetic) aren't ordered: each is a node that depends only on
//! its operands. Nodes are deduplicated as they're built, so a repeated
//! expression is computed once; they're folded when their operands are
//! constants; and they're only computed if something needs them. Operations
//! with effects (memory, I/O and calls) keep the order they were added in.
//!
//! [`lower`] turns a module into ops. It schedules each block's DAG, assigns
//! values to cells by coloring their interference graph, and picks an asm
//! helper for each node, using the helpers that take a constant where an
//! operand is one. The VM only has structured loops, so control flow becomes a
//! loop that dispatches on a block number. [`optimize`] simplifies a module
//! first, [`verify`] checks it, and [`run`] interprets it directly, as the
//! reference for what the lowered program should do.
//!
//! A module targets every cell width from its minimum (16 bits, unless it's
//! made with [`Module::with_min_width`]) up to 64, and means the same thing on
//! all of them: constants are only folded, and ranges only proven, where the
//! result holds on every one.
//!
//! Memory comes from `alloca`, `heap_alloc` (which never frees), or
//! `gc_alloc`, whose cells a garbage collector frees once nothing points into
//! them; the collector is written in the IR itself, and added when a module
//! that needs it is lowered. A module can also have global cells, and
//! `abort` stops the program from anywhere. Lowered programs check that the
//! stack and the heap don't run into each other, and stop with a message if
//! they would (see [`Options`]).

mod cfg;
pub mod dot;
mod fold;
mod gc;
mod imperative;
mod inline;
mod interp;
mod interproc;
pub mod llvm;
mod loops;
mod lower;
mod memory;
mod opt;
mod prepare;
mod range;
mod sched;
#[cfg(test)]
mod tests;
mod verify;

pub use interp::{run, run_counting, run_with};
pub use lower::{lower, lower_with, Options};
pub use opt::optimize;
pub use verify::verify;

use std::collections::HashMap;
use std::fmt;

/// A value: the result of a node.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct Value(u32);

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct Block(u32);

impl Value {
    fn index(self) -> usize {
        self.0 as usize
    }
}

impl Block {
    fn index(self) -> usize {
        self.0 as usize
    }
}

impl fmt::Display for Value {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "v{}", self.0)
    }
}

impl fmt::Display for Block {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "b{}", self.0)
    }
}

/// Operations on two cells. Each matches the asm helper of the same meaning:
/// signed unless it ends in `U`, wrapping on overflow, with comparisons giving
/// 1 or 0. Division by 0 gives -1 (all ones), and the remainder is the
/// dividend. `Index` is the address of element `b` of the array at `a`.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum BinOp {
    Add,
    Sub,
    Mul,
    Div,
    Rem,
    DivU,
    RemU,
    And,
    Or,
    Xor,
    Shl,
    Shr,
    ShrU,
    Eq,
    Ne,
    Lt,
    Le,
    Gt,
    Ge,
    LtU,
    LeU,
    GtU,
    GeU,
    Min,
    Max,
    Index,
}

impl BinOp {
    pub const ALL: [BinOp; 26] = {
        use BinOp::*;
        [
            Add, Sub, Mul, Div, Rem, DivU, RemU, And, Or, Xor, Shl, Shr, ShrU, Eq, Ne, Lt, Le, Gt, Ge, LtU, LeU, GtU,
            GeU, Min, Max, Index,
        ]
    };

    pub fn name(self) -> &'static str {
        use BinOp::*;
        match self {
            Add => "add",
            Sub => "sub",
            Mul => "mul",
            Div => "div",
            Rem => "rem",
            DivU => "divu",
            RemU => "remu",
            And => "and",
            Or => "or",
            Xor => "xor",
            Shl => "shl",
            Shr => "shr",
            ShrU => "shru",
            Eq => "eq",
            Ne => "ne",
            Lt => "lt",
            Le => "le",
            Gt => "gt",
            Ge => "ge",
            LtU => "ltu",
            LeU => "leu",
            GtU => "gtu",
            GeU => "geu",
            Min => "min",
            Max => "max",
            Index => "index",
        }
    }

    /// The op that gives the same result with its operands swapped, if any.
    fn swapped(self) -> Option<BinOp> {
        use BinOp::*;
        match self {
            Add | Mul | And | Or | Xor | Eq | Ne | Min | Max => Some(self),
            Lt => Some(Gt),
            Gt => Some(Lt),
            Le => Some(Ge),
            Ge => Some(Le),
            LtU => Some(GtU),
            GtU => Some(LtU),
            LeU => Some(GeU),
            GeU => Some(LeU),
            _ => None,
        }
    }
}

/// Operations on one cell. `LNot` is 1 for 0 and 0 otherwise, and `Abs` wraps
/// like `wrapping_abs`.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum UnOp {
    Neg,
    Not,
    LNot,
    Abs,
}

impl UnOp {
    pub fn name(self) -> &'static str {
        match self {
            UnOp::Neg => "neg",
            UnOp::Not => "not",
            UnOp::LNot => "lnot",
            UnOp::Abs => "abs",
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub enum Node {
    // Pure nodes, which form each block's DAG.
    Const(i64),
    /// Parameter `i` of a block.
    Param(Block, usize),
    Unary(UnOp, Value),
    Binary(BinOp, Value, Value),
    /// The address of a function, to call with `CallIndirect`.
    FuncAddr(String),
    /// The address of the module's global cell with this number, from
    /// [`Module::globals`].
    GlobalAddr(u32),
    // Effects, which run in the order they were added to their block.
    Load(Value),
    /// Stores the second value at the address in the first.
    Store(Value, Value),
    Call(String, Vec<Value>),
    /// Calls the function whose address is in the first value.
    CallIndirect(Value, Vec<Value>),
    /// Calls a function outside the module, declared with
    /// [`Module::external`], the way the VM calls one (see there). It can do
    /// anything to memory.
    CallExtern(String, Vec<Value>),
    GetChar,
    GetInt,
    PutChar(Value),
    PutInt(Value),
    PutUInt(Value),
    Puts(String),
    /// Allocates this many cells on the heap, giving their address.
    HeapAlloc(Value),
    /// Reserves this many cells for the rest of the function call, giving
    /// their address.
    Alloca(u64),
    /// Allocates this many cells, all 0, that the garbage collector frees
    /// once nothing points into them any more. A module uses this or
    /// `HeapAlloc`, not both.
    GcAlloc(Value),
    /// Stops the program.
    Abort,
    /// Machine state, for runtime code such as the garbage collector.
    Intrinsic(Intrinsic, Vec<Value>),
}

/// Machine state that runtime code needs.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum Intrinsic {
    /// The stack pointer: the first cell past the stack.
    StackPointer,
    /// The heap pointer: the lowest cell the heap has handed out.
    HeapPointer,
    /// Sets the heap pointer to its operand, giving cells back to the stack.
    SetHeapPointer,
    /// The address of the first cell that can hold a function's values: the
    /// cells from here to the stack pointer are where every value that's
    /// live is kept.
    RootsStart,
}

impl Intrinsic {
    pub fn name(self) -> &'static str {
        match self {
            Intrinsic::StackPointer => "stack_pointer",
            Intrinsic::HeapPointer => "heap_pointer",
            Intrinsic::SetHeapPointer => "set_heap_pointer",
            Intrinsic::RootsStart => "roots_start",
        }
    }
}

impl Node {
    pub fn is_pure(&self) -> bool {
        matches!(
            self,
            Node::Const(_) | Node::Param(..) | Node::Unary(..) | Node::Binary(..) | Node::FuncAddr(_) | Node::GlobalAddr(_)
        )
    }

    pub fn has_result(&self) -> bool {
        !matches!(
            self,
            Node::Store(..)
                | Node::PutChar(_)
                | Node::PutInt(_)
                | Node::PutUInt(_)
                | Node::Puts(_)
                | Node::Abort
                | Node::Intrinsic(Intrinsic::SetHeapPointer, _)
        )
    }

    pub fn operands(&self) -> Vec<Value> {
        match self {
            Node::Const(_)
            | Node::Param(..)
            | Node::FuncAddr(_)
            | Node::GlobalAddr(_)
            | Node::GetChar
            | Node::GetInt
            | Node::Puts(_)
            | Node::Alloca(_)
            | Node::Abort => vec![],
            Node::Unary(_, a)
            | Node::Load(a)
            | Node::PutChar(a)
            | Node::PutInt(a)
            | Node::PutUInt(a)
            | Node::HeapAlloc(a)
            | Node::GcAlloc(a) => vec![*a],
            Node::Binary(_, a, b) | Node::Store(a, b) => vec![*a, *b],
            Node::Call(_, args) | Node::Intrinsic(_, args) | Node::CallExtern(_, args) => args.clone(),
            Node::CallIndirect(f, args) => std::iter::once(*f).chain(args.iter().copied()).collect(),
        }
    }

    fn map_operands(&mut self, mut f: impl FnMut(Value) -> Value) {
        match self {
            Node::Const(_)
            | Node::Param(..)
            | Node::FuncAddr(_)
            | Node::GlobalAddr(_)
            | Node::GetChar
            | Node::GetInt
            | Node::Puts(_)
            | Node::Alloca(_)
            | Node::Abort => {}
            Node::Unary(_, a)
            | Node::Load(a)
            | Node::PutChar(a)
            | Node::PutInt(a)
            | Node::PutUInt(a)
            | Node::HeapAlloc(a)
            | Node::GcAlloc(a) => *a = f(*a),
            Node::Binary(_, a, b) | Node::Store(a, b) => {
                *a = f(*a);
                *b = f(*b);
            }
            Node::Call(_, args) | Node::Intrinsic(_, args) | Node::CallExtern(_, args) => args.iter_mut().for_each(|a| *a = f(*a)),
            Node::CallIndirect(g, args) => {
                *g = f(*g);
                args.iter_mut().for_each(|a| *a = f(*a));
            }
        }
    }
}

/// A jump destination: a block and the arguments for its parameters.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Target {
    pub block: Block,
    pub args: Vec<Value>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Terminator {
    Jump(Target),
    /// Goes to the first target if the value is nonzero, else the second.
    Branch(Value, Target, Target),
    /// Returns from the function, with 0 if there's no value. Returning from
    /// `main` ends the program.
    Return(Option<Value>),
}

impl Terminator {
    pub fn targets(&self) -> Vec<&Target> {
        match self {
            Terminator::Jump(t) => vec![t],
            Terminator::Branch(_, t, e) => vec![t, e],
            Terminator::Return(_) => vec![],
        }
    }

    pub fn operands(&self) -> Vec<Value> {
        let mut ops = match self {
            Terminator::Branch(c, ..) | Terminator::Return(Some(c)) => vec![*c],
            _ => vec![],
        };
        for t in self.targets() {
            ops.extend(&t.args);
        }
        ops
    }

    fn map_operands(&mut self, mut f: impl FnMut(Value) -> Value) {
        match self {
            Terminator::Jump(t) => t.args.iter_mut().for_each(|a| *a = f(*a)),
            Terminator::Branch(c, t, e) => {
                *c = f(*c);
                t.args.iter_mut().for_each(|a| *a = f(*a));
                e.args.iter_mut().for_each(|a| *a = f(*a));
            }
            Terminator::Return(v) => {
                if let Some(v) = v {
                    *v = f(*v);
                }
            }
        }
    }

    fn map_targets(&mut self, mut f: impl FnMut(&Target) -> Target) {
        match self {
            Terminator::Jump(t) => *t = f(t),
            Terminator::Branch(_, t, e) => {
                *t = f(t);
                *e = f(e);
            }
            Terminator::Return(_) => {}
        }
    }
}

#[derive(Clone, Debug)]
struct ValueData {
    node: Node,
    /// The block the node belongs to, or none for constants, which can be
    /// used anywhere.
    block: Option<Block>,
}

#[derive(Clone, Debug, Default)]
struct BlockData {
    params: Vec<Value>,
    effects: Vec<Value>,
    term: Option<Terminator>,
}

/// A function, which is also its own builder: new nodes go into the current
/// block, set with [`Function::switch_to`].
#[derive(Clone, Debug)]
pub struct Function {
    name: String,
    values: Vec<ValueData>,
    blocks: Vec<BlockData>,
    /// Pure nodes by block, so that building one twice gives the same value.
    dedup: HashMap<(Option<Block>, Node), Value>,
    current: Block,
    /// The module's narrowest target width, for folding.
    min_width: u32,
}

macro_rules! binary_ops {
    ($($name:ident => $op:ident),* $(,)?) => {
        $(
            pub fn $name(&mut self, a: Value, b: Value) -> Value {
                self.binary(BinOp::$op, a, b)
            }
        )*
    };
}

macro_rules! unary_ops {
    ($($name:ident => $op:ident),* $(,)?) => {
        $(
            pub fn $name(&mut self, a: Value) -> Value {
                self.unary(UnOp::$op, a)
            }
        )*
    };
}

enum Simplified {
    Value(Value),
    Int(i64),
}

impl Function {
    fn new(name: &str, params: usize, min_width: u32) -> Self {
        let mut f = Function {
            name: name.to_string(),
            values: vec![],
            blocks: vec![],
            dedup: HashMap::new(),
            current: Block(0),
            min_width,
        };
        f.new_block(params);
        f
    }

    pub fn name(&self) -> &str {
        &self.name
    }

    pub fn entry(&self) -> Block {
        Block(0)
    }

    /// The function's parameter `i`: parameter `i` of its entry block.
    pub fn param(&self, i: usize) -> Value {
        self.blocks[0].params[i]
    }

    pub fn param_count(&self) -> usize {
        self.blocks[0].params.len()
    }

    pub fn new_block(&mut self, params: usize) -> Block {
        let b = Block(self.blocks.len() as u32);
        self.blocks.push(BlockData::default());
        for i in 0..params {
            let v = self.push(Node::Param(b, i), Some(b));
            self.blocks[b.index()].params.push(v);
        }
        b
    }

    /// Adds a parameter to block `b`. Jumps to it then need another argument.
    fn add_param(&mut self, b: Block) -> Value {
        let i = self.blocks[b.index()].params.len();
        let v = self.push(Node::Param(b, i), Some(b));
        self.blocks[b.index()].params.push(v);
        v
    }

    pub fn block_params(&self, b: Block) -> &[Value] {
        &self.blocks[b.index()].params
    }

    pub fn block_param(&self, b: Block, i: usize) -> Value {
        self.blocks[b.index()].params[i]
    }

    pub fn switch_to(&mut self, b: Block) {
        self.current = b;
    }

    pub fn current(&self) -> Block {
        self.current
    }

    pub fn node(&self, v: Value) -> &Node {
        &self.values[v.index()].node
    }

    /// The block a value belongs to, or none for constants.
    pub fn block_of(&self, v: Value) -> Option<Block> {
        self.values[v.index()].block
    }

    pub fn effects(&self, b: Block) -> &[Value] {
        &self.blocks[b.index()].effects
    }

    pub fn terminator(&self, b: Block) -> Option<&Terminator> {
        self.blocks[b.index()].term.as_ref()
    }

    pub fn const_value(&self, v: Value) -> Option<i64> {
        match self.values[v.index()].node {
            Node::Const(k) => Some(k),
            _ => None,
        }
    }

    /// The blocks reachable from the entry, in reverse postorder.
    pub fn reachable_blocks(&self) -> Vec<Block> {
        cfg::reverse_postorder(self)
    }

    fn push(&mut self, node: Node, block: Option<Block>) -> Value {
        let v = Value(self.values.len() as u32);
        self.values.push(ValueData { node, block });
        v
    }

    fn pure(&mut self, node: Node) -> Value {
        let block = if matches!(node, Node::Const(_)) { None } else { Some(self.current) };
        if let Some(&v) = self.dedup.get(&(block, node.clone())) {
            return v;
        }
        let v = self.push(node.clone(), block);
        self.dedup.insert((block, node), v);
        v
    }

    fn effect(&mut self, node: Node) -> Value {
        let b = self.current;
        assert!(self.blocks[b.index()].term.is_none(), "{b} already ends with a terminator");
        let v = self.push(node, Some(b));
        self.blocks[b.index()].effects.push(v);
        v
    }

    /// The functions whose addresses this function takes, in code it needs.
    fn addresses_taken(&self) -> Vec<String> {
        let blocks = cfg::reverse_postorder(self);
        let needed = sched::needed(self, &blocks);
        self.values
            .iter()
            .enumerate()
            .filter_map(|(i, data)| match &data.node {
                Node::FuncAddr(name) if needed[i] => Some(name.clone()),
                _ => None,
            })
            .collect()
    }

    /// The values pinned to each block.
    fn pinned(&self) -> Vec<Vec<Value>> {
        let mut pinned = vec![vec![]; self.blocks.len()];
        for (i, data) in self.values.iter().enumerate() {
            if let Some(b) = data.block {
                pinned[b.index()].push(Value(i as u32));
            }
        }
        pinned
    }

    pub fn int(&mut self, k: i64) -> Value {
        self.pure(Node::Const(k))
    }

    pub fn binary(&mut self, op: BinOp, a: Value, b: Value) -> Value {
        match self.simplify_binary(op, a, b) {
            Ok(v) => v,
            Err(node) => self.pure(node),
        }
    }

    pub fn unary(&mut self, op: UnOp, a: Value) -> Value {
        match self.simplify_unary(op, a) {
            Ok(v) => v,
            Err(node) => self.pure(node),
        }
    }

    /// What `a op b` simplifies to: an existing value, or the node to build,
    /// with its operands in a canonical order.
    fn simplify_binary(&mut self, op: BinOp, a: Value, b: Value) -> Result<Value, Node> {
        let (ca, cb) = (self.const_value(a), self.const_value(b));
        if let (Some(x), Some(y)) = (ca, cb) {
            if let Some(k) = fold::fold_binary(op, x, y, self.min_width) {
                return Ok(self.int(k));
            }
        }
        // constants go on the right, where the helpers that take a constant
        // want them, and otherwise the lower value goes first
        let (op, a, b, cb) = match op.swapped() {
            Some(swapped) if (ca.is_some() && cb.is_none()) || (ca.is_some() == cb.is_some() && a > b) => {
                (swapped, b, a, ca)
            }
            _ => (op, a, b, cb),
        };
        use BinOp::*;
        let simplified = match (op, cb) {
            (Add | Sub | Or | Xor | Shl | Shr | ShrU | Index, Some(0)) => Some(Simplified::Value(a)),
            (Mul | Div | DivU, Some(1)) | (And, Some(-1)) => Some(Simplified::Value(a)),
            (Mul | And, Some(0)) | (Rem | RemU, Some(1)) => Some(Simplified::Int(0)),
            (Or, Some(-1)) => Some(Simplified::Int(-1)),
            _ if a == b => match op {
                Sub | Xor | Ne | Lt | Gt | LtU | GtU => Some(Simplified::Int(0)),
                Eq | Le | Ge | LeU | GeU => Some(Simplified::Int(1)),
                And | Or | Min | Max => Some(Simplified::Value(a)),
                _ => None,
            },
            _ => None,
        };
        match simplified {
            Some(Simplified::Value(v)) => Ok(v),
            Some(Simplified::Int(k)) => Ok(self.int(k)),
            None => Err(Node::Binary(op, a, b)),
        }
    }

    fn simplify_unary(&mut self, op: UnOp, a: Value) -> Result<Value, Node> {
        if let Some(k) = self.const_value(a) {
            if let Some(k) = fold::fold_unary(op, k, self.min_width) {
                return Ok(self.int(k));
            }
        }
        match (op, self.node(a)) {
            (UnOp::Neg, Node::Unary(UnOp::Neg, x)) | (UnOp::Not, Node::Unary(UnOp::Not, x)) => Ok(*x),
            _ => Err(Node::Unary(op, a)),
        }
    }

    binary_ops! {
        add => Add, sub => Sub, mul => Mul, div => Div, rem => Rem, divu => DivU, remu => RemU,
        and => And, or => Or, xor => Xor, shl => Shl, shr => Shr, shru => ShrU,
        eq => Eq, ne => Ne, lt => Lt, le => Le, gt => Gt, ge => Ge,
        ltu => LtU, leu => LeU, gtu => GtU, geu => GeU, min => Min, max => Max,
        index => Index,
    }

    unary_ops! { neg => Neg, not => Not, lnot => LNot, abs => Abs }

    /// The cell at the address in `addr`.
    pub fn load(&mut self, addr: Value) -> Value {
        self.effect(Node::Load(addr))
    }

    pub fn store(&mut self, addr: Value, value: Value) {
        self.effect(Node::Store(addr, value));
    }

    pub fn call(&mut self, name: &str, args: &[Value]) -> Value {
        self.effect(Node::Call(name.to_string(), args.to_vec()))
    }

    /// The address of function `name`, which `call_indirect` can call.
    pub fn func_addr(&mut self, name: &str) -> Value {
        self.pure(Node::FuncAddr(name.to_string()))
    }

    /// Calls the function whose address `f` holds, from `func_addr`.
    pub fn call_indirect(&mut self, f: Value, args: &[Value]) -> Value {
        self.effect(Node::CallIndirect(f, args.to_vec()))
    }

    /// Calls the external function `name` (see [`Module::external`]).
    pub fn call_extern(&mut self, name: &str, args: &[Value]) -> Value {
        self.effect(Node::CallExtern(name.to_string(), args.to_vec()))
    }

    /// The next byte of input, or -1 at the end.
    pub fn get_char(&mut self) -> Value {
        self.effect(Node::GetChar)
    }

    /// Reads a decimal integer, as `asm::getint` does.
    pub fn get_int(&mut self) -> Value {
        self.effect(Node::GetInt)
    }

    pub fn put_char(&mut self, v: Value) {
        self.effect(Node::PutChar(v));
    }

    pub fn put_int(&mut self, v: Value) {
        self.effect(Node::PutInt(v));
    }

    pub fn put_uint(&mut self, v: Value) {
        self.effect(Node::PutUInt(v));
    }

    pub fn puts(&mut self, s: &str) {
        self.effect(Node::Puts(s.to_string()));
    }

    pub fn heap_alloc(&mut self, cells: Value) -> Value {
        self.effect(Node::HeapAlloc(cells))
    }

    pub fn alloca(&mut self, cells: u64) -> Value {
        self.effect(Node::Alloca(cells))
    }

    /// Allocates `cells` cells, all 0, that are freed once nothing points
    /// into them.
    pub fn gc_alloc(&mut self, cells: Value) -> Value {
        self.effect(Node::GcAlloc(cells))
    }

    /// Stops the program. The block still needs a terminator, which never
    /// runs.
    pub fn abort(&mut self) {
        self.effect(Node::Abort);
    }

    /// The address of the module's global cell `i`.
    pub fn global_addr(&mut self, i: u32) -> Value {
        self.pure(Node::GlobalAddr(i))
    }

    pub fn intrinsic(&mut self, which: Intrinsic, args: &[Value]) -> Value {
        self.effect(Node::Intrinsic(which, args.to_vec()))
    }

    fn terminate(&mut self, t: Terminator) {
        let b = self.current;
        assert!(self.blocks[b.index()].term.is_none(), "{b} already ends with a terminator");
        self.blocks[b.index()].term = Some(t);
    }

    pub fn jump(&mut self, to: Block, args: &[Value]) {
        self.terminate(Terminator::Jump(Target { block: to, args: args.to_vec() }));
    }

    pub fn branch(&mut self, cond: Value, then: Block, then_args: &[Value], els: Block, else_args: &[Value]) {
        self.terminate(Terminator::Branch(
            cond,
            Target { block: then, args: then_args.to_vec() },
            Target { block: els, args: else_args.to_vec() },
        ));
    }

    pub fn ret(&mut self, v: Value) {
        self.terminate(Terminator::Return(Some(v)));
    }

    pub fn ret_void(&mut self) {
        self.terminate(Terminator::Return(None));
    }

    /// Rebuilds the table of pure nodes after passes have changed them.
    fn rebuild_dedup(&mut self) {
        self.dedup.clear();
        for (i, data) in self.values.iter().enumerate() {
            if data.node.is_pure() {
                self.dedup.entry((data.block, data.node.clone())).or_insert(Value(i as u32));
            }
        }
    }
}

/// A program: `main`, and the functions it calls.
#[derive(Clone, Debug)]
pub struct Module {
    funcs: Vec<Function>,
    /// How many global cells there are.
    globals: u32,
    /// The external functions it calls.
    externs: Vec<String>,
    /// The narrowest cell width the program will run on.
    min_width: u32,
}

impl Default for Module {
    fn default() -> Self {
        Self::new()
    }
}

impl Module {
    /// A module for CPUs with cells of 16 bits and up.
    pub fn new() -> Self {
        Self::with_min_width(16)
    }

    /// A module for CPUs with cells of at least `bits` bits (16 to 64). The
    /// wider its narrowest target, the more the optimizer can prove: values
    /// that fit in `bits` bits mean the same thing on every target.
    pub fn with_min_width(bits: u32) -> Self {
        assert!((16..=64).contains(&bits), "cell widths are 16 to 64 bits");
        Module { funcs: vec![Function::new("main", 0, bits)], globals: 0, externs: vec![], min_width: bits }
    }

    pub fn min_width(&self) -> u32 {
        self.min_width
    }

    /// Reserves `cells` global cells, which start at 0, and gives the number
    /// of the first, for `Function::global_addr`.
    pub fn add_globals(&mut self, cells: u32) -> u32 {
        self.globals += cells;
        self.globals - cells
    }

    /// How many global cells there are.
    pub fn globals(&self) -> u32 {
        self.globals
    }

    /// Declares an external function, which `call_extern` calls: one the VM
    /// calls through a label the program doesn't define, which in the C
    /// backend is a C function
    ///
    /// ```c
    /// void name(int64_t **tape, int64_t **ptr, int64_t *acc);
    /// ```
    ///
    /// A call puts its arguments (at most 9) in cells next to each other,
    /// with the pointer at the first (`(*ptr)[0]`, `(*ptr)[1]`, ...), and its
    /// result is what the function leaves in `acc`; the function must
    /// leave the pointer where it was. `*tape` is the start of the tape
    /// (in the LLVM backend, which has no tape, of the module's global
    /// cells). The interpreters call a host function, which gets the same.
    pub fn external(&mut self, name: &str) {
        if !self.externs.iter().any(|n| n == name) {
            self.externs.push(name.to_string());
        }
    }

    /// The external functions.
    pub fn externals(&self) -> &[String] {
        &self.externs
    }

    /// The program's entry point, which takes no parameters.
    pub fn main(&mut self) -> &mut Function {
        &mut self.funcs[0]
    }

    /// Adds a function. Its name must be 1 to 13 letters, digits or `_`.
    pub fn function(&mut self, name: &str, params: usize) -> &mut Function {
        assert!(self.index_of(name).is_none(), "there's already a function called {name}");
        self.funcs.push(Function::new(name, params, self.min_width));
        self.funcs.last_mut().unwrap()
    }

    pub fn get(&self, name: &str) -> Option<&Function> {
        self.index_of(name).map(|i| &self.funcs[i])
    }

    pub fn get_mut(&mut self, name: &str) -> Option<&mut Function> {
        self.index_of(name).map(|i| &mut self.funcs[i])
    }

    pub fn functions(&self) -> &[Function] {
        &self.funcs
    }

    fn index_of(&self, name: &str) -> Option<usize> {
        self.funcs.iter().position(|f| f.name == name)
    }

    /// Whether each function's address is taken, from a block that can run,
    /// so it can be called indirectly.
    fn address_taken(&self) -> Vec<bool> {
        let mut taken = vec![false; self.funcs.len()];
        for f in &self.funcs {
            for name in f.addresses_taken() {
                if let Some(i) = self.index_of(&name) {
                    taken[i] = true;
                }
            }
        }
        taken
    }

    /// The functions each function can call, from blocks it can reach. An
    /// indirect call can call any function whose address is taken.
    fn callees(&self) -> Vec<Vec<usize>> {
        let taken: Vec<usize> = self.address_taken().iter().enumerate().filter(|(_, t)| **t).map(|(i, _)| i).collect();
        self.funcs
            .iter()
            .map(|f| {
                cfg::reverse_postorder(f)
                    .into_iter()
                    .flat_map(|b| &f.blocks[b.index()].effects)
                    .flat_map(|&e| match &f.values[e.index()].node {
                        Node::Call(name, _) => self.index_of(name).into_iter().collect(),
                        Node::CallIndirect(..) => taken.clone(),
                        _ => vec![],
                    })
                    .collect()
            })
            .collect()
    }

    /// Whether each function can call itself, directly or through others.
    fn recursive(&self) -> Vec<bool> {
        let calls = self.callees();
        (0..self.funcs.len())
            .map(|start| {
                let mut seen = vec![false; calls.len()];
                let mut stack = calls[start].clone();
                while let Some(f) = stack.pop() {
                    if f == start {
                        return true;
                    }
                    if !seen[f] {
                        seen[f] = true;
                        stack.extend(&calls[f]);
                    }
                }
                false
            })
            .collect()
    }
}

impl fmt::Display for Module {
    fn fmt(&self, out: &mut fmt::Formatter) -> fmt::Result {
        for (i, f) in self.funcs.iter().enumerate() {
            if i > 0 {
                writeln!(out)?;
            }
            write!(out, "{f}")?;
        }
        Ok(())
    }
}

/// Prints the reachable blocks, with each block's nodes in the order they'll
/// be computed. Nodes that nothing needs aren't shown, since they never are.
impl fmt::Display for Function {
    fn fmt(&self, out: &mut fmt::Formatter) -> fmt::Result {
        let operand = |v: Value| match self.const_value(v) {
            Some(k) => k.to_string(),
            None => v.to_string(),
        };
        let list = |vs: &[Value]| vs.iter().map(|&v| operand(v)).collect::<Vec<_>>().join(", ");
        let target = |t: &Target| {
            if t.args.is_empty() { t.block.to_string() } else { format!("{}({})", t.block, list(&t.args)) }
        };

        let params: Vec<String> = self.blocks[0].params.iter().map(|v| v.to_string()).collect();
        writeln!(out, "fn {}({}) {{", self.name, params.join(", "))?;
        let blocks = cfg::reverse_postorder(self);
        let needed = sched::needed(self, &blocks);
        let outside = sched::used_outside(self, &blocks, &needed);
        let pinned = self.pinned();
        for &b in &blocks {
            let params = &self.blocks[b.index()].params;
            if params.is_empty() {
                writeln!(out, "{b}:")?;
            } else {
                writeln!(out, "{b}({}):", list(params))?;
            }
            for v in sched::schedule(self, b, &needed, &outside, &pinned[b.index()]) {
                let node = &self.values[v.index()].node;
                let text = match node {
                    Node::Const(_) | Node::Param(..) => unreachable!("never scheduled"),
                    Node::Unary(op, a) => format!("{} {}", op.name(), operand(*a)),
                    Node::Binary(op, a, b) => format!("{} {}, {}", op.name(), operand(*a), operand(*b)),
                    Node::Load(a) => format!("load {}", operand(*a)),
                    Node::Store(a, x) => format!("store {}, {}", operand(*a), operand(*x)),
                    Node::Call(name, args) => format!("call {name}({})", list(args)),
                    Node::FuncAddr(name) => format!("addr {name}"),
                    Node::CallIndirect(g, args) => format!("call *{}({})", operand(*g), list(args)),
                    Node::CallExtern(name, args) => format!("call extern {name}({})", list(args)),
                    Node::GetChar => "get_char".to_string(),
                    Node::GetInt => "get_int".to_string(),
                    Node::PutChar(a) => format!("put_char {}", operand(*a)),
                    Node::PutInt(a) => format!("put_int {}", operand(*a)),
                    Node::PutUInt(a) => format!("put_uint {}", operand(*a)),
                    Node::Puts(s) => format!("puts {s:?}"),
                    Node::HeapAlloc(a) => format!("heap_alloc {}", operand(*a)),
                    Node::Alloca(cells) => format!("alloca {cells}"),
                    Node::GlobalAddr(i) => format!("global {i}"),
                    Node::GcAlloc(a) => format!("gc_alloc {}", operand(*a)),
                    Node::Abort => "abort".to_string(),
                    Node::Intrinsic(which, args) => format!("{}({})", which.name(), list(args)),
                };
                if node.has_result() {
                    writeln!(out, "    {v} = {text}")?;
                } else {
                    writeln!(out, "    {text}")?;
                }
            }
            match &self.blocks[b.index()].term {
                Some(Terminator::Jump(t)) => writeln!(out, "    jump {}", target(t))?,
                Some(Terminator::Branch(c, t, e)) => {
                    writeln!(out, "    br {}, {}, {}", operand(*c), target(t), target(e))?
                }
                Some(Terminator::Return(Some(v))) => writeln!(out, "    ret {}", operand(*v))?,
                Some(Terminator::Return(None)) => writeln!(out, "    ret")?,
                None => writeln!(out, "    (no terminator)")?,
            }
        }
        writeln!(out, "}}")
    }
}
