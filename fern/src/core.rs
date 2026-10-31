//! The program after type inference: every name resolved, traits turned
//! into dictionaries passed as arguments, sugar (lists, `&&`, `let mut`)
//! gone. What `cps` compiles. Types are gone too: everything is one cell.
//!
//! - A struct, a tuple and a trait's dictionary are a block of cells
//!   (`Tuple`, read with `Proj`, a struct's field set with `SetProj`, and
//!   read with `Field` if anything sets it); except a struct of one field
//!   that's never set, which is just that field.
//! - An enum's value is a block holding its variant's number, then its
//!   fields (`Con`).
//! - A record is its fields with their labels, read by label.
//! - `true` is 1, `false` 0, `()` 0.
//!
//! What its types said that compiling needs is kept: what each call, and
//! each lambda, may do (`Eff`). A call that can't perform an operation needs
//! no continuation, so it can be compiled as an ordinary call (see
//! `direct.rs`).

use crate::types::Type;

/// A local variable, made unique by the type checker (`x_12`).
pub type Name = String;

/// What calling something may do, from its type's effects.
#[derive(Clone, Debug, PartialEq)]
pub enum Eff {
    /// Nothing: no effects.
    Pure,
    /// Only what the effect parameters of the function it's in may do (`'e`
    /// in `fold`): nothing, in the version of that function made for when
    /// they're nothing.
    Poly,
    /// Operations: it may need the rest of the computation.
    Impure,
    /// While type checking: the effects' row, sorted out into one of the
    /// others once its function is checked.
    Row(Type),
}

#[derive(Clone, Debug)]
pub enum Core {
    Int(i64),
    Str(String),
    Local(Name),
    /// A call to a top-level function, and what it may do.
    CallGlobal(String, Vec<Core>, Eff),
    /// A function value (a closure): its number (each lambda's is its own),
    /// parameters, body, and what calling it may do; and calling one.
    Lam(usize, Vec<Name>, Box<Core>, Eff),
    App(Box<Core>, Vec<Core>, Eff),
    Let(Name, Box<Core>, Box<Core>),
    If(Box<Core>, Box<Core>, Box<Core>),
    Match(Box<Core>, Vec<(Pat, Core)>),
    /// Variant `tag` of an enum, with its fields.
    Con(i64, Vec<Core>),
    Tuple(Vec<Core>),
    /// Cell `i` of a block, which never changes once the block's made.
    Proj(Box<Core>, usize),
    /// Cell `i` of a block that can change: a struct's field that something
    /// sets.
    Field(Box<Core>, usize),
    /// Sets cell `i` of a block (a struct's field), giving `()`.
    SetProj(Box<Core>, usize, Box<Core>),
    Record(Vec<(String, Core)>),
    RecGet(Box<Core>, String),
    /// A record with fields added in front (hiding any of the same names).
    RecExtend(Box<Core>, Vec<(String, Core)>),
    Prim(Prim, Vec<Core>),
    Seq(Box<Core>, Box<Core>),
    While(Box<Core>, Box<Core>),
    Loop(Box<Core>),
    Break,
    Continue,
    Return(Box<Core>),
    /// A `let mut` variable is a cell on the heap.
    NewRef(Box<Core>),
    GetRef(Box<Core>),
    SetRef(Box<Core>, Box<Core>),
    /// `handle body { .. }` for effect `eff` (by number): what to do with
    /// what the body gives back, and with each operation (its parameters, then
    /// `resume`).
    Handle { eff: i64, body: Box<Core>, ret: (Name, Box<Core>), ops: Vec<(Vec<Name>, Name, Core)> },
    /// Performing operation `op` of effect `eff`.
    Perform { eff: i64, op: usize, args: Vec<Core> },
    /// Stops the program with a message (a `match` nothing matched).
    Panic(String),
    /// What's at this place in the source (a call, or a `match`): where a
    /// runtime error in it says it is.
    Located(crate::lexer::Pos, Box<Core>),

    // Placeholders, while type checking: what's filled in once the types
    // they depend on are known (none are left after it).
    /// The dictionary for the trait requirement with this number.
    DictHole(usize),
    /// Method `method` of `trait_`, with that requirement's dictionary (and
    /// what calling it may do).
    MethodCall(usize, String, usize, Vec<Core>, Eff),
    /// `==` and friends, with the `Eq`/`Ord` requirement's dictionary: a
    /// machine comparison for `Int`, `Bool` and `String`, else a method call.
    Compare(Cmp, usize, Box<Core>, Box<Core>),
    /// `+ - * /` or negation, with the `Num` requirement's dictionary: the
    /// machine's for `Int`, else a method call.
    Arith(Prim, usize, Vec<Core>),
    /// In a call to a function of the same recursive group: this function's
    /// own dictionary parameters (they all have the same ones).
    DictArgs,
    /// A method call or field whose receiver's type wasn't known where it
    /// was written: what it is, once that's worked out (by number).
    Pending(usize),
}

impl Core {
    /// The expressions directly inside this one.
    pub fn children(&self) -> Vec<&Core> {
        match self {
            Core::Int(_) | Core::Str(_) | Core::Local(_) | Core::Break | Core::Continue | Core::Panic(_) | Core::DictHole(_) | Core::DictArgs | Core::Pending(_) => vec![],
            Core::CallGlobal(_, args, _) | Core::Con(_, args) | Core::Tuple(args) | Core::Prim(_, args) | Core::MethodCall(_, _, _, args, _) | Core::Arith(_, _, args) => args.iter().collect(),
            Core::Perform { args, .. } => args.iter().collect(),
            Core::Lam(_, _, b, _) | Core::Proj(b, _) | Core::Field(b, _) | Core::RecGet(b, _) | Core::Loop(b) | Core::Return(b) | Core::NewRef(b) | Core::GetRef(b) | Core::Located(_, b) => vec![b],
            Core::App(f, args, _) => std::iter::once(&**f).chain(args).collect(),
            Core::Let(_, a, b) | Core::Seq(a, b) | Core::While(a, b) | Core::SetRef(a, b) | Core::Compare(_, _, a, b) => vec![a, b],
            Core::If(c, a, b) => vec![c, a, b],
            Core::SetProj(r, _, v) => vec![r, v],
            Core::Match(s, arms) => std::iter::once(&**s).chain(arms.iter().map(|(_, b)| b)).collect(),
            Core::Record(fs) => fs.iter().map(|(_, v)| v).collect(),
            Core::RecExtend(r, fs) => std::iter::once(&**r).chain(fs.iter().map(|(_, v)| v)).collect(),
            Core::Handle { body, ret, ops, .. } => std::iter::once(&**body).chain(std::iter::once(&*ret.1)).chain(ops.iter().map(|(_, _, b)| b)).collect(),
        }
    }

    /// The expressions directly inside this one, to change.
    pub fn children_mut(&mut self) -> Vec<&mut Core> {
        match self {
            Core::Int(_) | Core::Str(_) | Core::Local(_) | Core::Break | Core::Continue | Core::Panic(_) | Core::DictHole(_) | Core::DictArgs | Core::Pending(_) => vec![],
            Core::CallGlobal(_, args, _) | Core::Con(_, args) | Core::Tuple(args) | Core::Prim(_, args) | Core::MethodCall(_, _, _, args, _) | Core::Arith(_, _, args) => args.iter_mut().collect(),
            Core::Perform { args, .. } => args.iter_mut().collect(),
            Core::Lam(_, _, b, _) | Core::Proj(b, _) | Core::Field(b, _) | Core::RecGet(b, _) | Core::Loop(b) | Core::Return(b) | Core::NewRef(b) | Core::GetRef(b) | Core::Located(_, b) => vec![&mut **b],
            Core::App(f, args, _) => std::iter::once(&mut **f).chain(args.iter_mut()).collect(),
            Core::Let(_, a, b) | Core::Seq(a, b) | Core::While(a, b) | Core::SetRef(a, b) | Core::Compare(_, _, a, b) | Core::SetProj(a, _, b) => vec![&mut **a, &mut **b],
            Core::If(c, a, b) => vec![&mut **c, &mut **a, &mut **b],
            Core::Match(s, arms) => std::iter::once(&mut **s).chain(arms.iter_mut().map(|(_, b)| b)).collect(),
            Core::Record(fs) => fs.iter_mut().map(|(_, v)| v).collect(),
            Core::RecExtend(r, fs) => std::iter::once(&mut **r).chain(fs.iter_mut().map(|(_, v)| v)).collect(),
            Core::Handle { body, ret, ops, .. } => std::iter::once(&mut **body).chain(std::iter::once(&mut *ret.1)).chain(ops.iter_mut().map(|(_, _, b)| b)).collect(),
        }
    }
}

#[derive(Clone, Copy, Debug, PartialEq)]
pub enum Cmp {
    Eq,
    Ne,
    Lt,
    Le,
    Gt,
    Ge,
}

#[derive(Clone, Debug)]
pub enum Pat {
    Wild,
    Bind(Name),
    Int(i64),
    Str(String),
    /// Variant `tag` of enum `enum_` (by full name, for exhaustiveness).
    Con(String, i64, Vec<Pat>),
    Tuple(Vec<Pat>),
}

/// Operations built in.
#[derive(Clone, Copy, Debug, PartialEq)]
pub enum Prim {
    Add,
    Sub,
    Mul,
    Div,
    Rem,
    BitAnd,
    BitOr,
    BitXor,
    Shl,
    Shr,
    Neg,
    Not,
    IntEq,
    IntNe,
    IntLt,
    IntLe,
    IntGt,
    IntGe,
    StrEq,
    StrLt,
    Concat,
    Print,
    ReadInt,
    IntToString,
    StrLength,
    CharAt,
    CharToString,
    /// An array: a block of its length, then its elements (`array(n, x)`
    /// makes one of `n` `x`s).
    ArrayNew,
    /// An array of numbers (`Int`s or `Bool`s), which never hold a pointer:
    /// the collector needn't look in it.
    ArrayNewData,
    ArrayGet,
    ArraySet,
    ArrayLength,
    /// A call to the program's `n`th external function (see `Program`).
    Extern(usize),
}

pub struct Func {
    pub name: String,
    pub params: Vec<Name>,
    pub body: Core,
    /// What calling it may do: `Poly` for one with effect parameters.
    pub eff: Eff,
}

pub struct Program {
    pub funcs: Vec<Func>,
    /// The function that's the program (`main`'s full name).
    pub main: String,
    /// Whether it reads input (`read_int`).
    pub reads_input: bool,
    /// The `extern fn`s it calls: each one's name and number of parameters.
    pub externs: Vec<(String, usize)>,
    /// What's worth saying about it that isn't an error (a variable that's
    /// never used, ...): where, and what.
    pub warnings: Vec<(crate::lexer::Pos, String)>,
    /// The files, by number (`Pos::file`).
    pub files: Vec<String>,
}
