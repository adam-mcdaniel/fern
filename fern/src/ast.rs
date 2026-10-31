//! The program as written: what the parser makes. Names here are still
//! the paths in the source (`list::map`, `Some`); `resolve` works out what
//! each one means.

use crate::lexer::Pos;

/// `a::b::c`
#[derive(Clone, Debug)]
pub struct Path {
    pub segments: Vec<String>,
    pub pos: Pos,
}

impl Path {
    pub fn last(&self) -> &str {
        self.segments.last().unwrap()
    }
}

impl std::fmt::Display for Path {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        write!(f, "{}", self.segments.join("::"))
    }
}

pub enum Item {
    /// `mod name;` (the file name.fern next to this one) or `mod name { .. }`
    Mod { name: String, public: bool, body: Option<Vec<Item>>, pos: Pos },
    /// `use a::b::{c, d as e, f::*};`, as one entry per name it brings in
    Use { public: bool, uses: Vec<Use> },
    Fn(FnDef),
    Struct(StructDef),
    Enum(EnumDef),
    Trait(TraitDef),
    Impl(ImplDef),
    Effect(EffectDef),
    /// `extern fn name(x: Int) -> Int;`: a function written in C (with
    /// `bf.h`), called by that name
    Extern(FnDef),
    /// `impl<T> Type<T> { fn name(self, ..) { .. } }`: methods of a type
    Methods(MethodsDef),
}

#[derive(Clone, Debug)]
pub struct Use {
    pub path: Path,
    /// `as name`, or `*` (everything public in the module)
    pub alias: Option<String>,
    pub glob: bool,
}

/// A generic parameter: `T: Show + Eq`, or an effect variable `'e`.
#[derive(Clone, Debug)]
pub struct Generic {
    pub name: String,
    pub bounds: Vec<Path>,
    pub effect: bool,
}

#[derive(Clone, Debug)]
pub struct Param {
    pub name: String,
    pub ty: Option<TypeExpr>,
    pub mutable: bool,
}

#[derive(Clone, Debug)]
pub struct FnDef {
    pub name: String,
    pub public: bool,
    pub generics: Vec<Generic>,
    pub params: Vec<Param>,
    /// Whether the first parameter is `self` (in traits and impls).
    pub has_self: bool,
    pub ret: Option<TypeExpr>,
    /// `with E1, E2, 'e`: the effects it may have, if they're written.
    pub effects: Option<EffectExpr>,
    pub body: Option<Expr>,
    pub pos: Pos,
}

pub struct StructDef {
    pub name: String,
    pub public: bool,
    pub generics: Vec<String>,
    pub fields: Vec<(String, TypeExpr)>,
    pub derives: Vec<String>,
    pub pos: Pos,
}

pub struct EnumDef {
    pub name: String,
    pub public: bool,
    pub generics: Vec<String>,
    pub variants: Vec<(String, Vec<TypeExpr>)>,
    pub derives: Vec<String>,
    pub pos: Pos,
}

pub struct TraitDef {
    pub name: String,
    pub public: bool,
    /// `trait Ord: Eq`
    pub supers: Vec<Path>,
    /// Its associated types, each with the traits it has to have: `type
    /// Item: Show;`
    pub assoc: Vec<(String, Vec<Path>)>,
    pub methods: Vec<FnDef>,
    pub pos: Pos,
}

pub struct ImplDef {
    pub generics: Vec<Generic>,
    pub trait_: Path,
    pub ty: TypeExpr,
    /// What it says the trait's associated types are: `type Item = Int;`
    pub assoc: Vec<(String, TypeExpr, Pos)>,
    pub methods: Vec<FnDef>,
    pub pos: Pos,
}

/// A type's methods: functions called as `x.name(..)` on a value of the
/// type (those with `self` first), or `Type::name(..)`.
pub struct MethodsDef {
    pub generics: Vec<Generic>,
    pub ty: TypeExpr,
    pub methods: Vec<FnDef>,
    pub pos: Pos,
}

pub struct EffectDef {
    pub name: String,
    pub public: bool,
    pub generics: Vec<String>,
    pub ops: Vec<FnDef>,
    pub pos: Pos,
}

#[derive(Clone, Debug)]
pub enum TypeExpr {
    /// `Int`, `List<T>`, `T`
    Named(Path, Vec<TypeExpr>),
    /// `(A, B)`, and `()`
    Tuple(Vec<TypeExpr>),
    /// `fn(A, B) -> C with E`
    Fn(Vec<TypeExpr>, Box<TypeExpr>, Option<EffectExpr>),
    /// `{ x: Int, y: Int }`, or `{ x: Int, ..r }` (any record with an x)
    Record(Vec<(String, TypeExpr)>, Option<String>),
    SelfType,
    /// `Self::Item`: an associated type of the trait being defined or
    /// implemented (`T::Item`, for a type parameter `T`, is a `Named` path).
    SelfAssoc(String),
    /// `_`: worked out
    Infer,
}

/// `with Yield<Int>, Io, 'e`
#[derive(Clone, Debug)]
pub struct EffectExpr {
    pub effects: Vec<(Path, Vec<TypeExpr>)>,
    pub tail: Option<String>,
}

#[derive(Clone, Debug)]
pub struct Expr {
    pub kind: ExprKind,
    pub pos: Pos,
}

#[derive(Clone, Copy, Debug, PartialEq)]
pub enum BinOp {
    Add,
    Sub,
    Mul,
    Div,
    Rem,
    Eq,
    Ne,
    Lt,
    Le,
    Gt,
    Ge,
    And,
    Or,
    /// `++`: strings
    Concat,
    BitAnd,
    BitOr,
    BitXor,
    /// `<<`, and `>>` (which copies the sign bit)
    Shl,
    Shr,
}

#[derive(Clone, Copy, Debug, PartialEq)]
pub enum UnOp {
    Neg,
    Not,
}

#[derive(Clone, Debug)]
pub enum ExprKind {
    Int(i64),
    Str(String),
    Bool(bool),
    Unit,
    /// A variable, function, constructor or effect operation.
    Path(Path),
    Call(Box<Expr>, Vec<Expr>),
    /// `x.method(args)`: a trait's method
    Method(Box<Expr>, String, Vec<Expr>),
    /// `x.field`: a struct's or a record's
    Field(Box<Expr>, String),
    Binary(BinOp, Box<Expr>, Box<Expr>),
    Unary(UnOp, Box<Expr>),
    /// `{ statements; value }`
    Block(Vec<Stmt>, Option<Box<Expr>>),
    If(Box<Expr>, Box<Expr>, Option<Box<Expr>>),
    Match(Box<Expr>, Vec<(Pattern, Expr)>),
    While(Box<Expr>, Box<Expr>),
    Loop(Box<Expr>),
    Break,
    Continue,
    Return(Option<Box<Expr>>),
    /// `|x, y| body`
    Lambda(Vec<Param>, Box<Expr>),
    Tuple(Vec<Expr>),
    /// `[a, b, c]`: a `List`
    List(Vec<Expr>),
    /// `{ x: 1, y: 2 }`, or `{ ..r, x: 1 }` (r with x added, or changed)
    Record(Vec<(String, Expr)>, Option<Box<Expr>>),
    /// `Point { x: 1, y: 2 }`
    StructLit(Path, Vec<(String, Expr)>),
    /// `x = e` (x a `let mut`)
    Assign(String, Box<Expr>),
    /// `r.f = e`: a struct's field set
    SetField(Box<Expr>, String, Box<Expr>),
    /// `handle e { return(v) => .., op(a) => .. }` (`resume` in the op arms)
    Handle(Box<Expr>, Vec<HandlerArm>),
}

#[derive(Clone, Debug)]
pub struct HandlerArm {
    /// The operation (`return` for what the handled code gives back).
    pub op: Path,
    pub params: Vec<String>,
    pub body: Expr,
}

#[derive(Clone, Debug)]
pub enum Stmt {
    Let { pat: Pattern, mutable: bool, ty: Option<TypeExpr>, value: Expr },
    Expr(Expr),
}

#[derive(Clone, Debug)]
pub struct Pattern {
    pub kind: PatKind,
    pub pos: Pos,
}

#[derive(Clone, Debug)]
pub enum PatKind {
    Wild,
    Bind(String),
    Int(i64),
    Bool(bool),
    Str(String),
    Unit,
    Tuple(Vec<Pattern>),
    /// `Some(x)`, `None`, `list::Cons(h, t)`
    Ctor(Path, Vec<Pattern>),
    /// `[a, b]`, `[a, ..rest]`
    List(Vec<Pattern>, Option<Box<Pattern>>),
}
