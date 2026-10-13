//! The abstract syntax: DOT's types and terms, plus integers, booleans,
//! conditionals and a few built-ins.
//!
//! Variables are resolved to unique ids by the parser, so substitution never
//! captures anything, and the names they came from are kept for messages.

use std::collections::HashSet;

/// A variable, unique in the whole program.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct Var(pub u32);

/// A path: a variable, or a field selected from a path. Paths are what types
/// can depend on.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub enum Path {
    Var(Var),
    Sel(Box<Path>, String),
}

impl Path {
    pub fn root(&self) -> Var {
        match self {
            Path::Var(x) => *x,
            Path::Sel(p, _) => p.root(),
        }
    }

    /// This path with `x` replaced by `with`.
    pub fn subst(&self, x: Var, with: &Path) -> Path {
        match self {
            Path::Var(y) if *y == x => with.clone(),
            Path::Var(_) => self.clone(),
            Path::Sel(p, a) => Path::Sel(Box::new(p.subst(x, with)), a.clone()),
        }
    }

    pub fn sel(&self, a: &str) -> Path {
        Path::Sel(Box::new(self.clone()), a.to_string())
    }
}

/// Which way a type parameter varies: which bound applying the type to an
/// argument gives the parameter's member.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Variance {
    /// `+A`: `F[X]` is `F & { type A <: X }`.
    Co,
    /// `-A`: `F[X]` is `F & { type A >: X }`.
    Contra,
    /// `A`: `F[X]` is `F & { type A = X }`.
    In,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Type {
    Top,
    Bot,
    Int,
    Bool,
    Unit,
    /// Text: immutable, and compared by what it says.
    Str,
    /// `{ val a: T }`
    Field(String, Box<Type>),
    /// `{ var a: T }`: a field that can be assigned, so its type is
    /// invariant, and paths can't go through it.
    VarField(String, Box<Type>),
    /// `{ type A >: L <: U }`
    Member(String, Box<Type>, Box<Type>),
    /// `p.A`, the type member `A` of the value at `p`.
    Select(Path, String),
    /// `S & T`
    And(Box<Type>, Box<Type>),
    /// `(x: S) => T`, where `T` can mention `x`.
    Fun(Var, Box<Type>, Box<Type>),
    /// `{ z => T }`, DOT's `μ(z: T)`: a type that can mention the value it
    /// describes, as `z`.
    Rec(Var, Box<Type>),
    /// The parameters of a type that takes them (which are its type members
    /// of these names), noted in it so `F[X]` can be worked out wherever `F`
    /// is. As a type, it's `Top`.
    Params(Vec<(String, Variance)>),
    /// `F[X, Y]`, where the parser couldn't see `F`'s parameters: the checker
    /// finds them in `F`'s bounds.
    Applied(Box<Type>, Vec<Type>),
}

impl Type {
    pub fn and(types: Vec<Type>) -> Type {
        types.into_iter().reduce(|a, b| Type::And(Box::new(a), Box::new(b))).unwrap_or(Type::Top)
    }

    /// This type with `x` replaced by the path `with`.
    pub fn subst(&self, x: Var, with: &Path) -> Type {
        let s = |t: &Type| Box::new(t.subst(x, with));
        match self {
            Type::Field(a, t) => Type::Field(a.clone(), s(t)),
            Type::VarField(a, t) => Type::VarField(a.clone(), s(t)),
            Type::Member(a, l, u) => Type::Member(a.clone(), s(l), s(u)),
            Type::Select(p, a) => Type::Select(p.subst(x, with), a.clone()),
            Type::And(a, b) => Type::And(s(a), s(b)),
            Type::Fun(y, a, b) => Type::Fun(*y, s(a), s(b)),
            Type::Rec(y, t) => Type::Rec(*y, s(t)),
            Type::Applied(f, args) => Type::Applied(s(f), args.iter().map(|a| a.subst(x, with)).collect()),
            t => t.clone(),
        }
    }

    /// The variables this type mentions.
    pub fn free(&self, out: &mut HashSet<Var>) {
        match self {
            Type::Field(_, t) | Type::VarField(_, t) | Type::Rec(_, t) => t.free(out),
            Type::Member(_, l, u) | Type::And(l, u) | Type::Fun(_, l, u) => {
                l.free(out);
                u.free(out);
            }
            Type::Select(p, _) => {
                out.insert(p.root());
            }
            Type::Applied(f, args) => {
                f.free(out);
                args.iter().for_each(|a| a.free(out));
            }
            _ => {}
        }
    }

    pub fn mentions(&self, x: Var) -> bool {
        let mut free = HashSet::new();
        self.free(&mut free);
        free.contains(&x)
    }
}

#[derive(Clone, Debug)]
pub struct Term {
    pub kind: TermKind,
    /// Where it starts in the source, as a byte offset.
    pub pos: usize,
}

#[derive(Clone, Debug)]
pub enum TermKind {
    Var(Var),
    Int(i64),
    Bool(bool),
    Unit,
    Str(String),
    /// `(x: T) => body`, or `x => body` where the type expected says what
    /// `x` is.
    Lam(Var, Option<Type>, Box<Term>),
    App(Box<Term>, Box<Term>),
    /// `t.a`
    Sel(Box<Term>, String),
    /// `new { z: T => defs }`, with the self type optional.
    New(Var, Option<Type>, Vec<Def>),
    /// `let x: T = t; body`
    Let(Var, Option<Type>, Box<Term>, Box<Term>),
    If(Box<Term>, Box<Term>, Box<Term>),
    Prim(Prim, Vec<Term>),
    /// `(t: T)`
    Ascribe(Box<Term>, Type),
    /// A type as an argument: the object `new { type T = X }`, which a
    /// generic function takes for its type parameter. Only its type matters,
    /// so at run time it's nothing.
    TypeArg(Type),
    /// `var x: T = t; body`: a variable that can be assigned. It isn't a
    /// path, since what it holds can change.
    LetVar(Var, Option<Type>, Box<Term>, Box<Term>),
    /// Reading a `var`.
    Get(Var),
    /// `x = t`, for a `var` x.
    Set(Var, Box<Term>),
    /// `t.a = u`, for a `var` field `a`.
    Assign(Box<Term>, String, Box<Term>),
    /// `while (c) body`
    While(Box<Term>, Box<Term>),
    /// The body of an `extern def` or a `builtin def`: a call to the
    /// function with this name, passing these parameters.
    Foreign(String, Vec<Var>, ForeignKind),
}

/// What a function declared without a body is.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum ForeignKind {
    /// `extern def`: one outside the program, which the VM calls through a
    /// label the program doesn't define (in the C backend, a C function
    /// `void name(int64_t **tape, int64_t **ptr, int64_t *acc)`).
    Extern,
    /// `builtin def`: one of the compiler's own (see `codegen::BUILTINS`).
    Builtin,
}

#[derive(Clone, Debug)]
pub struct Def {
    pub name: String,
    pub kind: DefKind,
    pub pos: usize,
}

#[derive(Clone, Debug)]
pub enum DefKind {
    /// `val a: T = t`, and `def`s, which become values that are functions.
    Val(Option<Type>, Term),
    /// `var a: T = t`
    Var(Option<Type>, Term),
    /// `type A = T`
    Type(Type),
}

#[derive(Clone, Debug, PartialEq)]
pub enum Prim {
    Add,
    Sub,
    Mul,
    Div,
    Rem,
    Neg,
    Eq,
    Ne,
    Lt,
    Le,
    Gt,
    Ge,
    And,
    Or,
    Not,
    /// Prints an integer or a boolean.
    Print,
    PrintLn,
    /// Prints the character with this code.
    PrintChar,
    /// Prints a string literal.
    Puts(String),
    /// Reads an integer.
    Read,
    /// Reads a character's code, or -1 at the end of the input.
    ReadChar,
    /// Reads a line, without its newline.
    ReadLine,
    /// Prints "error: " and the message, and stops the program.
    Error,
}

/// The names variables came from, for messages.
#[derive(Clone, Debug, Default)]
pub struct Names {
    names: Vec<String>,
    /// The variables that are type parameters: objects whose type member
    /// `T` is written as the variable's name.
    type_params: HashSet<Var>,
    /// The variables of objects made of a block's definitions, whose members
    /// are written without them.
    groups: HashSet<Var>,
}

impl Names {
    pub fn fresh(&mut self, name: &str) -> Var {
        self.names.push(name.to_string());
        Var(self.names.len() as u32 - 1)
    }

    /// A type parameter's variable.
    pub fn type_param(&mut self, name: &str) -> Var {
        let x = self.fresh(name);
        self.type_params.insert(x);
        x
    }

    pub fn is_type_param(&self, x: Var) -> bool {
        self.type_params.contains(&x)
    }

    pub fn is_group(&self, x: Var) -> bool {
        self.groups.contains(&x)
    }

    /// The variable of a block's definitions.
    pub fn group(&mut self) -> Var {
        let x = self.fresh("defs");
        self.groups.insert(x);
        x
    }

    pub fn name(&self, x: Var) -> &str {
        &self.names[x.0 as usize]
    }

    pub fn path(&self, p: &Path) -> String {
        match p {
            Path::Sel(q, a) if matches!(**q, Path::Var(x) if self.groups.contains(&x)) => a.clone(),
            Path::Var(x) => self.name(*x).to_string(),
            Path::Sel(p, a) => format!("{}.{a}", self.path(p)),
        }
    }

    /// A type, written the way the source writes types.
    pub fn show(&self, t: &Type) -> String {
        self.show_in(t, &mut vec![])
    }

    /// A type inside records whose self variables are `hidden`: they had no
    /// name in the source, so their members are written without one.
    fn show_in(&self, t: &Type, hidden: &mut Vec<Var>) -> String {
        // the members of an intersection, for printing them as one record
        // (parameters' notes aren't printed: they're `Top`)
        fn members<'t>(t: &'t Type, out: &mut Vec<&'t Type>) {
            match t {
                Type::And(a, b) => {
                    members(a, out);
                    members(b, out);
                }
                Type::Params(_) => {}
                t => out.push(t),
            }
        }
        let decl = |t: &Type, hidden: &mut Vec<Var>| match t {
            Type::Field(a, t) => format!("val {a}: {}", self.show_in(t, hidden)),
            Type::VarField(a, t) => format!("var {a}: {}", self.show_in(t, hidden)),
            Type::Member(a, l, u) if l == u => format!("type {a} = {}", self.show_in(l, hidden)),
            Type::Member(a, l, u) => {
                let mut s = format!("type {a}");
                if **l != Type::Bot {
                    s += &format!(" >: {}", self.show_in(l, hidden));
                }
                if **u != Type::Top {
                    s += &format!(" <: {}", self.show_in(u, hidden));
                }
                s
            }
            t => self.show_in(t, hidden),
        };
        match t {
            Type::Top => "Top".to_string(),
            Type::Bot => "Bot".to_string(),
            Type::Int => "Int".to_string(),
            Type::Bool => "Bool".to_string(),
            Type::Unit => "Unit".to_string(),
            Type::Str => "String".to_string(),
            Type::Field(..) | Type::VarField(..) | Type::Member(..) => format!("{{ {} }}", decl(t, hidden)),
            Type::Select(Path::Var(x), a) if hidden.last() == Some(x) => a.clone(),
            Type::Select(Path::Var(x), a) if a == "T" && self.type_params.contains(x) => self.name(*x).to_string(),
            Type::Select(Path::Var(x), a) if self.groups.contains(x) => a.clone(),
            Type::Select(p, a) => format!("{}.{a}", self.path(p)),
            Type::And(..) => {
                let mut all = vec![];
                members(t, &mut all);
                if all.len() == 1 {
                    return self.show_in(all[0], hidden);
                }
                if all.iter().all(|t| matches!(t, Type::Field(..) | Type::VarField(..) | Type::Member(..))) {
                    format!("{{ {} }}", all.iter().map(|t| decl(t, hidden)).collect::<Vec<_>>().join("; "))
                } else {
                    let parts: Vec<String> = all
                        .iter()
                        .map(|t| match t {
                            Type::Fun(..) => format!("({})", self.show_in(t, hidden)),
                            t => self.show_in(t, hidden),
                        })
                        .collect();
                    parts.join(" & ")
                }
            }
            Type::Fun(x, a, b) => {
                let (a_shown, b_shown) = (self.show_in(a, hidden), self.show_in(b, hidden));
                if b.mentions(*x) {
                    format!("({}: {a_shown}) => {b_shown}", self.name(*x))
                } else if matches!(**a, Type::Fun(..) | Type::And(..)) {
                    format!("({a_shown}) => {b_shown}")
                } else {
                    format!("{a_shown} => {b_shown}")
                }
            }
            Type::Params(_) => "Top".to_string(),
            Type::Applied(f, args) => {
                format!("{}[{}]", self.show_in(f, hidden), args.iter().map(|a| self.show_in(a, hidden)).collect::<Vec<_>>().join(", "))
            }
            Type::Rec(z, body) => {
                let mut all = vec![];
                members(body, &mut all);
                let anonymous = self.name(*z) == "this" && !inner_record_mentions(body, *z);
                if anonymous {
                    hidden.push(*z);
                }
                let decls = all.iter().map(|t| decl(t, hidden)).collect::<Vec<_>>().join("; ");
                if anonymous {
                    hidden.pop();
                    format!("{{ {decls} }}")
                } else {
                    format!("{{ {} => {decls} }}", self.name(*z))
                }
            }
        }
    }
}

/// Whether a recursive type inside `t` mentions `z`, so `z`'s members can't
/// be written without its name there.
fn inner_record_mentions(t: &Type, z: Var) -> bool {
    match t {
        Type::Rec(_, body) => body.mentions(z),
        Type::Field(_, u) | Type::VarField(_, u) => inner_record_mentions(u, z),
        Type::Member(_, a, b) | Type::And(a, b) | Type::Fun(_, a, b) => inner_record_mentions(a, z) || inner_record_mentions(b, z),
        _ => false,
    }
}
