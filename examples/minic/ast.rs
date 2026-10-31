//! The program as a tree: what the parser builds, the checker checks and
//! code generation walks. It says nothing about the VM.

/// The whole program.
pub struct Module {
    pub structs: Vec<Struct>,
    pub funcs: Vec<Function>,
}

/// `struct Point { x, y }`: a block of cells, one for each field, in order.
pub struct Struct {
    pub name: String,
    pub fields: Vec<String>,
}

pub struct Function {
    pub name: String,
    pub params: Vec<String>,
    pub body: Vec<Stmt>,
}

pub enum Stmt {
    /// `let x = e;` (a new variable)
    Let(String, Expr),
    /// `let buf[n];`: an array of n cells on the stack, for the rest of the
    /// function call (`buf` is its address)
    LetArray(String, i64),
    /// `let p: Point;`: a struct on the stack, for the rest of the call
    /// (`p` is its address, like an array's)
    LetStruct(String, String),
    /// `x = e;`, `a[i] = e;` or `*p = e;`
    Assign(Target, Expr),
    /// `if c { .. } else { .. }` (an `else if` is an `if` alone in the else)
    If(Expr, Vec<Stmt>, Vec<Stmt>),
    /// `while c { .. }`
    While(Expr, Vec<Stmt>),
    /// `return e;` or `return;`
    Return(Option<Expr>),
    Break,
    Continue,
    /// `print(a, "text", b);`
    Print(Vec<PrintArg>),
    /// `f(x);`, for what it does
    Expr(Expr),
}

/// What can be assigned to.
pub enum Target {
    Var(String),
    Index(Expr, Expr),
    Deref(Expr),
    Field(Expr, String),
}

pub enum PrintArg {
    Str(String),
    Expr(Expr),
}

pub enum Expr {
    Int(i64),
    Var(String),
    /// `a[i]`
    Index(Box<Expr>, Box<Expr>),
    /// `f(a, b)`, including the built-in `read()` and `array(n)`
    Call(String, Vec<Expr>),
    Neg(Box<Expr>),
    Not(Box<Expr>),
    /// `&x` or `&a[i]`: an address
    AddrOf(Box<Expr>),
    /// `*p`: the cell at an address
    Deref(Box<Expr>),
    /// `p.x`: a field of the struct at address p (C's `p->x`)
    Field(Box<Expr>, String),
    /// `new Point`: a struct on the heap: its address
    New(String),
    /// `sizeof(Point)`: how many cells a struct takes
    SizeOf(String),
    Binary(Op, Box<Expr>, Box<Expr>),
}

#[derive(Clone, Copy, PartialEq)]
pub enum Op {
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
    /// `&&` and `||`, which only work out their right side if they need it
    And,
    Or,
}

impl Expr {
    /// Whether working it out calls a function (which can change memory).
    pub fn has_call(&self) -> bool {
        match self {
            Expr::Int(_) | Expr::Var(_) | Expr::New(_) | Expr::SizeOf(_) => false,
            Expr::Field(a, _) => a.has_call(),
            Expr::Call(..) => true,
            Expr::Index(a, b) | Expr::Binary(_, a, b) => a.has_call() || b.has_call(),
            Expr::Neg(a) | Expr::Not(a) | Expr::AddrOf(a) | Expr::Deref(a) => a.has_call(),
        }
    }
}

/// Whether any of `funcs` calls `name`.
pub fn calls(funcs: &[Function], name: &str) -> bool {
    fn in_expr(e: &Expr, name: &str) -> bool {
        match e {
            Expr::Int(_) | Expr::Var(_) | Expr::New(_) | Expr::SizeOf(_) => false,
            Expr::Field(a, _) => in_expr(a, name),
            Expr::Call(n, args) => n == name || args.iter().any(|a| in_expr(a, name)),
            Expr::Index(a, b) | Expr::Binary(_, a, b) => in_expr(a, name) || in_expr(b, name),
            Expr::Neg(a) | Expr::Not(a) | Expr::AddrOf(a) | Expr::Deref(a) => in_expr(a, name),
        }
    }
    fn in_target(t: &Target, name: &str) -> bool {
        match t {
            Target::Var(_) => false,
            Target::Index(a, i) => in_expr(a, name) || in_expr(i, name),
            Target::Deref(p) | Target::Field(p, _) => in_expr(p, name),
        }
    }
    fn in_stmts(stmts: &[Stmt], name: &str) -> bool {
        stmts.iter().any(|s| match s {
            Stmt::Let(_, e) | Stmt::Expr(e) => in_expr(e, name),
            Stmt::Assign(t, e) => in_target(t, name) || in_expr(e, name),
            Stmt::LetArray(..) | Stmt::LetStruct(..) => false,
            Stmt::If(c, t, o) => in_expr(c, name) || in_stmts(t, name) || in_stmts(o, name),
            Stmt::While(c, b) => in_expr(c, name) || in_stmts(b, name),
            Stmt::Return(e) => e.as_ref().is_some_and(|e| in_expr(e, name)),
            Stmt::Print(args) => args.iter().any(|a| matches!(a, PrintArg::Expr(e) if in_expr(e, name))),
            Stmt::Break | Stmt::Continue => false,
        })
    }
    funcs.iter().any(|f| in_stmts(&f.body, name))
}

/// Where each field is in its struct, in cells from the start. Field names
/// are global, as they were in the first C compilers: without types,
/// `p.x` can't look up which struct p points to, so `x` has to be at the
/// same offset in every struct that has one.
pub fn field_offsets(structs: &[Struct]) -> Result<std::collections::HashMap<String, i64>, String> {
    let mut offsets = std::collections::HashMap::new();
    for s in structs {
        for (i, field) in s.fields.iter().enumerate() {
            if let Some(&j) = offsets.get(field) {
                if j != i as i64 {
                    return Err(format!("the field {field} is at different places in different structs"));
                }
            }
            offsets.insert(field.clone(), i as i64);
        }
    }
    Ok(offsets)
}
