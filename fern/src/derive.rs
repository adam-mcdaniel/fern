//! `#[derive(Eq, Ord, Show)]`: writes the impls, as syntax, for the type
//! checker to check like any other.
//!
//! - `Eq`: the same variant, with equal fields.
//! - `Ord`: by variant (in the order they're declared), then field by
//!   field.
//! - `Show`: `Name(a, b)`, or `Name { x: 1, y: 2 }` for a struct.
//!
//! And the standard library's `Eq`, `Ord` and `Show` for tuples, of every
//! size from 2 to 12 (`tuple_impls`): the same rules, written for each.

use crate::ast::*;
use crate::lexer::Pos;

pub fn struct_impls(s: &StructDef) -> Result<Vec<ImplDef>, (Pos, String)> {
    let pos = s.pos;
    let b = Build { pos };
    let fields: Vec<&String> = s.fields.iter().map(|(f, _)| f).collect();
    s.derives
        .iter()
        .map(|d| {
            let (trait_, method) = match d.as_str() {
                "Eq" => {
                    // self.a == other.a && ...
                    let tests = fields.iter().map(|f| b.binary(BinOp::Eq, b.field("self", f), b.field("other", f)));
                    ("Eq", b.method("eq", true, "Bool", b.all(tests)))
                }
                "Ord" => {
                    let pairs = fields.iter().map(|f| (b.field("self", f), b.field("other", f))).collect();
                    ("Ord", b.method("cmp", true, "Int", b.lexicographic(pairs)))
                }
                "Show" => {
                    // "Point { x: " ++ self.x.show() ++ ", y: " ++ ... ++ " }"
                    let mut parts = vec![];
                    for (i, f) in fields.iter().enumerate() {
                        let label = if i == 0 { format!("{} {{ {f}: ", s.name) } else { format!(", {f}: ") };
                        parts.push(b.str(&label));
                        parts.push(b.call_method(b.field("self", f), "show"));
                    }
                    parts.push(b.str(if fields.is_empty() { &s.name } else { " }" }));
                    let body = if fields.is_empty() { b.str(&s.name) } else { b.concat(parts) };
                    ("Show", b.method("show", false, "String", body))
                }
                _ => return Err((pos, format!("can't derive {d} (only Eq, Ord and Show)"))),
            };
            Ok(b.impl_(trait_, &s.name, &s.generics, method))
        })
        .collect()
}

pub fn enum_impls(e: &EnumDef) -> Result<Vec<ImplDef>, (Pos, String)> {
    let pos = e.pos;
    let b = Build { pos };
    e.derives
        .iter()
        .map(|d| {
            let (trait_, method) = match d.as_str() {
                "Eq" => {
                    // match (self, other) { (A(a0, a1), A(b0, b1)) => a0 == b0 && a1 == b1, ..., _ => false }
                    let mut arms = vec![];
                    for (v, fields) in &e.variants {
                        let n = fields.len();
                        let pat = b.pat_tuple(vec![b.pat_ctor(v, "a", n), b.pat_ctor(v, "b", n)]);
                        let tests = (0..n).map(|i| b.binary(BinOp::Eq, b.var(&format!("a{i}")), b.var(&format!("b{i}"))));
                        arms.push((pat, b.all(tests)));
                    }
                    if e.variants.len() > 1 {
                        arms.push((b.pat(PatKind::Wild), b.bool(false)));
                    }
                    ("Eq", b.method("eq", true, "Bool", b.match_(b.tuple(vec![b.var("self"), b.var("other")]), arms)))
                }
                "Ord" => {
                    // the same variant: field by field; else by which comes first
                    let mut arms = vec![];
                    for (v, fields) in &e.variants {
                        let n = fields.len();
                        let pat = b.pat_tuple(vec![b.pat_ctor(v, "a", n), b.pat_ctor(v, "b", n)]);
                        let pairs = (0..n).map(|i| (b.var(&format!("a{i}")), b.var(&format!("b{i}")))).collect();
                        arms.push((pat, b.lexicographic(pairs)));
                    }
                    if e.variants.len() > 1 {
                        let index = |x: &str| {
                            let arms = e.variants.iter().enumerate().map(|(k, (v, fs))| (b.pat_ctor_wild(v, fs.len()), b.int(k as i64))).collect();
                            b.match_(b.var(x), arms)
                        };
                        arms.push((b.pat(PatKind::Wild), b.int_cmp(index("self"), index("other"))));
                    }
                    ("Ord", b.method("cmp", true, "Int", b.match_(b.tuple(vec![b.var("self"), b.var("other")]), arms)))
                }
                "Show" => {
                    // match self { A(a0, a1) => "A(" ++ a0.show() ++ ", " ++ a1.show() ++ ")", B => "B" }
                    let mut arms = vec![];
                    for (v, fields) in &e.variants {
                        let n = fields.len();
                        let body = if n == 0 {
                            b.str(v)
                        } else {
                            let mut parts = vec![b.str(&format!("{v}("))];
                            for i in 0..n {
                                if i > 0 {
                                    parts.push(b.str(", "));
                                }
                                parts.push(b.call_method(b.var(&format!("a{i}")), "show"));
                            }
                            parts.push(b.str(")"));
                            b.concat(parts)
                        };
                        arms.push((b.pat_ctor(v, "a", n), body));
                    }
                    ("Show", b.method("show", false, "String", b.match_(b.var("self"), arms)))
                }
                _ => return Err((pos, format!("can't derive {d} (only Eq, Ord and Show)"))),
            };
            Ok(b.impl_(trait_, &e.name, &e.generics, method))
        })
        .collect()
}

/// Making syntax, all at one position.
struct Build {
    pos: Pos,
}

impl Build {
    fn e(&self, kind: ExprKind) -> Expr {
        Expr { kind, pos: self.pos }
    }
    fn path(&self, name: &str) -> Path {
        Path { segments: vec![name.to_string()], pos: self.pos }
    }
    fn var(&self, name: &str) -> Expr {
        self.e(ExprKind::Path(self.path(name)))
    }
    fn str(&self, s: &str) -> Expr {
        self.e(ExprKind::Str(s.to_string()))
    }
    fn int(&self, n: i64) -> Expr {
        self.e(ExprKind::Int(n))
    }
    fn bool(&self, v: bool) -> Expr {
        self.e(ExprKind::Bool(v))
    }
    fn field(&self, of: &str, f: &str) -> Expr {
        self.e(ExprKind::Field(Box::new(self.var(of)), f.to_string()))
    }
    fn binary(&self, op: BinOp, a: Expr, b: Expr) -> Expr {
        self.e(ExprKind::Binary(op, Box::new(a), Box::new(b)))
    }
    fn call_method(&self, recv: Expr, name: &str) -> Expr {
        self.e(ExprKind::Method(Box::new(recv), name.to_string(), vec![]))
    }
    fn tuple(&self, es: Vec<Expr>) -> Expr {
        self.e(ExprKind::Tuple(es))
    }
    fn match_(&self, scrutinee: Expr, arms: Vec<(Pattern, Expr)>) -> Expr {
        self.e(ExprKind::Match(Box::new(scrutinee), arms))
    }
    /// `a && b && ...` (true for none)
    fn all(&self, tests: impl Iterator<Item = Expr>) -> Expr {
        tests.reduce(|a, b| self.binary(BinOp::And, a, b)).unwrap_or_else(|| self.bool(true))
    }
    /// `a ++ b ++ ...`
    fn concat(&self, parts: Vec<Expr>) -> Expr {
        parts.into_iter().reduce(|a, b| self.binary(BinOp::Concat, a, b)).unwrap()
    }
    /// `if a < b { -1 } else if a > b { 1 } else { 0 }`
    fn int_cmp(&self, a: Expr, b: Expr) -> Expr {
        let block = |e: Expr| self.e(ExprKind::Block(vec![], Some(Box::new(e))));
        let inner = self.e(ExprKind::If(Box::new(self.binary(BinOp::Gt, a.clone(), b.clone())), Box::new(block(self.int(1))), Some(Box::new(block(self.int(0))))));
        self.e(ExprKind::If(Box::new(self.binary(BinOp::Lt, a, b)), Box::new(block(self.int(-1))), Some(Box::new(inner))))
    }
    /// Comparing pairs in order: `{ let c = a0.cmp(b0); if c != 0 { c } else { ... } }`
    fn lexicographic(&self, mut pairs: Vec<(Expr, Expr)>) -> Expr {
        if pairs.is_empty() {
            return self.int(0);
        }
        let (a, b) = pairs.remove(0);
        let rest = self.lexicographic(pairs);
        let c = self.e(ExprKind::Method(Box::new(a), "cmp".into(), vec![b]));
        let test = self.binary(BinOp::Ne, self.var("c%"), self.int(0));
        let block = |e: Expr| self.e(ExprKind::Block(vec![], Some(Box::new(e))));
        let choose = self.e(ExprKind::If(Box::new(test), Box::new(block(self.var("c%"))), Some(Box::new(block(rest)))));
        let let_ = Stmt::Let { pat: self.pat(PatKind::Bind("c%".into())), mutable: false, ty: None, value: c };
        self.e(ExprKind::Block(vec![let_], Some(Box::new(choose))))
    }
    fn pat(&self, kind: PatKind) -> Pattern {
        Pattern { kind, pos: self.pos }
    }
    fn pat_tuple(&self, ps: Vec<Pattern>) -> Pattern {
        self.pat(PatKind::Tuple(ps))
    }
    /// `V(prefix0, prefix1, ...)`
    fn pat_ctor(&self, v: &str, prefix: &str, n: usize) -> Pattern {
        let subs = (0..n).map(|i| self.pat(PatKind::Bind(format!("{prefix}{i}")))).collect();
        self.pat(PatKind::Ctor(self.path(v), subs))
    }
    fn pat_ctor_wild(&self, v: &str, n: usize) -> Pattern {
        self.pat(PatKind::Ctor(self.path(v), (0..n).map(|_| self.pat(PatKind::Wild)).collect()))
    }
    /// `fn name(self[, other: Self]) -> ret { body }`
    fn method(&self, name: &str, other: bool, ret: &str, body: Expr) -> FnDef {
        let mut params = vec![Param { name: "self".into(), ty: Some(TypeExpr::SelfType), mutable: false }];
        if other {
            params.push(Param { name: "other".into(), ty: Some(TypeExpr::SelfType), mutable: false });
        }
        FnDef {
            name: name.into(),
            public: true,
            generics: vec![],
            params,
            has_self: true,
            ret: Some(TypeExpr::Named(self.path(ret), vec![])),
            effects: None,
            body: Some(self.e(ExprKind::Block(vec![], Some(Box::new(body))))),
            pos: self.pos,
        }
    }
    /// `impl<T: Trait, ..> Trait for Type<T, ..> { method }`
    fn impl_(&self, trait_: &str, ty: &str, generics: &[String], method: FnDef) -> ImplDef {
        ImplDef {
            generics: generics.iter().map(|g| Generic { name: g.clone(), bounds: vec![self.path(trait_)], effect: false }).collect(),
            trait_: self.path(trait_),
            ty: TypeExpr::Named(self.path(ty), generics.iter().map(|g| TypeExpr::Named(self.path(g), vec![])).collect()),
            assoc: vec![],
            methods: vec![method],
            pos: self.pos,
        }
    }
}

/// `Eq`, `Ord` and `Show` for tuples of 2 to 12, as fern source for the
/// standard library: equal if each part is, ordered by the first part
/// that differs, shown as `(a, b)`.
pub fn tuple_impls() -> String {
    let mut out = String::new();
    for n in 2..=12 {
        let list = |f: &dyn Fn(usize) -> String, sep: &str| (0..n).map(f).collect::<Vec<_>>().join(sep);
        let ty = format!("({})", list(&|i| format!("T{i}"), ", "));
        let generics = |t: &str| list(&|i| format!("T{i}: {t}"), ", ");
        let unpack = format!("let ({}) = self;\n        let ({}) = other;", list(&|i| format!("x{i}"), ", "), list(&|i| format!("y{i}"), ", "));
        out += &format!(
            "impl<{}> Eq for {ty} {{\n    fn eq(self, other: {ty}) -> Bool {{\n        {unpack}\n        {}\n    }}\n}}\n\n",
            generics("Eq"),
            list(&|i| format!("x{i} == y{i}"), " && ")
        );
        // (the first part that differs decides)
        let mut cmp = format!("x{}.cmp(y{})", n - 1, n - 1);
        for i in (0..n - 1).rev() {
            cmp = format!("{{ let c = x{i}.cmp(y{i}); if c != 0 {{ c }} else {{ {cmp} }} }}");
        }
        out += &format!("impl<{}> Ord for {ty} {{\n    fn cmp(self, other: {ty}) -> Int {{\n        {unpack}\n        {cmp}\n    }}\n}}\n\n", generics("Ord"));
        out += &format!(
            "impl<{}> Show for {ty} {{\n    fn show(self) -> String {{\n        let ({}) = self;\n        \"(\" ++ {} ++ \")\"\n    }}\n}}\n\n",
            generics("Show"),
            list(&|i| format!("x{i}"), ", "),
            list(&|i| format!("x{i}.show()"), " ++ \", \" ++ ")
        );
    }
    out
}
