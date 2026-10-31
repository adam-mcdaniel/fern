//! Tokens into the syntax tree, by recursive descent: one function for each
//! kind of thing, and binary operators by precedence climbing.

use crate::ast::*;
use crate::lexer::{Pos, Tok, Token};

pub type PResult<T> = Result<T, (Pos, String)>;

pub fn parse(tokens: Vec<Token>) -> PResult<Vec<Item>> {
    let mut p = Parser { tokens, pos: 0, no_struct: false };
    let mut items = vec![];
    while p.peek() != &Tok::Eof {
        items.push(p.item()?);
    }
    Ok(items)
}

struct Parser {
    tokens: Vec<Token>,
    pos: usize,
    /// Whether `Name {` isn't a struct literal here: in an `if`, `while`,
    /// `match` or `handle`'s first part, where `{` starts the block after it.
    no_struct: bool,
}

impl Parser {
    fn peek(&self) -> &Tok {
        &self.tokens[self.pos].tok
    }

    fn peek_at(&self, k: usize) -> &Tok {
        &self.tokens[(self.pos + k).min(self.tokens.len() - 1)].tok
    }

    fn here(&self) -> Pos {
        self.tokens[self.pos].pos
    }

    fn next(&mut self) -> Tok {
        let t = self.tokens[self.pos].tok.clone();
        if t != Tok::Eof {
            self.pos += 1;
        }
        t
    }

    fn error<T>(&self, what: &str) -> PResult<T> {
        Err((self.here(), format!("expected {what}, found {}", self.peek())))
    }

    fn is(&self, s: &str) -> bool {
        match self.peek() {
            Tok::Sym(x) => *x == s,
            Tok::Ident(x) => x == s,
            _ => false,
        }
    }

    fn eat(&mut self, s: &str) -> bool {
        // (`>>` closes two lists of type arguments: `Option<List<Int>>`)
        if s == ">" && self.is(">>") {
            self.tokens[self.pos].tok = Tok::Sym(">");
            return true;
        }
        let here = self.is(s);
        if here {
            self.next();
        }
        here
    }

    fn expect(&mut self, s: &str) -> PResult<()> {
        if self.eat(s) { Ok(()) } else { self.error(&format!("'{s}'")) }
    }

    fn ident(&mut self) -> PResult<String> {
        match self.peek().clone() {
            Tok::Ident(name) => {
                self.next();
                Ok(name)
            }
            _ => self.error("a name"),
        }
    }

    /// `a::b::c`
    fn path(&mut self) -> PResult<Path> {
        let pos = self.here();
        let mut segments = vec![self.ident()?];
        while self.is("::") && matches!(self.peek_at(1), Tok::Ident(_)) {
            self.next();
            segments.push(self.ident()?);
        }
        Ok(Path { segments, pos })
    }

    /// Items separated by `sep`, up to `close`.
    fn list<T>(&mut self, close: &str, mut one: impl FnMut(&mut Self) -> PResult<T>) -> PResult<Vec<T>> {
        let mut out = vec![];
        while !self.eat(close) {
            out.push(one(self)?);
            if !self.eat(",") {
                self.expect(close)?;
                break;
            }
        }
        Ok(out)
    }

    // ---- items

    fn item(&mut self) -> PResult<Item> {
        let mut derives = vec![];
        while self.eat("#") {
            self.expect("[")?;
            let attr = self.ident()?;
            if attr != "derive" {
                return Err((self.here(), format!("unknown attribute {attr}")));
            }
            self.expect("(")?;
            derives.extend(self.list(")", |p| p.ident())?);
            self.expect("]")?;
        }
        let public = self.eat("pub");
        let pos = self.here();
        let item = match self.peek() {
            Tok::Ident(k) if k == "mod" => {
                self.next();
                let name = self.ident()?;
                let body = if self.eat(";") {
                    None
                } else {
                    self.expect("{")?;
                    let mut items = vec![];
                    while !self.eat("}") {
                        items.push(self.item()?);
                    }
                    Some(items)
                };
                Item::Mod { name, public, body, pos }
            }
            Tok::Ident(k) if k == "use" => {
                self.next();
                let mut uses = vec![];
                self.use_tree(vec![], &mut uses)?;
                self.expect(";")?;
                Item::Use { public, uses }
            }
            Tok::Ident(k) if k == "fn" => Item::Fn(self.fn_def(public, false)?),
            Tok::Ident(k) if k == "extern" => {
                self.next();
                let f = self.fn_def(public, true)?;
                if f.body.is_some() || !f.generics.is_empty() {
                    return Err((pos, "an extern fn has no body or type parameters: it's `extern fn name(x: Int) -> Int;`".into()));
                }
                if let Some(p) = f.params.iter().find(|p| p.ty.is_none()) {
                    return Err((pos, format!("extern fn {}'s parameter {} needs a type", f.name, p.name)));
                }
                Item::Extern(f)
            }
            Tok::Ident(k) if k == "struct" => {
                self.next();
                let name = self.ident()?;
                let generics = self.type_params()?;
                self.expect("{")?;
                let fields = self.list("}", |p| {
                    let f = p.ident()?;
                    p.expect(":")?;
                    Ok((f, p.ty()?))
                })?;
                Item::Struct(StructDef { name, public, generics, fields, derives: std::mem::take(&mut derives), pos })
            }
            Tok::Ident(k) if k == "enum" => {
                self.next();
                let name = self.ident()?;
                let generics = self.type_params()?;
                self.expect("{")?;
                let variants = self.list("}", |p| {
                    let v = p.ident()?;
                    let fields = if p.eat("(") { p.list(")", |p| p.ty())? } else { vec![] };
                    Ok((v, fields))
                })?;
                Item::Enum(EnumDef { name, public, generics, variants, derives: std::mem::take(&mut derives), pos })
            }
            Tok::Ident(k) if k == "trait" => {
                self.next();
                let name = self.ident()?;
                let mut supers = vec![];
                if self.eat(":") {
                    supers.push(self.path()?);
                    while self.eat("+") {
                        supers.push(self.path()?);
                    }
                }
                self.expect("{")?;
                let (mut assoc, mut methods) = (vec![], vec![]);
                while !self.eat("}") {
                    // (`type Item;`, an associated type)
                    if self.eat("type") {
                        let name = self.ident()?;
                        let mut bounds = vec![];
                        if self.eat(":") {
                            bounds.push(self.path()?);
                            while self.eat("+") {
                                bounds.push(self.path()?);
                            }
                        }
                        assoc.push((name, bounds));
                        self.expect(";")?;
                    } else {
                        methods.push(self.fn_def(true, true)?);
                    }
                }
                Item::Trait(TraitDef { name, public, supers, assoc, methods, pos })
            }
            Tok::Ident(k) if k == "impl" => {
                self.next();
                let generics = self.generics()?;
                // `impl Trait for Type`, or `impl Type`: its own methods
                let first = self.ty()?;
                if self.eat("for") {
                    let TypeExpr::Named(trait_, args) = first else { return Err((pos, "expected a trait before `for`".into())) };
                    if !args.is_empty() {
                        return Err((pos, "a trait takes no type arguments".into()));
                    }
                    let ty = self.ty()?;
                    self.expect("{")?;
                    let (mut assoc, mut methods) = (vec![], vec![]);
                    while !self.eat("}") {
                        // (`type Item = Int;`, what an associated type is)
                        let at = self.here();
                        if self.eat("type") {
                            let name = self.ident()?;
                            self.expect("=")?;
                            assoc.push((name, self.ty()?, at));
                            self.expect(";")?;
                        } else {
                            methods.push(self.fn_def(true, false)?);
                        }
                    }
                    Item::Impl(ImplDef { generics, trait_, ty, assoc, methods, pos })
                } else {
                    self.expect("{")?;
                    let mut methods = vec![];
                    while !self.eat("}") {
                        let public = self.eat("pub");
                        methods.push(self.fn_def(public, false)?);
                    }
                    Item::Methods(MethodsDef { generics, ty: first, methods, pos })
                }
            }
            Tok::Ident(k) if k == "effect" => {
                self.next();
                let name = self.ident()?;
                let generics = self.type_params()?;
                self.expect("{")?;
                let mut ops = vec![];
                while !self.eat("}") {
                    ops.push(self.fn_def(true, true)?);
                }
                Item::Effect(EffectDef { name, public, generics, ops, pos })
            }
            _ => return self.error("an item (fn, struct, enum, trait, impl, effect, mod or use)"),
        };
        if !derives.is_empty() {
            return Err((pos, "#[derive] only goes on a struct or an enum".into()));
        }
        Ok(item)
    }

    /// The rest of a `use`, after `prefix::`.
    fn use_tree(&mut self, prefix: Vec<String>, out: &mut Vec<Use>) -> PResult<()> {
        let pos = self.here();
        if self.eat("{") {
            let trees = self.list("}", |p| {
                let mut sub = vec![];
                p.use_tree(prefix.clone(), &mut sub)?;
                Ok(sub)
            })?;
            out.extend(trees.into_iter().flatten());
            return Ok(());
        }
        if self.eat("*") {
            out.push(Use { path: Path { segments: prefix, pos }, alias: None, glob: true });
            return Ok(());
        }
        let mut segments = prefix;
        segments.push(self.ident()?);
        if self.eat("::") {
            return self.use_tree(segments, out);
        }
        let alias = if self.eat("as") { Some(self.ident()?) } else { None };
        out.push(Use { path: Path { segments, pos }, alias, glob: false });
        Ok(())
    }

    /// `<T, U>` on a struct, enum or effect (names only)
    fn type_params(&mut self) -> PResult<Vec<String>> {
        if !self.eat("<") {
            return Ok(vec![]);
        }
        self.list(">", |p| p.ident())
    }

    /// `<T: Show + Eq, U, 'e>` on a function or impl
    fn generics(&mut self) -> PResult<Vec<Generic>> {
        if !self.eat("<") {
            return Ok(vec![]);
        }
        self.list(">", |p| {
            if let Tok::Tick(name) = p.peek().clone() {
                p.next();
                return Ok(Generic { name, bounds: vec![], effect: true });
            }
            let name = p.ident()?;
            let mut bounds = vec![];
            if p.eat(":") {
                bounds.push(p.path()?);
                while p.eat("+") {
                    bounds.push(p.path()?);
                }
            }
            Ok(Generic { name, bounds, effect: false })
        })
    }

    /// `fn name<..>(params) -> T with E { body }`, or with `;` instead of a
    /// body (in a trait, `decl` says the body is optional).
    fn fn_def(&mut self, public: bool, decl: bool) -> PResult<FnDef> {
        let pos = self.here();
        self.expect("fn")?;
        let name = self.ident()?;
        let generics = self.generics()?;
        self.expect("(")?;
        let mut has_self = false;
        let mut params = vec![];
        if self.eat("self") {
            has_self = true;
            params.push(Param { name: "self".into(), ty: Some(TypeExpr::SelfType), mutable: false });
            if !self.eat(",") {
                self.expect(")")?;
            } else {
                params.extend(self.list(")", |p| p.param())?);
            }
        } else {
            params = self.list(")", |p| p.param())?;
        }
        let ret = if self.eat("->") { Some(self.ty()?) } else { None };
        let effects = if self.eat("with") { Some(self.effects()?) } else { None };
        let body = if decl && self.eat(";") {
            None
        } else {
            Some(self.block()?)
        };
        Ok(FnDef { name, public, generics, params, has_self, ret, effects, body, pos })
    }

    fn param(&mut self) -> PResult<Param> {
        let mutable = self.eat("mut");
        let name = self.ident()?;
        let ty = if self.eat(":") { Some(self.ty()?) } else { None };
        Ok(Param { name, ty, mutable })
    }

    // ---- types

    fn ty(&mut self) -> PResult<TypeExpr> {
        if self.eat("(") {
            let mut ts = self.list(")", |p| p.ty())?;
            return Ok(if ts.len() == 1 { ts.pop().unwrap() } else { TypeExpr::Tuple(ts) });
        }
        if self.eat("fn") {
            self.expect("(")?;
            let params = self.list(")", |p| p.ty())?;
            let ret = if self.eat("->") { self.ty()? } else { TypeExpr::Tuple(vec![]) };
            let effects = if self.eat("with") { Some(self.effects()?) } else { None };
            return Ok(TypeExpr::Fn(params, Box::new(ret), effects));
        }
        if self.eat("{") {
            let mut fields = vec![];
            let mut rest = None;
            while !self.eat("}") {
                if self.eat("..") {
                    rest = Some(self.ident()?);
                    self.expect("}")?;
                    break;
                }
                let f = self.ident()?;
                self.expect(":")?;
                fields.push((f, self.ty()?));
                if !self.eat(",") {
                    self.expect("}")?;
                    break;
                }
            }
            return Ok(TypeExpr::Record(fields, rest));
        }
        if self.eat("Self") {
            // (`Self::Item`: an associated type)
            if self.eat("::") {
                return Ok(TypeExpr::SelfAssoc(self.ident()?));
            }
            return Ok(TypeExpr::SelfType);
        }
        if self.eat("_") {
            return Ok(TypeExpr::Infer);
        }
        let path = self.path()?;
        let args = if self.eat("<") { self.list(">", |p| p.ty())? } else { vec![] };
        Ok(TypeExpr::Named(path, args))
    }

    /// After `with`: one effect, or `{E1, E2, 'e}`.
    fn effects(&mut self) -> PResult<EffectExpr> {
        let mut e = EffectExpr { effects: vec![], tail: None };
        let braced = self.eat("{");
        loop {
            if let Tok::Tick(name) = self.peek().clone() {
                self.next();
                e.tail = Some(name);
            } else if braced && self.is("}") {
                // (`with {}`: none)
            } else {
                let path = self.path()?;
                let args = if self.eat("<") { self.list(">", |p| p.ty())? } else { vec![] };
                e.effects.push((path, args));
            }
            if !braced || !self.eat(",") {
                break;
            }
        }
        if braced {
            self.expect("}")?;
        }
        Ok(e)
    }

    // ---- expressions

    fn block(&mut self) -> PResult<Expr> {
        let pos = self.here();
        self.expect("{")?;
        let saved = std::mem::replace(&mut self.no_struct, false);
        let mut stmts = vec![];
        let mut tail = None;
        while !self.eat("}") {
            if self.eat("let") {
                let mutable = self.eat("mut");
                let pat = self.pattern()?;
                let ty = if self.eat(":") { Some(self.ty()?) } else { None };
                self.expect("=")?;
                let value = self.expr()?;
                self.expect(";")?;
                stmts.push(Stmt::Let { pat, mutable, ty, value });
                continue;
            }
            // (as in Rust, `if c { .. }` on a line of its own ends there:
            // a `(` on the next line isn't calling it; otherwise the
            // expression goes on from it, parsed once)
            let start = self.here();
            let e = if ["if", "match", "while", "loop", "handle", "{"].iter().any(|k| self.is(k)) {
                let e = self.primary()?;
                if self.is("(") {
                    stmts.push(Stmt::Expr(e));
                    continue;
                }
                let e = self.postfix(e)?;
                let e = self.binary_from(e, 0)?;
                self.expr_from(e, start)?
            } else {
                self.expr()?
            };
            if self.eat(";") {
                stmts.push(Stmt::Expr(e));
            } else if self.eat("}") {
                tail = Some(Box::new(e));
                break;
            } else if block_like(&e) {
                stmts.push(Stmt::Expr(e));
            } else {
                return self.error("';' or '}'");
            }
        }
        self.no_struct = saved;
        Ok(Expr { kind: ExprKind::Block(stmts, tail), pos })
    }

    fn expr(&mut self) -> PResult<Expr> {
        let pos = self.here();
        let e = self.binary(0)?;
        self.expr_from(e, pos)
    }

    /// The rest of an expression that starts with `e`: a range, or an
    /// assignment.
    fn expr_from(&mut self, e: Expr, pos: Pos) -> PResult<Expr> {
        // `a..b` is `std::Range::new(a, b)`, and `a..=b`, `std::Range::new(a, b + 1)`
        if self.is("..") || self.is("..=") {
            let inclusive = self.is("..=");
            self.next();
            let mut end = self.binary(0)?;
            if inclusive {
                let one = Expr { kind: ExprKind::Int(1), pos };
                end = Expr { kind: ExprKind::Binary(BinOp::Add, Box::new(end), Box::new(one)), pos };
            }
            let path = Path { segments: vec!["std".into(), "Range".into(), "new".into()], pos };
            let f = Expr { kind: ExprKind::Path(path), pos };
            return Ok(Expr { kind: ExprKind::Call(Box::new(f), vec![e, end]), pos });
        }
        if self.is("=") {
            // (a variable, or a struct's field: `x = e`, `r.f = e`)
            let kind = match e.kind {
                ExprKind::Path(path) if path.segments.len() == 1 => {
                    self.next();
                    ExprKind::Assign(path.segments[0].clone(), Box::new(self.expr()?))
                }
                ExprKind::Field(r, f) => {
                    self.next();
                    ExprKind::SetField(r, f, Box::new(self.expr()?))
                }
                _ => return Err((pos, "only a variable or a field can be assigned to".into())),
            };
            return Ok(Expr { kind, pos });
        }
        Ok(e)
    }

    /// An expression with no binary operators looser than `min`.
    fn binary(&mut self, min: u8) -> PResult<Expr> {
        let left = self.unary()?;
        self.binary_from(left, min)
    }

    /// The binary operators (no looser than `min`) after `left`.
    fn binary_from(&mut self, mut left: Expr, min: u8) -> PResult<Expr> {
        loop {
            let Tok::Sym(s) = self.peek() else { break };
            let (op, prec) = match *s {
                "||" => (BinOp::Or, 1),
                "&&" => (BinOp::And, 2),
                "==" => (BinOp::Eq, 3),
                "!=" => (BinOp::Ne, 3),
                "<" => (BinOp::Lt, 3),
                "<=" => (BinOp::Le, 3),
                ">" => (BinOp::Gt, 3),
                ">=" => (BinOp::Ge, 3),
                "++" => (BinOp::Concat, 4),
                // (the bitwise ones as in Rust: `x & 0xf == 0` is `(x & 0xf) == 0`)
                "|" => (BinOp::BitOr, 5),
                "^" => (BinOp::BitXor, 6),
                "&" => (BinOp::BitAnd, 7),
                "<<" => (BinOp::Shl, 8),
                ">>" => (BinOp::Shr, 8),
                "+" => (BinOp::Add, 9),
                "-" => (BinOp::Sub, 9),
                "*" => (BinOp::Mul, 10),
                "/" => (BinOp::Div, 10),
                "%" => (BinOp::Rem, 10),
                _ => break,
            };
            if prec < min {
                break;
            }
            let pos = self.here();
            self.next();
            let right = self.binary(prec + 1)?;
            left = Expr { kind: ExprKind::Binary(op, Box::new(left), Box::new(right)), pos };
        }
        Ok(left)
    }

    fn unary(&mut self) -> PResult<Expr> {
        let pos = self.here();
        if self.eat("-") {
            return Ok(Expr { kind: ExprKind::Unary(UnOp::Neg, Box::new(self.unary()?)), pos });
        }
        if self.eat("!") {
            return Ok(Expr { kind: ExprKind::Unary(UnOp::Not, Box::new(self.unary()?)), pos });
        }
        let e = self.primary()?;
        self.postfix(e)
    }

    /// Calls, method calls and fields after `e`.
    fn postfix(&mut self, mut e: Expr) -> PResult<Expr> {
        loop {
            let pos = self.here();
            if self.eat("(") {
                let args = self.list(")", |p| p.expr())?;
                e = Expr { kind: ExprKind::Call(Box::new(e), args), pos };
            } else if self.eat(".") {
                let name = self.ident()?;
                if self.eat("(") {
                    let args = self.list(")", |p| p.expr())?;
                    e = Expr { kind: ExprKind::Method(Box::new(e), name, args), pos };
                } else {
                    e = Expr { kind: ExprKind::Field(Box::new(e), name), pos };
                }
            } else {
                return Ok(e);
            }
        }
    }

    /// A condition or scrutinee: no struct literals (see `no_struct`).
    fn head_expr(&mut self) -> PResult<Expr> {
        let saved = std::mem::replace(&mut self.no_struct, true);
        let e = self.expr();
        self.no_struct = saved;
        e
    }

    fn primary(&mut self) -> PResult<Expr> {
        let pos = self.here();
        let kind = match self.peek().clone() {
            Tok::Int(n) => {
                self.next();
                ExprKind::Int(n)
            }
            // `1.25` is `std::Rational::new(125, 100)`
            Tok::Decimal(n, d) => {
                self.next();
                let path = Path { segments: vec!["std".into(), "Rational".into(), "new".into()], pos };
                let f = Expr { kind: ExprKind::Path(path), pos };
                let arg = |k| Expr { kind: ExprKind::Int(k), pos };
                ExprKind::Call(Box::new(f), vec![arg(n), arg(d)])
            }
            Tok::Str(s) => {
                self.next();
                ExprKind::Str(s)
            }
            Tok::Ident(k) if k == "true" || k == "false" => {
                self.next();
                ExprKind::Bool(k == "true")
            }
            Tok::Ident(k) if k == "if" => {
                self.next();
                return self.if_rest(pos);
            }
            Tok::Ident(k) if k == "match" => {
                self.next();
                let scrutinee = self.head_expr()?;
                self.expect("{")?;
                let mut arms = vec![];
                while !self.eat("}") {
                    let pat = self.pattern()?;
                    self.expect("=>")?;
                    let body = self.expr()?;
                    let blocky = block_like(&body);
                    arms.push((pat, body));
                    if !self.eat(",") && !blocky {
                        self.expect("}")?;
                        break;
                    }
                }
                ExprKind::Match(Box::new(scrutinee), arms)
            }
            Tok::Ident(k) if k == "while" => {
                self.next();
                let cond = self.head_expr()?;
                let body = self.block()?;
                ExprKind::While(Box::new(cond), Box::new(body))
            }
            Tok::Ident(k) if k == "loop" => {
                self.next();
                ExprKind::Loop(Box::new(self.block()?))
            }
            Tok::Ident(k) if k == "break" => {
                self.next();
                ExprKind::Break
            }
            Tok::Ident(k) if k == "continue" => {
                self.next();
                ExprKind::Continue
            }
            Tok::Ident(k) if k == "return" => {
                self.next();
                let value = if self.is(";") || self.is("}") || self.is(",") { None } else { Some(Box::new(self.expr()?)) };
                ExprKind::Return(value)
            }
            Tok::Ident(k) if k == "handle" => {
                self.next();
                let body = self.head_expr()?;
                self.expect("{")?;
                let mut arms = vec![];
                while !self.eat("}") {
                    let op = if self.is("return") {
                        let p = self.here();
                        self.next();
                        Path { segments: vec!["return".into()], pos: p }
                    } else {
                        self.path()?
                    };
                    self.expect("(")?;
                    let params = self.list(")", |p| p.ident())?;
                    self.expect("=>")?;
                    let body = self.expr()?;
                    let blocky = block_like(&body);
                    arms.push(HandlerArm { op, params, body });
                    if !self.eat(",") && !blocky {
                        self.expect("}")?;
                        break;
                    }
                }
                ExprKind::Handle(Box::new(body), arms)
            }
            Tok::Sym("|") | Tok::Sym("||") => {
                let params = if self.eat("||") {
                    vec![]
                } else {
                    self.next();
                    self.list("|", |p| p.param())?
                };
                let body = self.expr()?;
                ExprKind::Lambda(params, Box::new(body))
            }
            Tok::Sym("(") => {
                self.next();
                let mut es = self.list(")", |p| p.expr())?;
                match es.len() {
                    0 => ExprKind::Unit,
                    1 => return Ok(es.pop().unwrap()),
                    _ => ExprKind::Tuple(es),
                }
            }
            Tok::Sym("[") => {
                self.next();
                ExprKind::List(self.list("]", |p| p.expr())?)
            }
            Tok::Sym("{") => {
                // a record (`{ x: ..`, `{ ..r`), or a block
                let record = matches!(self.peek_at(1), Tok::Sym(".."))
                    || (matches!(self.peek_at(1), Tok::Ident(_)) && matches!(self.peek_at(2), Tok::Sym(":")));
                if !record {
                    return self.block();
                }
                self.next();
                let mut fields = vec![];
                let mut base = None;
                while !self.eat("}") {
                    if self.eat("..") {
                        base = Some(Box::new(self.expr()?));
                    } else {
                        let f = self.ident()?;
                        self.expect(":")?;
                        fields.push((f, self.expr()?));
                    }
                    if !self.eat(",") {
                        self.expect("}")?;
                        break;
                    }
                }
                ExprKind::Record(fields, base)
            }
            Tok::Ident(_) => {
                let path = self.path()?;
                // `Point { x: 1 }`, where a struct literal can be
                if !self.no_struct
                    && self.is("{")
                    && path.last().starts_with(char::is_uppercase)
                    && (matches!(self.peek_at(1), Tok::Sym("}")) || matches!(self.peek_at(2), Tok::Sym(":")))
                {
                    self.next();
                    let fields = self.list("}", |p| {
                        let f = p.ident()?;
                        p.expect(":")?;
                        Ok((f, p.expr()?))
                    })?;
                    ExprKind::StructLit(path, fields)
                } else {
                    ExprKind::Path(path)
                }
            }
            _ => return self.error("an expression"),
        };
        Ok(Expr { kind, pos })
    }

    /// After `if`.
    fn if_rest(&mut self, pos: Pos) -> PResult<Expr> {
        let cond = self.head_expr()?;
        let then = self.block()?;
        let otherwise = if self.eat("else") {
            let p = self.here();
            Some(Box::new(if self.eat("if") { self.if_rest(p)? } else { self.block()? }))
        } else {
            None
        };
        Ok(Expr { kind: ExprKind::If(Box::new(cond), Box::new(then), otherwise), pos })
    }

    // ---- patterns

    fn pattern(&mut self) -> PResult<Pattern> {
        let pos = self.here();
        let kind = match self.peek().clone() {
            Tok::Int(n) => {
                self.next();
                PatKind::Int(n)
            }
            Tok::Sym("-") => {
                self.next();
                match self.next() {
                    Tok::Int(n) => PatKind::Int(-n),
                    _ => return self.error("a number"),
                }
            }
            Tok::Str(s) => {
                self.next();
                PatKind::Str(s)
            }
            Tok::Ident(k) if k == "true" || k == "false" => {
                self.next();
                PatKind::Bool(k == "true")
            }
            Tok::Ident(k) if k == "_" => {
                self.next();
                PatKind::Wild
            }
            Tok::Sym("(") => {
                self.next();
                let mut ps = self.list(")", |p| p.pattern())?;
                match ps.len() {
                    0 => PatKind::Unit,
                    1 => return Ok(ps.pop().unwrap()),
                    _ => PatKind::Tuple(ps),
                }
            }
            Tok::Sym("[") => {
                self.next();
                let mut items = vec![];
                let mut rest = None;
                while !self.eat("]") {
                    if self.eat("..") {
                        rest = Some(Box::new(self.pattern()?));
                        self.expect("]")?;
                        break;
                    }
                    items.push(self.pattern()?);
                    if !self.eat(",") {
                        self.expect("]")?;
                        break;
                    }
                }
                PatKind::List(items, rest)
            }
            Tok::Ident(_) => {
                let path = self.path()?;
                if self.eat("(") {
                    PatKind::Ctor(path, self.list(")", |p| p.pattern())?)
                } else if path.segments.len() == 1 && !path.last().starts_with(char::is_uppercase) {
                    // (lower case: a new variable; upper case: a constructor)
                    PatKind::Bind(path.segments[0].clone())
                } else {
                    PatKind::Ctor(path, vec![])
                }
            }
            _ => return self.error("a pattern"),
        };
        Ok(Pattern { kind, pos })
    }
}

/// Whether an expression ends with a block, so a statement of it needs no `;`.
fn block_like(e: &Expr) -> bool {
    matches!(
        e.kind,
        ExprKind::Block(..) | ExprKind::If(..) | ExprKind::Match(..) | ExprKind::While(..) | ExprKind::Loop(..) | ExprKind::Handle(..)
    )
}
