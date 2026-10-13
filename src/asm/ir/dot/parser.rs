//! The lexer and parser, which also resolve names to variables, and turn
//! the language's conveniences into DOT.
//!
//! The syntax is a small Scala:
//!
//! ```text
//! val x: T = t       var x: T = t       x = t       p.a = t       while (c) t
//! def f[A <: U](x: S, y: A): R = t       type A = T       type F[+A, -B] = T
//! new { self => val a = t; var b = t; def m(x: T): U = t; type A = T }
//! new F[X] { members }      module M { members }      module M: Sig { ... }
//! (x: T) => t     x => t     [A] => (x: A) => t     f(a, b)     f[Int](a)
//! t.a     if (c) t else u     (t: T)     { val x = t; u }
//! import std.list      import std.map as maps      import M._      import M.{a, B, c => d}
//! extern def name(x: Int): Int      builtin def mem_new(n: Int): Int
//! "text"     print(t)     println(t)     printc(t)     read()     readc()
//! readLine()     error(message)     // a comment     /* another */
//! ```
//!
//! Types are `Top`, `Bot`, `Int`, `Bool`, `Unit`, `String`, records
//! `{ self => val a: T; var b: T; def m(x: S): T; type A >: L <: U }`,
//! paths' type members `p.A`, intersections `S & T`, refinements
//! `T { decls }` (which are `T & { decls }`), applied types `F[X]`, and
//! functions `S => T`, `(S, T) => U` (the same as `S => T => U`) or
//! `(x: S) => T`, whose result can mention `x`.
//!
//! Everything beyond DOT is written in DOT here:
//!
//! - `module M { members }` is `val M = new { M => members }`, and a signature
//!   `module M: Sig { ... }` ascribes it, hiding what `Sig` makes abstract.
//!   A functor is just a function from modules to modules.
//! - A type parameter is a parameter that's an object with a type member:
//!   `def f[A <: U](x: A)` is `def f(A: { type T <: U }, x: A.T)`, and
//!   `f[Int](3)` passes `new { type T = Int }` (or the checker works out
//!   which, when it's left out).
//! - A type with parameters has them as type members: `type F[+A] = T` is
//!   `type F = { this => type A; T }`, and `F[X]` is `F & { type A <: X }`
//!   (`>: X` for a `-` parameter, `= X` for one without a sign).
//!   `new F[X] { members }` is an object with `type A = X` added, that's
//!   given the type `F[X]`.
//! - `import M._` and `import M.{a, B}` just name `M`'s members, and
//!   `import std.list` loads the module `std/list.dot`, as an object, once.
//!
//! Inside an object or a record type, members can be named without the self
//! variable. Consecutive `def`s, `type`s, `module`s, `extern`s and
//! `builtin`s in a block
//! become one object, so they can refer to each other.

use super::syntax::*;
use super::{Error, Source, FILE_SHIFT};
use std::collections::HashMap;
use std::rc::Rc;

#[derive(Clone, Debug, PartialEq)]
enum Tok {
    Ident(String),
    Int(i64),
    Str(String),
    Sym(&'static str),
    Newline,
    Eof,
}

#[derive(Clone, Debug)]
struct Token {
    tok: Tok,
    pos: usize,
}

const SYMBOLS: [&str; 30] = [
    "=>", "==", "!=", "<=", ">=", "&&", "||", ">:", "<:", "(", ")", "{", "}", "[", "]", ",", ";", ":", ".", "=", "&", "+",
    "-", "*", "/", "%", "<", ">", "!", "_",
];

/// Symbols a statement can't end with, so a newline after one continues it.
const CONTINUES: [&str; 25] = [
    "=>", "==", "!=", "<=", ">=", "&&", "||", ">:", "<:", "(", "{", "[", ",", ";", ":", ".", "=", "&", "+", "-", "*", "/",
    "%", "<", ">",
];

fn lex(src: &str, file: usize) -> Result<Vec<Token>> {
    let base = file << FILE_SHIFT;
    let bytes = src.as_bytes();
    let mut toks: Vec<Token> = vec![];
    let mut i = 0;
    // newlines inside brackets don't end statements
    let mut depth = 0;
    while i < bytes.len() {
        let c = bytes[i];
        if c == b'\n' {
            let continues = match toks.last() {
                None | Some(Token { tok: Tok::Newline, .. }) => true,
                Some(Token { tok: Tok::Sym(s), .. }) => CONTINUES.contains(s),
                _ => false,
            };
            if depth == 0 && !continues {
                toks.push(Token { tok: Tok::Newline, pos: base + i });
            }
            i += 1;
        } else if c.is_ascii_whitespace() {
            i += 1;
        } else if src[i..].starts_with("//") {
            while i < bytes.len() && bytes[i] != b'\n' {
                i += 1;
            }
        } else if src[i..].starts_with("/*") {
            let start = i;
            match src[i + 2..].find("*/") {
                Some(end) => i += end + 4,
                None => return Err(Error::at(base + start, "unterminated comment")),
            }
        } else if c.is_ascii_digit() {
            let start = i;
            while i < bytes.len() && bytes[i].is_ascii_digit() {
                i += 1;
            }
            let n = src[start..i].parse().map_err(|_| Error::at(base + start, "integer too big"))?;
            toks.push(Token { tok: Tok::Int(n), pos: base + start });
        } else if c.is_ascii_alphabetic() || (c == b'_' && bytes.get(i + 1).is_some_and(|b| b.is_ascii_alphanumeric())) {
            let start = i;
            while i < bytes.len() && (bytes[i].is_ascii_alphanumeric() || bytes[i] == b'_') {
                i += 1;
            }
            toks.push(Token { tok: Tok::Ident(src[start..i].to_string()), pos: base + start });
        } else if c == b'"' {
            let start = i;
            i += 1;
            let mut s = String::new();
            while i < bytes.len() && bytes[i] != b'"' {
                if bytes[i] == b'\\' && i + 1 < bytes.len() {
                    i += 1;
                    s.push(match bytes[i] {
                        b'n' => '\n',
                        b't' => '\t',
                        other => other as char,
                    });
                } else {
                    s.push(bytes[i] as char);
                }
                i += 1;
            }
            if i >= bytes.len() {
                return Err(Error::at(base + start, "unterminated string"));
            }
            i += 1;
            toks.push(Token { tok: Tok::Str(s), pos: base + start });
        } else {
            let Some(sym) = SYMBOLS.iter().find(|s| src[i..].starts_with(**s)) else {
                return Err(Error::at(base + i, &format!("unexpected character {:?}", c as char)));
            };
            match *sym {
                "(" | "[" => depth += 1,
                ")" | "]" => depth -= 1,
                _ => {}
            }
            toks.push(Token { tok: Tok::Sym(sym), pos: base + i });
            i += sym.len();
        }
    }
    toks.push(Token { tok: Tok::Eof, pos: base + src.len() });
    // a newline before `else` or `.` continues the statement
    let mut kept: Vec<Token> = vec![];
    for (j, t) in toks.iter().enumerate() {
        if t.tok == Tok::Newline {
            if let Some(next) = toks.get(j + 1) {
                if matches!(&next.tok, Tok::Ident(s) if s == "else") || next.tok == Tok::Sym(".") {
                    continue;
                }
            }
        }
        kept.push(t.clone());
    }
    Ok(kept)
}

const KEYWORDS: [&str; 23] = [
    "val", "var", "def", "type", "new", "if", "else", "while", "true", "false", "module", "import", "extern", "builtin", "print",
    "println", "printc", "read", "readc", "readLine", "error", "_", "this",
];

#[derive(Clone, Debug)]
struct Param {
    name: String,
    variance: Variance,
}

type Params = Option<Rc<Vec<Param>>>;

#[derive(Clone)]
enum Binding {
    Term(Path),
    /// A `var`, which isn't a path.
    Mutable(Var),
    /// A type, with its parameters if it takes any.
    Type(Type, Params),
}

/// What the parser knows about an object's members, for `import` and for
/// applying the types among them to arguments.
#[derive(Clone, Debug, Default)]
struct Members {
    list: Vec<(String, Member)>,
}

#[derive(Clone, Debug)]
enum Member {
    /// A value, and its members if it's a known object.
    Term(Option<Rc<Members>>),
    Type(Params),
}

impl Members {
    fn get(&self, name: &str) -> impl Iterator<Item = &Member> {
        self.list.iter().filter(move |(n, _)| n == name).map(|(_, m)| m)
    }
}

/// A member about to be parsed, found by looking ahead.
#[derive(Clone)]
struct Ahead {
    name: String,
    ty: bool,
    params: Params,
}

/// Finds a module's source by its name: `std.list` for `import std.list`.
pub type Loader<'a> = &'a dyn Fn(&str) -> Option<String>;

pub struct Parser<'a> {
    toks: Vec<Token>,
    at: usize,
    pub names: Names,
    /// Scopes of names: terms and types are separate namespaces.
    scopes: Vec<HashMap<(String, bool), Binding>>,
    /// What's known about the objects variables are bound to.
    roots: HashMap<Var, Rc<Members>>,
    loader: Loader<'a>,
    /// Modules loaded so far, by name, and the ones being loaded.
    loaded: HashMap<String, (Var, Rc<Members>)>,
    loading: Vec<String>,
    /// The loaded modules' objects, in an order where each comes after the
    /// ones it imports.
    modules: Vec<(Var, Term)>,
    pub sources: Vec<Source>,
}

/// Parses a program, loading the modules it imports with `loader`.
pub fn parse(src: &str, loader: Loader) -> std::result::Result<(Term, Names, Vec<Source>), (Error, Vec<Source>)> {
    let mut p = Parser {
        toks: vec![],
        at: 0,
        names: Names::default(),
        scopes: vec![HashMap::new()],
        roots: HashMap::new(),
        loader,
        loaded: HashMap::new(),
        loading: vec![],
        modules: vec![],
        sources: vec![Source { name: "main".to_string(), text: src.to_string() }],
    };
    let result = (|| {
        p.toks = lex(src, 0)?;
        p.skip_newlines();
        let t = p.statements(None)?;
        p.skip_separators();
        if p.peek() != &Tok::Eof {
            return Err(p.error("expected the end of the program"));
        }
        Ok(t)
    })();
    match result {
        Ok(mut t) => {
            // the modules are bound around the program, the first outermost
            for (x, m) in std::mem::take(&mut p.modules).into_iter().rev() {
                t = Term { pos: m.pos, kind: TermKind::Let(x, None, Box::new(m), Box::new(t)) };
            }
            Ok((t, p.names, p.sources))
        }
        Err(e) => Err((e, p.sources)),
    }
}

type Result<T> = std::result::Result<T, Error>;

fn term(pos: usize, kind: TermKind) -> Term {
    Term { pos, kind }
}

impl Parser<'_> {
    fn peek(&self) -> &Tok {
        &self.toks[self.at].tok
    }

    fn peek_at(&self, n: usize) -> &Tok {
        &self.toks[(self.at + n).min(self.toks.len() - 1)].tok
    }

    fn pos(&self) -> usize {
        self.toks[self.at].pos
    }

    fn next(&mut self) -> Tok {
        let t = self.toks[self.at].tok.clone();
        if self.at + 1 < self.toks.len() {
            self.at += 1;
        }
        t
    }

    fn error(&self, msg: &str) -> Error {
        let found = match self.peek() {
            Tok::Ident(s) => format!("`{s}`"),
            Tok::Int(n) => format!("`{n}`"),
            Tok::Str(_) => "a string".to_string(),
            Tok::Sym(s) => format!("`{s}`"),
            Tok::Newline => "the end of the line".to_string(),
            Tok::Eof => "the end of the file".to_string(),
        };
        Error::at(self.pos(), &format!("{msg}, but found {found}"))
    }

    fn is_sym(&self, s: &str) -> bool {
        self.peek() == &Tok::Sym(leak(s))
    }

    fn is_keyword(&self, k: &str) -> bool {
        matches!(self.peek(), Tok::Ident(s) if s == k)
    }

    fn eat_sym(&mut self, s: &str) -> bool {
        if self.is_sym(s) {
            self.next();
            true
        } else {
            false
        }
    }

    fn eat_keyword(&mut self, k: &str) -> bool {
        if self.is_keyword(k) {
            self.next();
            true
        } else {
            false
        }
    }

    fn expect_sym(&mut self, s: &str) -> Result<()> {
        if self.eat_sym(s) { Ok(()) } else { Err(self.error(&format!("expected `{s}`"))) }
    }

    fn ident(&mut self) -> Result<String> {
        match self.peek().clone() {
            Tok::Ident(s) if !KEYWORDS.contains(&s.as_str()) => {
                self.next();
                Ok(s)
            }
            _ => Err(self.error("expected a name")),
        }
    }

    fn skip_newlines(&mut self) {
        while self.peek() == &Tok::Newline {
            self.next();
        }
    }

    fn skip_separators(&mut self) {
        while matches!(self.peek(), Tok::Newline | Tok::Sym(";")) {
            self.next();
        }
    }

    fn bind(&mut self, name: &str, ty: bool, b: Binding) {
        self.scopes.last_mut().unwrap().insert((name.to_string(), ty), b);
    }

    fn lookup(&self, name: &str, ty: bool) -> Option<Binding> {
        self.scopes.iter().rev().find_map(|s| s.get(&(name.to_string(), ty)).cloned())
    }

    fn bind_var(&mut self, name: &str) -> Var {
        let x = self.names.fresh(name);
        self.bind(name, false, Binding::Term(Path::Var(x)));
        x
    }

    fn scoped<T>(&mut self, f: impl FnOnce(&mut Self) -> Result<T>) -> Result<T> {
        self.scopes.push(HashMap::new());
        let r = f(self);
        self.scopes.pop();
        r
    }

    /// What's known about the object at `p`.
    fn members_of(&self, p: &Path) -> Option<Rc<Members>> {
        match p {
            Path::Var(x) => self.roots.get(x).cloned(),
            Path::Sel(q, a) => self.members_of(q)?.get(a).find_map(|m| match m {
                Member::Term(Some(m)) => Some(m.clone()),
                _ => None,
            }),
        }
    }

    /// The members or statements starting here that can refer to each other
    /// (those that begin with one of `starts`), found without moving, so
    /// they can be in scope before any of them is parsed.
    fn ahead(&self, starts: &[&str]) -> Vec<Ahead> {
        let mut found = vec![];
        let mut i = self.at;
        loop {
            while matches!(self.toks[i].tok, Tok::Newline | Tok::Sym(";")) {
                i += 1;
            }
            let Tok::Ident(k) = &self.toks[i].tok else { break };
            // imports among members are skipped over
            if k == "import" && starts.contains(&"val") {
                while !matches!(self.toks[i].tok, Tok::Newline | Tok::Sym(";") | Tok::Sym("}") | Tok::Eof) {
                    i += 1;
                }
                continue;
            }
            if !starts.contains(&k.as_str()) {
                break;
            }
            let mut j = i + 1;
            if k == "extern" || k == "builtin" {
                // past the `def`
                j += 1;
            }
            if let Tok::Ident(name) = &self.toks[j].tok {
                let ty = k == "type";
                let params = if ty && self.toks[j + 1].tok == Tok::Sym("[") { Some(Rc::new(params_at(&self.toks, j + 1))) } else { None };
                found.push(Ahead { name: name.clone(), ty, params });
            }
            // skip to the end of this member
            let mut depth = 0;
            i = j;
            loop {
                match &self.toks[i].tok {
                    Tok::Sym("(") | Tok::Sym("{") | Tok::Sym("[") => depth += 1,
                    Tok::Sym(")") | Tok::Sym("]") => depth -= 1,
                    Tok::Sym("}") if depth == 0 => return found,
                    Tok::Sym("}") => depth -= 1,
                    Tok::Newline | Tok::Sym(";") if depth == 0 => break,
                    Tok::Eof => return found,
                    _ => {}
                }
                i += 1;
            }
        }
        found
    }

    /// Puts the members found ahead in scope, as members of `at`, and notes
    /// them as `at`'s if it's a variable, so `at.F[X]` can be parsed before
    /// `F` is.
    fn bind_members(&mut self, at: &Path, members: &[Ahead]) {
        if let Path::Var(x) = at {
            if !self.roots.contains_key(x) {
                let list = members
                    .iter()
                    .map(|m| (m.name.clone(), if m.ty { Member::Type(m.params.clone()) } else { Member::Term(None) }))
                    .collect();
                self.roots.insert(*x, Rc::new(Members { list }));
            }
        }
        for m in members {
            if m.ty {
                self.bind(&m.name, true, Binding::Type(Type::Select(at.clone(), m.name.clone()), m.params.clone()));
            } else {
                self.bind(&m.name, false, Binding::Term(at.sel(&m.name)));
            }
        }
    }

    /// Statements up to `end` (or the end of the file), as one term.
    fn statements(&mut self, end: Option<&str>) -> Result<Term> {
        enum Stmt {
            Let(Var, Option<Type>, Term),
            LetVar(Var, Option<Type>, Term),
            Expr(Term),
        }
        let at_end = |p: &Parser| match end {
            Some(s) => p.is_sym(s),
            None => p.peek() == &Tok::Eof,
        };
        let mut stmts = vec![];
        let start = self.pos();
        loop {
            self.skip_separators();
            if at_end(self) {
                break;
            }
            let pos = self.pos();
            const GROUPED: [&str; 5] = ["def", "type", "module", "extern", "builtin"];
            if GROUPED.iter().any(|k| self.is_keyword(k)) {
                // a group of definitions becomes an object
                let group = self.names.group();
                let ahead = self.ahead(&GROUPED);
                self.bind_members(&Path::Var(group), &ahead);
                let mut defs = vec![];
                let mut members = Members::default();
                while GROUPED.iter().any(|k| self.is_keyword(k)) {
                    let (def, member) = self.member(Some(&Path::Var(group)))?;
                    members.list.push((def.name.clone(), member));
                    defs.push(def);
                    self.roots.insert(group, Rc::new(members.clone()));
                    self.skip_separators();
                }
                stmts.push(Stmt::Let(group, None, term(pos, TermKind::New(group, None, defs))));
                continue;
            }
            if self.eat_keyword("import") {
                self.import()?;
            } else if self.eat_keyword("val") {
                let name = self.ident()?;
                let ty = if self.eat_sym(":") { Some(self.ty()?) } else { None };
                self.expect_sym("=")?;
                self.skip_newlines();
                let t = self.expr()?;
                let known = self.object_members(&t);
                let x = self.bind_var(&name);
                if let Some(m) = known {
                    self.roots.insert(x, m);
                }
                stmts.push(Stmt::Let(x, ty, t));
            } else if self.eat_keyword("var") {
                let name = self.ident()?;
                let ty = if self.eat_sym(":") { Some(self.ty()?) } else { None };
                self.expect_sym("=")?;
                self.skip_newlines();
                let t = self.expr()?;
                let x = self.names.fresh(&name);
                self.bind(&name, false, Binding::Mutable(x));
                stmts.push(Stmt::LetVar(x, ty, t));
            } else {
                stmts.push(Stmt::Expr(self.expr()?));
            }
            if !at_end(self) && !matches!(self.peek(), Tok::Newline | Tok::Sym(";")) {
                return Err(self.error("expected a new line or `;` after the statement"));
            }
        }
        let mut result = match stmts.pop() {
            Some(Stmt::Expr(t)) => t,
            Some(s) => {
                stmts.push(s);
                term(start, TermKind::Unit)
            }
            None => term(start, TermKind::Unit),
        };
        for s in stmts.into_iter().rev() {
            let pos = result.pos;
            result = match s {
                Stmt::Let(x, ty, t) => term(t.pos, TermKind::Let(x, ty, Box::new(t), Box::new(result))),
                Stmt::LetVar(x, ty, t) => term(t.pos, TermKind::LetVar(x, ty, Box::new(t), Box::new(result))),
                Stmt::Expr(t) => {
                    let ignored = self.names.fresh("_");
                    term(t.pos.min(pos), TermKind::Let(ignored, None, Box::new(t), Box::new(result)))
                }
            };
        }
        Ok(result)
    }

    /// What's known about the object a term makes, if it makes one.
    fn object_members(&self, t: &Term) -> Option<Rc<Members>> {
        match &t.kind {
            TermKind::New(z, ..) => self.roots.get(z).cloned(),
            TermKind::Ascribe(t, _) => self.object_members(t),
            _ => None,
        }
    }

    /// `import a.b.c`, `import p._` or `import p.{a, B => C}`, after
    /// `import`.
    fn import(&mut self) -> Result<()> {
        let pos = self.pos();
        let mut parts = vec![self.ident()?];
        let mut selector = None;
        while self.eat_sym(".") {
            if self.eat_sym("_") {
                selector = Some(None);
                break;
            }
            if self.eat_sym("{") {
                let mut names = vec![];
                loop {
                    self.skip_newlines();
                    let name = self.ident()?;
                    let rename = if self.eat_sym("=>") { self.ident()? } else { name.clone() };
                    names.push((name, rename));
                    self.skip_newlines();
                    if !self.eat_sym(",") {
                        break;
                    }
                }
                self.skip_newlines();
                self.expect_sym("}")?;
                selector = Some(Some(names));
                break;
            }
            parts.push(self.ident()?);
        }
        // `import a.b as c` names it `c`
        let name = if selector.is_none() && self.is_keyword("as") {
            self.next();
            self.ident()?
        } else {
            parts.last().unwrap().clone()
        };
        // a value in scope, or else a module to load
        let value = matches!(self.lookup(&parts[0], false), Some(Binding::Term(_)));
        let (path, members) = match self.lookup(&parts[0], false) {
            Some(Binding::Term(p)) => {
                let path = parts[1..].iter().fold(p, |p, a| p.sel(a));
                let members = self.members_of(&path);
                (path, members)
            }
            Some(Binding::Mutable(_)) => return Err(Error::at(pos, &format!("`{}` is a var, not a module", parts[0]))),
            _ => {
                let (x, members) = self.load(&parts.join("."), pos)?;
                if selector.is_none() {
                    self.bind(&name, false, Binding::Term(Path::Var(x)));
                    self.roots.insert(x, members.clone());
                }
                (Path::Var(x), Some(members))
            }
        };
        match selector {
            None => {
                if value && parts.len() > 1 {
                    // `import a.b` of a value: names `b`
                    self.bind(&name, false, Binding::Term(path.clone()));
                    if let Some(m) = members {
                        if let Path::Var(x) = path {
                            self.roots.insert(x, m);
                        }
                    }
                }
            }
            Some(None) => {
                let Some(members) = members else {
                    return Err(Error::at(pos, "can only import everything from a module or an object whose members are known"));
                };
                for (name, member) in members.list.clone() {
                    self.bind_member(&path, &name, &name, &member);
                }
            }
            Some(Some(names)) => {
                for (name, rename) in names {
                    match &members {
                        Some(members) => {
                            let found: Vec<Member> = members.get(&name).cloned().collect();
                            if found.is_empty() {
                                return Err(Error::at(pos, &format!("there's no `{name}` to import")));
                            }
                            for member in found {
                                self.bind_member(&path, &name, &rename, &member);
                            }
                        }
                        // not known: it could be a value or a type
                        None => {
                            self.bind(&rename, false, Binding::Term(path.sel(&name)));
                            self.bind(&rename, true, Binding::Type(Type::Select(path.clone(), name.clone()), None));
                        }
                    }
                }
            }
        }
        Ok(())
    }

    fn bind_member(&mut self, at: &Path, name: &str, rename: &str, member: &Member) {
        match member {
            Member::Term(_) => self.bind(rename, false, Binding::Term(at.sel(name))),
            Member::Type(params) => self.bind(rename, true, Binding::Type(Type::Select(at.clone(), name.to_string()), params.clone())),
        }
    }

    /// Loads the module called `name` (once), and gives the variable it's
    /// bound to.
    fn load(&mut self, name: &str, pos: usize) -> Result<(Var, Rc<Members>)> {
        if let Some(found) = self.loaded.get(name) {
            return Ok(found.clone());
        }
        if self.loading.iter().any(|n| n == name) {
            return Err(Error::at(pos, &format!("the module `{name}` imports itself, through {}", self.loading.join(", "))));
        }
        let Some(text) = (self.loader)(name) else {
            return Err(Error::at(pos, &format!("there's no module called `{name}`")));
        };
        let file = self.sources.len();
        self.sources.push(Source { name: format!("{}.dot", name.replace('.', "/")), text: text.clone() });
        self.loading.push(name.to_string());
        let saved = (std::mem::take(&mut self.toks), self.at, std::mem::replace(&mut self.scopes, vec![HashMap::new()]));
        let short = name.rsplit('.').next().unwrap().to_string();
        let result = (|| {
            self.toks = lex(&text, file)?;
            self.at = 0;
            let pos = self.pos();
            let z = self.names.fresh(&short);
            // the module can name itself
            self.bind(&short, false, Binding::Term(Path::Var(z)));
            let (defs, members) = self.members(&Path::Var(z), None)?;
            if self.peek() != &Tok::Eof {
                return Err(self.error("expected a definition"));
            }
            self.roots.insert(z, members.clone());
            Ok((term(pos, TermKind::New(z, None, defs)), members))
        })();
        (self.toks, self.at, self.scopes) = saved;
        self.loading.pop();
        let (object, members) = result?;
        let x = self.names.fresh(&short);
        self.modules.push((x, object));
        self.roots.insert(x, members.clone());
        self.loaded.insert(name.to_string(), (x, members.clone()));
        Ok((x, members))
    }

    /// An object's members, as members of `at`, up to `end` (or the end of
    /// the file).
    fn members(&mut self, at: &Path, end: Option<&str>) -> Result<(Vec<Def>, Rc<Members>)> {
        self.scoped(|p| {
            let ahead = p.ahead(&["val", "var", "def", "type", "module", "extern", "builtin"]);
            p.bind_members(at, &ahead);
            let mut defs = vec![];
            let mut members = Members::default();
            loop {
                p.skip_separators();
                let done = match end {
                    Some(s) => p.is_sym(s),
                    None => p.peek() == &Tok::Eof,
                };
                if done {
                    break;
                }
                if p.eat_keyword("import") {
                    p.import()?;
                } else {
                    let (def, member) = p.member(None)?;
                    members.list.push((def.name.clone(), member));
                    defs.push(def);
                }
                if !matches!(p.peek(), Tok::Newline | Tok::Sym(";") | Tok::Sym("}") | Tok::Eof) {
                    return Err(p.error("expected a new line or `;` after the member"));
                }
            }
            Ok((defs, Rc::new(members)))
        })
    }

    /// A member of an object or a group: `val`, `var`, `def`, `type`,
    /// `module`, `extern` or `builtin`. `group` is the group's variable, for
    /// a group.
    fn member(&mut self, group: Option<&Path>) -> Result<(Def, Member)> {
        let pos = self.pos();
        if self.eat_keyword("type") {
            let name = self.ident()?;
            let params = if self.is_sym("[") { Some(self.type_params()?) } else { None };
            if !self.eat_sym("=") {
                return Err(self.error("expected `=`: an object's type members are defined"));
            }
            self.skip_newlines();
            let ty = self.with_type_params(params.as_deref(), |p| p.ty())?;
            let member = Member::Type(params.map(|ps| Rc::new(ps.into_iter().map(|(p, ..)| p).collect())));
            return Ok((Def { name, kind: DefKind::Type(ty), pos }, member));
        }
        if self.is_keyword("val") || self.is_keyword("var") {
            if group.is_some() {
                return Err(Error::at(pos, "a `val` or `var` here would start a new statement"));
            }
            let mutable = self.next() == Tok::Ident("var".to_string());
            let name = self.ident()?;
            let ty = if self.eat_sym(":") { Some(self.ty()?) } else { None };
            self.expect_sym("=")?;
            self.skip_newlines();
            let t = self.expr()?;
            let known = self.object_members(&t);
            let kind = if mutable { DefKind::Var(ty, t) } else { DefKind::Val(ty, t) };
            return Ok((Def { name, kind, pos }, Member::Term(if mutable { None } else { known })));
        }
        if self.eat_keyword("module") {
            let name = self.ident()?;
            let sig = if self.eat_sym(":") { Some(self.type_without_refinements()?) } else { None };
            self.skip_newlines();
            self.expect_sym("{")?;
            let z = self.names.fresh(&name);
            let (defs, members) = self.scoped(|p| {
                p.bind(&name, false, Binding::Term(Path::Var(z)));
                p.members(&Path::Var(z), Some("}"))
            })?;
            self.expect_sym("}")?;
            self.roots.insert(z, members.clone());
            let object = term(pos, TermKind::New(z, None, defs));
            // a module kept behind a signature is only known by it
            let known = if sig.is_some() { None } else { Some(members) };
            return Ok((Def { name, kind: DefKind::Val(sig, object), pos }, Member::Term(known)));
        }
        let kind = if self.eat_keyword("extern") {
            Some(ForeignKind::Extern)
        } else if self.eat_keyword("builtin") {
            Some(ForeignKind::Builtin)
        } else {
            None
        };
        let foreign = kind.is_some();
        if !self.eat_keyword("def") {
            return Err(self.error("expected `val`, `var`, `def`, `type`, `module`, `extern` or `builtin`"));
        }
        let name = self.ident()?;
        let (ty, body) = self.scoped(|p| {
            let types = if p.is_sym("[") { p.bind_type_params()? } else { vec![] };
            let params = if foreign || p.is_sym("(") { p.params()? } else { vec![] };
            let result = if p.eat_sym(":") { Some(p.ty()?) } else { None };
            let body = if let Some(kind) = kind {
                let Some(_) = &result else { return Err(Error::at(pos, "a function declared without a body needs its result type")) };
                if kind == ForeignKind::Extern && params.len() > 9 {
                    return Err(Error::at(pos, "an external function takes at most 9 parameters"));
                }
                term(pos, TermKind::Foreign(name.clone(), params.iter().map(|(x, _)| *x).collect(), kind))
            } else {
                p.expect_sym("=")?;
                p.skip_newlines();
                p.expr()?
            };
            let all: Vec<(Var, Type)> = types.into_iter().chain(params).collect();
            if all.is_empty() {
                return Err(Error::at(pos, &format!("`def {name}` needs parameters: `def {name}() = ...` takes none")));
            }
            let ty = result.map(|r| all.iter().rev().fold(r, |acc, (x, t)| Type::Fun(*x, Box::new(t.clone()), Box::new(acc))));
            let body = all.into_iter().rev().fold(body, |acc, (x, t)| term(pos, TermKind::Lam(x, Some(t), Box::new(acc))));
            Ok((ty, body))
        })?;
        Ok((Def { name, kind: DefKind::Val(ty, body), pos }, Member::Term(None)))
    }

    /// `[+A, -B, C <: U]`, the parameters of a type: each with its variance
    /// and bounds, not yet in scope.
    fn type_params(&mut self) -> Result<Vec<(Param, Type, Type)>> {
        self.expect_sym("[")?;
        let mut params = vec![];
        loop {
            let variance = if self.eat_sym("+") {
                Variance::Co
            } else if self.eat_sym("-") {
                Variance::Contra
            } else {
                Variance::In
            };
            let name = self.ident()?;
            let lower = if self.eat_sym(">:") { self.ty()? } else { Type::Bot };
            let upper = if self.eat_sym("<:") { self.ty()? } else { Type::Top };
            params.push((Param { name, variance }, lower, upper));
            if !self.eat_sym(",") {
                break;
            }
        }
        self.expect_sym("]")?;
        Ok(params)
    }

    /// Parses `f` with a type's parameters in scope, as members of the type
    /// itself, and gives `{ this => type A; ...; f }`.
    fn with_type_params(&mut self, params: Option<&[(Param, Type, Type)]>, f: impl FnOnce(&mut Self) -> Result<Type>) -> Result<Type> {
        let Some(params) = params else { return f(self) };
        self.scoped(|p| {
            let z = p.names.fresh("this");
            for (param, ..) in params {
                p.bind(&param.name, true, Binding::Type(Type::Select(Path::Var(z), param.name.clone()), None));
            }
            let body = f(p)?;
            let note = Type::Params(params.iter().map(|(param, ..)| (param.name.clone(), param.variance)).collect());
            let members: Vec<Type> = std::iter::once(note)
                .chain(params.iter().map(|(param, l, u)| Type::Member(param.name.clone(), Box::new(l.clone()), Box::new(u.clone()))))
                .chain([body])
                .collect();
            let t = Type::and(members);
            Ok(if t.mentions(z) { Type::Rec(z, Box::new(t)) } else { t })
        })
    }

    /// `[A, B <: U]` on a function: each type parameter is a parameter that's
    /// an object with a type member `T`, which the parameter's name stands
    /// for, in scope from here on.
    fn bind_type_params(&mut self) -> Result<Vec<(Var, Type)>> {
        self.expect_sym("[")?;
        let mut params = vec![];
        loop {
            let name = self.ident()?;
            let lower = if self.eat_sym(">:") { self.ty()? } else { Type::Bot };
            let upper = if self.eat_sym("<:") { self.ty()? } else { Type::Top };
            let x = self.names.type_param(&name);
            self.bind(&name, true, Binding::Type(Type::Select(Path::Var(x), "T".to_string()), None));
            params.push((x, Type::Member("T".to_string(), Box::new(lower), Box::new(upper))));
            if !self.eat_sym(",") {
                break;
            }
        }
        self.expect_sym("]")?;
        Ok(params)
    }

    /// `(x: S, y: T)`, bringing each name into scope for what follows. No
    /// parameters is one of type `Unit`.
    fn params(&mut self) -> Result<Vec<(Var, Type)>> {
        Ok(self.maybe_typed_params(true)?.into_iter().map(|(x, t)| (x, t.unwrap())).collect())
    }

    /// Parameters whose types can be left out, unless `typed`.
    fn maybe_typed_params(&mut self, typed: bool) -> Result<Vec<(Var, Option<Type>)>> {
        self.expect_sym("(")?;
        let mut params = vec![];
        if self.eat_sym(")") {
            let x = self.names.fresh("_");
            return Ok(vec![(x, Some(Type::Unit))]);
        }
        loop {
            let name = if self.eat_sym("_") { "_".to_string() } else { self.ident()? };
            let t = if typed || self.is_sym(":") {
                self.expect_sym(":")?;
                Some(self.ty()?)
            } else {
                None
            };
            let x = self.bind_var(&name);
            params.push((x, t));
            if !self.eat_sym(",") {
                break;
            }
        }
        self.expect_sym(")")?;
        Ok(params)
    }

    /// Whether the bracket here closes before `=>`, as a lambda's parameters
    /// do.
    fn lambda_ahead(&self) -> bool {
        let mut depth = 0;
        let mut i = self.at;
        loop {
            match &self.toks[i].tok {
                Tok::Sym("(") | Tok::Sym("[") => depth += 1,
                Tok::Sym(")") | Tok::Sym("]") => {
                    depth -= 1;
                    if depth == 0 {
                        return self.toks[i + 1].tok == Tok::Sym("=>");
                    }
                }
                Tok::Eof => return false,
                _ => {}
            }
            i += 1;
        }
    }

    fn expr(&mut self) -> Result<Term> {
        let pos = self.pos();
        if let (Tok::Ident(name), Tok::Sym("=>")) = (self.peek().clone(), self.peek_at(1).clone()) {
            if !KEYWORDS.contains(&name.as_str()) {
                return self.scoped(|p| {
                    p.next();
                    p.next();
                    let x = p.bind_var(&name);
                    p.skip_newlines();
                    let body = p.expr()?;
                    Ok(term(pos, TermKind::Lam(x, None, Box::new(body))))
                });
            }
        }
        if self.is_sym("[") && self.lambda_ahead() {
            // `[A] => t`: a function of a type
            return self.scoped(|p| {
                let types = p.bind_type_params()?;
                p.expect_sym("=>")?;
                p.skip_newlines();
                let body = p.expr()?;
                Ok(types.into_iter().rev().fold(body, |acc, (x, t)| term(pos, TermKind::Lam(x, Some(t), Box::new(acc)))))
            });
        }
        if self.is_sym("(") && self.lambda_ahead() {
            return self.scoped(|p| {
                let params = p.maybe_typed_params(false)?;
                p.expect_sym("=>")?;
                p.skip_newlines();
                let body = p.expr()?;
                Ok(params.into_iter().rev().fold(body, |acc, (x, t)| term(pos, TermKind::Lam(x, t, Box::new(acc)))))
            });
        }
        if self.eat_keyword("if") {
            self.expect_sym("(")?;
            let c = self.expr()?;
            self.expect_sym(")")?;
            self.skip_newlines();
            let t = self.expr()?;
            self.skip_newlines();
            if !self.eat_keyword("else") {
                return Err(self.error("expected `else`"));
            }
            self.skip_newlines();
            let e = self.expr()?;
            return Ok(term(pos, TermKind::If(Box::new(c), Box::new(t), Box::new(e))));
        }
        if self.eat_keyword("while") {
            self.expect_sym("(")?;
            let c = self.expr()?;
            self.expect_sym(")")?;
            self.skip_newlines();
            let body = self.expr()?;
            return Ok(term(pos, TermKind::While(Box::new(c), Box::new(body))));
        }
        let lhs = self.binary(0)?;
        if self.is_sym("=") {
            let at = self.pos();
            self.next();
            self.skip_newlines();
            let value = Box::new(self.expr()?);
            return match lhs.kind {
                TermKind::Get(x) => Ok(term(at, TermKind::Set(x, value))),
                TermKind::Sel(recv, a) => Ok(term(at, TermKind::Assign(recv, a, value))),
                _ => Err(Error::at(at, "only a `var` or a field can be assigned to")),
            };
        }
        Ok(lhs)
    }

    fn binary(&mut self, min: usize) -> Result<Term> {
        const LEVELS: [&[(&str, Prim)]; 6] = [
            &[("||", Prim::Or)],
            &[("&&", Prim::And)],
            &[("==", Prim::Eq), ("!=", Prim::Ne)],
            &[("<", Prim::Lt), ("<=", Prim::Le), (">", Prim::Gt), (">=", Prim::Ge)],
            &[("+", Prim::Add), ("-", Prim::Sub)],
            &[("*", Prim::Mul), ("/", Prim::Div), ("%", Prim::Rem)],
        ];
        if min == LEVELS.len() {
            return self.unary();
        }
        let mut lhs = self.binary(min + 1)?;
        loop {
            let Some((_, prim)) = LEVELS[min].iter().find(|(s, _)| self.is_sym(s)) else { break };
            let pos = self.pos();
            self.next();
            self.skip_newlines();
            let rhs = self.binary(min + 1)?;
            lhs = term(pos, TermKind::Prim(prim.clone(), vec![lhs, rhs]));
        }
        Ok(lhs)
    }

    fn unary(&mut self) -> Result<Term> {
        let pos = self.pos();
        if self.eat_sym("-") {
            let t = self.unary()?;
            return Ok(term(pos, TermKind::Prim(Prim::Neg, vec![t])));
        }
        if self.eat_sym("!") {
            let t = self.unary()?;
            return Ok(term(pos, TermKind::Prim(Prim::Not, vec![t])));
        }
        self.postfix()
    }

    fn postfix(&mut self) -> Result<Term> {
        let mut t = self.primary()?;
        loop {
            let pos = self.pos();
            if self.eat_sym(".") {
                let a = self.ident()?;
                t = term(pos, TermKind::Sel(Box::new(t), a));
            } else if self.is_sym("(") {
                for arg in self.args()? {
                    t = term(pos, TermKind::App(Box::new(t), Box::new(arg)));
                }
            } else if self.eat_sym("[") {
                // type arguments
                loop {
                    let at = self.pos();
                    let ty = self.ty()?;
                    t = term(pos, TermKind::App(Box::new(t), Box::new(term(at, TermKind::TypeArg(ty)))));
                    if !self.eat_sym(",") {
                        break;
                    }
                }
                self.expect_sym("]")?;
            } else {
                return Ok(t);
            }
        }
    }

    /// `(a, b)`, with `()` passing `()`.
    fn args(&mut self) -> Result<Vec<Term>> {
        self.expect_sym("(")?;
        // (the `()` is at its `)`, so it's somewhere other than the call,
        // which is at the `(`)
        let pos = self.pos();
        if self.eat_sym(")") {
            return Ok(vec![term(pos, TermKind::Unit)]);
        }
        let mut args = vec![self.expr()?];
        while self.eat_sym(",") {
            args.push(self.expr()?);
        }
        self.expect_sym(")")?;
        Ok(args)
    }

    fn primary(&mut self) -> Result<Term> {
        let pos = self.pos();
        match self.peek().clone() {
            Tok::Int(n) => {
                self.next();
                Ok(term(pos, TermKind::Int(n)))
            }
            Tok::Str(s) => {
                self.next();
                Ok(term(pos, TermKind::Str(s)))
            }
            Tok::Sym("(") => {
                self.next();
                if self.eat_sym(")") {
                    return Ok(term(pos, TermKind::Unit));
                }
                let t = self.expr()?;
                if self.eat_sym(":") {
                    let ty = self.ty()?;
                    self.expect_sym(")")?;
                    return Ok(term(pos, TermKind::Ascribe(Box::new(t), ty)));
                }
                self.expect_sym(")")?;
                Ok(t)
            }
            Tok::Sym("{") => {
                self.next();
                let t = self.scoped(|p| p.statements(Some("}")))?;
                self.expect_sym("}")?;
                Ok(t)
            }
            Tok::Ident(k) => match k.as_str() {
                "true" | "false" => {
                    self.next();
                    Ok(term(pos, TermKind::Bool(k == "true")))
                }
                "new" => {
                    self.next();
                    self.object(pos)
                }
                "print" | "println" | "printc" | "read" | "readc" | "readLine" | "error" => {
                    self.next();
                    self.builtin(&k, pos)
                }
                _ => {
                    let name = self.ident()?;
                    match self.lookup(&name, false) {
                        Some(Binding::Term(p)) => Ok(path_term(&p, pos)),
                        Some(Binding::Mutable(x)) => Ok(term(pos, TermKind::Get(x))),
                        _ => Err(Error::at(pos, &format!("`{name}` isn't defined"))),
                    }
                }
            },
            _ => Err(self.error("expected an expression")),
        }
    }

    fn builtin(&mut self, name: &str, pos: usize) -> Result<Term> {
        let prim = |prim, args| Ok(term(pos, TermKind::Prim(prim, args)));
        self.expect_sym("(")?;
        // printing a literal doesn't need to build a string
        if let (Tok::Str(s), Tok::Sym(")")) = (self.peek().clone(), self.peek_at(1).clone()) {
            if name == "print" || name == "println" {
                self.next();
                self.expect_sym(")")?;
                let s = if name == "println" { s + "\n" } else { s };
                return prim(Prim::Puts(s), vec![]);
            }
        }
        if self.eat_sym(")") {
            return match name {
                "read" => prim(Prim::Read, vec![]),
                "readc" => prim(Prim::ReadChar, vec![]),
                "readLine" => prim(Prim::ReadLine, vec![]),
                "println" => prim(Prim::Puts("\n".to_string()), vec![]),
                _ => Err(Error::at(pos, &format!("`{name}` needs an argument"))),
            };
        }
        let arg = self.expr()?;
        self.expect_sym(")")?;
        match name {
            "print" => prim(Prim::Print, vec![arg]),
            "println" => prim(Prim::PrintLn, vec![arg]),
            "printc" => prim(Prim::PrintChar, vec![arg]),
            "error" => prim(Prim::Error, vec![arg]),
            _ => Err(Error::at(pos, &format!("`{name}` doesn't take an argument"))),
        }
    }

    /// After `new`: `{ self: T => members }`, or `F[X] { members }`, an
    /// object of type `F[X]`.
    fn object(&mut self, pos: usize) -> Result<Term> {
        // a template: its parameters become type members
        let mut template: Option<(Type, Vec<Def>)> = None;
        if !self.is_sym("{") {
            let at = self.pos();
            let (ty, args) = self.applied_type()?;
            let defs = args.into_iter().map(|(name, t)| Def { name, kind: DefKind::Type(t), pos: at }).collect();
            template = Some((ty, defs));
            if !self.is_sym("{") {
                let z = self.names.fresh("this");
                let (ty, defs) = template.unwrap();
                return Ok(term(pos, TermKind::New(z, Some(ty), defs)));
            }
        }
        self.expect_sym("{")?;
        self.skip_newlines();
        let self_name = match (self.peek().clone(), self.peek_at(1).clone()) {
            (Tok::Ident(s), Tok::Sym("=>")) | (Tok::Ident(s), Tok::Sym(":")) if !KEYWORDS.contains(&s.as_str()) => Some(s),
            _ => None,
        };
        self.scoped(|p| {
            let z = match &self_name {
                Some(s) => {
                    p.next();
                    p.bind_var(s)
                }
                None => p.names.fresh("this"),
            };
            let mut annotation = if self_name.is_some() && p.eat_sym(":") { Some(p.and_ty()?) } else { None };
            if self_name.is_some() {
                p.expect_sym("=>")?;
            }
            let (mut defs, members) = p.members(&Path::Var(z), Some("}"))?;
            p.expect_sym("}")?;
            if let Some((ty, type_defs)) = template {
                for d in type_defs {
                    if !defs.iter().any(|e| e.name == d.name) {
                        defs.insert(0, d);
                    }
                }
                annotation = Some(match annotation {
                    Some(a) => Type::And(Box::new(a), Box::new(ty)),
                    None => ty,
                });
            }
            p.roots.insert(z, members);
            Ok(term(pos, TermKind::New(z, annotation, defs)))
        })
    }

    pub fn ty(&mut self) -> Result<Type> {
        if self.is_sym("(") && self.lambda_ahead() {
            // `(x: S, y: T) => U`, whose result can mention the parameters
            if matches!(self.peek_at(1), Tok::Ident(_)) && matches!(self.peek_at(2), Tok::Sym(":")) {
                return self.scoped(|p| {
                    let params = p.params()?;
                    p.expect_sym("=>")?;
                    let result = p.ty()?;
                    Ok(params.into_iter().rev().fold(result, |acc, (x, t)| Type::Fun(x, Box::new(t), Box::new(acc))))
                });
            }
            // `(S, T) => U`, the same as `S => T => U`; `() => U` takes Unit
            self.expect_sym("(")?;
            let mut params = vec![];
            if !self.eat_sym(")") {
                loop {
                    params.push(self.ty()?);
                    if !self.eat_sym(",") {
                        break;
                    }
                }
                self.expect_sym(")")?;
            } else {
                params.push(Type::Unit);
            }
            self.expect_sym("=>")?;
            let result = self.ty()?;
            return Ok(params.into_iter().rev().fold(result, |acc, t| Type::Fun(self.names.fresh("_"), Box::new(t), Box::new(acc))));
        }
        if self.is_sym("[") && self.lambda_ahead() {
            // `[A <: U] => T`: what a function of a type is
            return self.scoped(|p| {
                let types = p.bind_type_params()?;
                p.expect_sym("=>")?;
                let result = p.ty()?;
                Ok(types.into_iter().rev().fold(result, |acc, (x, t)| Type::Fun(x, Box::new(t), Box::new(acc))))
            });
        }
        let t = self.and_ty()?;
        if self.eat_sym("=>") {
            let x = self.names.fresh("_");
            let result = self.ty()?;
            return Ok(Type::Fun(x, Box::new(t), Box::new(result)));
        }
        Ok(t)
    }

    fn and_ty(&mut self) -> Result<Type> {
        let mut t = self.refined_ty()?;
        while self.eat_sym("&") {
            let u = self.refined_ty()?;
            t = Type::And(Box::new(t), Box::new(u));
        }
        Ok(t)
    }

    /// A type, then any refinements: `T { decls }` is `T & { decls }`.
    fn refined_ty(&mut self) -> Result<Type> {
        let mut t = self.atom_ty()?;
        while self.is_sym("{") {
            let r = self.record_ty()?;
            t = Type::And(Box::new(t), Box::new(r));
        }
        Ok(t)
    }

    /// A type that a `{` doesn't refine, as a module's signature is.
    fn type_without_refinements(&mut self) -> Result<Type> {
        let mut t = self.atom_ty()?;
        while self.eat_sym("&") {
            let u = self.atom_ty()?;
            t = Type::And(Box::new(t), Box::new(u));
        }
        Ok(t)
    }

    fn atom_ty(&mut self) -> Result<Type> {
        if self.eat_sym("(") {
            let t = self.ty()?;
            self.expect_sym(")")?;
            return Ok(t);
        }
        if self.is_sym("{") {
            return self.record_ty();
        }
        Ok(self.applied_type()?.0)
    }

    /// A named type, applied to its arguments if it's given any: the type,
    /// and the type members the arguments fix.
    fn applied_type(&mut self) -> Result<(Type, Vec<(String, Type)>)> {
        let pos = self.pos();
        let first = self.ident()?;
        match first.as_str() {
            "Top" => return Ok((Type::Top, vec![])),
            "Bot" => return Ok((Type::Bot, vec![])),
            "Int" => return Ok((Type::Int, vec![])),
            "Bool" => return Ok((Type::Bool, vec![])),
            "Unit" => return Ok((Type::Unit, vec![])),
            "String" => return Ok((Type::Str, vec![])),
            _ => {}
        }
        let (base, params, name) = if !self.is_sym(".") {
            match self.lookup(&first, true) {
                Some(Binding::Type(t, params)) => (t, params, first),
                _ => return Err(Error::at(pos, &format!("there's no type called `{first}` here"))),
            }
        } else {
            // a path, then a type member's name
            let mut path = match self.lookup(&first, false) {
                Some(Binding::Term(p)) => p,
                Some(Binding::Mutable(_)) => return Err(Error::at(pos, &format!("`{first}` is a var, so types can't depend on it"))),
                _ => return Err(Error::at(pos, &format!("`{first}` isn't defined"))),
            };
            self.expect_sym(".")?;
            let mut last = self.ident()?;
            while self.eat_sym(".") {
                path = path.sel(&last);
                last = self.ident()?;
            }
            let params = self.members_of(&path).and_then(|m| {
                m.get(&last).find_map(|m| match m {
                    Member::Type(p) => p.clone(),
                    _ => None,
                })
            });
            (Type::Select(path, last.clone()), params, last)
        };
        if !self.is_sym("[") {
            return Ok((base, vec![]));
        }
        self.expect_sym("[")?;
        let mut args = vec![];
        loop {
            args.push(self.ty()?);
            if !self.eat_sym(",") {
                break;
            }
        }
        self.expect_sym("]")?;
        // a type whose parameters aren't known here (a member of a value
        // that isn't a known object): the checker finds them
        let Some(params) = params else {
            if matches!(&base, Type::Select(p, _) if self.members_of(p).is_none()) {
                return Ok((Type::Applied(Box::new(base), args), vec![]));
            }
            return Err(Error::at(pos, &format!("`{name}` doesn't take type parameters")));
        };
        if args.len() != params.len() {
            return Err(Error::at(pos, &format!("`{name}` takes {} type parameters, not {}", params.len(), args.len())));
        }
        let mut t = base;
        let mut fixed = vec![];
        for (param, arg) in params.iter().zip(args) {
            let (l, u) = match param.variance {
                Variance::Co => (Type::Bot, arg.clone()),
                Variance::Contra => (arg.clone(), Type::Top),
                Variance::In => (arg.clone(), arg.clone()),
            };
            t = Type::And(Box::new(t), Box::new(Type::Member(param.name.clone(), Box::new(l), Box::new(u))));
            fixed.push((param.name.clone(), arg));
        }
        Ok((t, fixed))
    }

    /// `{ self => declarations }`
    fn record_ty(&mut self) -> Result<Type> {
        self.expect_sym("{")?;
        self.skip_newlines();
        let self_name = match (self.peek().clone(), self.peek_at(1).clone()) {
            (Tok::Ident(s), Tok::Sym("=>")) if !KEYWORDS.contains(&s.as_str()) => Some(s),
            _ => None,
        };
        self.scoped(|p| {
            let z = match &self_name {
                Some(s) => {
                    p.next();
                    p.next();
                    p.bind_var(s)
                }
                None => p.names.fresh("this"),
            };
            let ahead = p.ahead(&["val", "var", "def", "type"]);
            p.bind_members(&Path::Var(z), &ahead);
            let mut decls = vec![];
            loop {
                p.skip_separators();
                if p.eat_sym("}") {
                    break;
                }
                decls.push(p.decl()?);
                if !matches!(p.peek(), Tok::Newline | Tok::Sym(";") | Tok::Sym("}")) {
                    return Err(p.error("expected a new line or `;` after the declaration"));
                }
            }
            let body = Type::and(decls);
            Ok(if body.mentions(z) { Type::Rec(z, Box::new(body)) } else { body })
        })
    }

    fn decl(&mut self) -> Result<Type> {
        if self.eat_keyword("type") {
            let name = self.ident()?;
            let params = if self.is_sym("[") { Some(self.type_params()?) } else { None };
            if self.eat_sym("=") {
                let t = self.with_type_params(params.as_deref(), |p| p.ty())?;
                return Ok(Type::Member(name, Box::new(t.clone()), Box::new(t)));
            }
            let lower = if self.eat_sym(">:") { self.ty()? } else { Type::Bot };
            let upper = if self.eat_sym("<:") { self.ty()? } else { Type::Top };
            // an abstract type that takes parameters has them as members
            let upper = match &params {
                Some(params) => {
                    let note = Type::Params(params.iter().map(|(p, ..)| (p.name.clone(), p.variance)).collect());
                    let members: Vec<Type> = std::iter::once(note)
                        .chain(params.iter().map(|(p, l, u)| Type::Member(p.name.clone(), Box::new(l.clone()), Box::new(u.clone()))))
                        .collect();
                    Type::And(Box::new(Type::and(members)), Box::new(upper))
                }
                None => upper,
            };
            return Ok(Type::Member(name, Box::new(lower), Box::new(upper)));
        }
        if self.is_keyword("val") || self.is_keyword("var") {
            let mutable = self.next() == Tok::Ident("var".to_string());
            let name = self.ident()?;
            self.expect_sym(":")?;
            let t = Box::new(self.ty()?);
            return Ok(if mutable { Type::VarField(name, t) } else { Type::Field(name, t) });
        }
        if self.eat_keyword("def") {
            let name = self.ident()?;
            let t = self.scoped(|p| {
                let types = if p.is_sym("[") { p.bind_type_params()? } else { vec![] };
                let params = if p.is_sym("(") { p.params()? } else { vec![] };
                p.expect_sym(":")?;
                let result = p.ty()?;
                Ok(types.into_iter().chain(params).rev().fold(result, |acc, (x, t)| Type::Fun(x, Box::new(t), Box::new(acc))))
            })?;
            return Ok(Type::Field(name, Box::new(t)));
        }
        Err(self.error("expected `val`, `var`, `def` or `type`"))
    }
}

/// The parameters of `type F[...]`, from the tokens starting at its `[`,
/// without parsing their bounds.
fn params_at(toks: &[Token], mut i: usize) -> Vec<Param> {
    let mut params = vec![];
    let mut depth = 0;
    let mut expecting = true;
    loop {
        match &toks[i].tok {
            Tok::Sym("[") => {
                depth += 1;
                if depth == 1 {
                    expecting = true;
                }
            }
            Tok::Sym("]") => {
                depth -= 1;
                if depth == 0 {
                    return params;
                }
            }
            Tok::Sym(",") if depth == 1 => expecting = true,
            Tok::Sym(s @ ("+" | "-")) if depth == 1 && expecting => {
                if let Tok::Ident(name) = &toks[i + 1].tok {
                    let variance = if *s == "+" { Variance::Co } else { Variance::Contra };
                    params.push(Param { name: name.clone(), variance });
                    expecting = false;
                    i += 1;
                }
            }
            Tok::Ident(name) if depth == 1 && expecting => {
                params.push(Param { name: name.clone(), variance: Variance::In });
                expecting = false;
            }
            Tok::Eof => return params,
            _ => {}
        }
        i += 1;
    }
}

/// The term that reads a path.
fn path_term(p: &Path, pos: usize) -> Term {
    match p {
        Path::Var(x) => term(pos, TermKind::Var(*x)),
        Path::Sel(q, a) => term(pos, TermKind::Sel(Box::new(path_term(q, pos)), a.clone())),
    }
}

/// A symbol as the `'static` string the lexer uses.
fn leak(s: &str) -> &'static str {
    SYMBOLS.iter().find(|t| **t == s).copied().unwrap_or("")
}
