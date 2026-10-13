//! The type checker: DOT's typing and subtyping rules, made algorithmic.
//!
//! Types of terms are inferred bottom up, and checked against annotations by
//! subtyping; where a type is expected, a lambda is checked against it, so
//! its parameters can leave out their types. Paths are what make types
//! dependent: the type of a path is its declared type with recursive types
//! unfolded at the path, so `p.A` can be looked up as the bounds `p`'s type
//! gives its member `A`.
//!
//! Where a type would mention a variable going out of scope (a `let`'s
//! variable, or the fresh variable an argument or receiver that isn't a path
//! is given), the variable is avoided: `x.A` is replaced by its upper bounds
//! where the type is covariant, and by a lower bound where it's
//! contravariant. Where two types meet, as the branches of an `if` do, the
//! result is their join: the least type both are subtypes of that the
//! checker can find, field by field and member by member, or `Top`.
//!
//! The members of an object without declared types are inferred, together,
//! starting from `Bot` and joining in what each round finds until nothing
//! changes, so recursive functions don't need their result types written.
//! An object's values are computed in order, so a value can't use a member
//! that comes after it, even through a function it calls, and only `def`s
//! can use the object itself.
//!
//! Subtyping in DOT is undecidable, so the checker has a budget, and gives up
//! on programs that need more.

use super::syntax::*;
use super::Error;
use std::collections::{HashMap, HashSet};

/// How many steps of subtyping and lookups a program can take to check.
const FUEL: usize = 4_000_000;
/// How deep lookups and subtyping can nest.
const DEPTH: usize = 48;
/// How many times avoidance follows a bound to one that still mentions the
/// variable, before it settles for `Top` or `Bot`; and how deep joins go.
const AVOID_DEPTH: usize = 8;
/// How many rounds inferring the types of an object's members can take.
const ROUNDS: usize = 12;

type Result<T> = std::result::Result<T, Error>;

/// What code generation needs to know about a term that its types decide,
/// kept by the term's position.
#[derive(Clone, Copy, Debug, PartialEq)]
pub enum Note {
    /// `print` or `println` of a `Bool`, or of a `String`.
    PrintBool,
    PrintStr,
    /// `==` or `!=` on strings, which compares what they say.
    StrEq,
    /// `+` with a string on either side: what each side is.
    Concat(Kind, Kind),
    /// A member of a string: `length`, `charAt` or `substring`.
    StrMember,
}

/// The kinds of value that `+`, `==` and `print` treat differently.
#[derive(Clone, Copy, Debug, PartialEq)]
pub enum Kind {
    Int,
    Bool,
    Str,
}

pub struct Typer<'a> {
    names: &'a mut Names,
    env: HashMap<Var, Type>,
    /// The `var`s in scope, which aren't paths.
    mutables: HashMap<Var, Type>,
    fuel: usize,
    pub notes: HashMap<usize, Note>,
    /// For arguments the checker passes a type argument before, which it
    /// worked out: how many, by the argument's position.
    pub implicit: HashMap<usize, usize>,
    /// Arguments' types, found while working out type arguments, by
    /// position, so they're only found once.
    known: HashMap<usize, Type>,
}

/// `t` with its recursive types unfolded at the path `p`, which has type `t`.
fn unfold(t: &Type, p: &Path) -> Type {
    match t {
        Type::Rec(z, body) => unfold(&body.subst(*z, p), p),
        Type::And(a, b) => Type::And(Box::new(unfold(a, p)), Box::new(unfold(b, p))),
        t => t.clone(),
    }
}

/// The parts of an intersection.
fn components<'t>(t: &'t Type, out: &mut Vec<&'t Type>) {
    match t {
        Type::And(a, b) => {
            components(a, out);
            components(b, out);
        }
        t => out.push(t),
    }
}

/// The path a term is, if it's one.
fn term_path(t: &Term) -> Option<Path> {
    match &t.kind {
        TermKind::Var(x) => Some(Path::Var(*x)),
        TermKind::Sel(r, a) => term_path(r).map(|p| p.sel(a)),
        _ => None,
    }
}

/// The members of `z` that `t` selects, anywhere in it, and whether it uses
/// `z` other than to select a member.
fn uses_of(t: &Term, z: Var, out: &mut HashSet<String>, bare: &mut bool) {
    match &t.kind {
        TermKind::Sel(r, a) if matches!(r.kind, TermKind::Var(y) if y == z) => {
            out.insert(a.clone());
            return;
        }
        TermKind::Var(y) if *y == z => {
            *bare = true;
            return;
        }
        // assigning a field of the object uses it
        TermKind::Assign(r, a, v) if matches!(r.kind, TermKind::Var(y) if y == z) => {
            out.insert(a.clone());
            uses_of(v, z, out, bare);
            return;
        }
        _ => {}
    }
    let mut go = |t: &Term| uses_of(t, z, out, bare);
    match &t.kind {
        TermKind::Sel(r, _) => go(r),
        TermKind::Lam(_, _, b) | TermKind::Ascribe(b, _) | TermKind::Set(_, b) => go(b),
        TermKind::App(a, b) | TermKind::Let(_, _, a, b) | TermKind::LetVar(_, _, a, b) | TermKind::While(a, b) => {
            go(a);
            go(b);
        }
        TermKind::Assign(r, _, v) => {
            go(r);
            go(v);
        }
        TermKind::If(a, b, c) => {
            go(a);
            go(b);
            go(c);
        }
        TermKind::Prim(_, args) => args.iter().for_each(go),
        TermKind::New(_, _, defs) => {
            for d in defs {
                if let DefKind::Val(_, t) | DefKind::Var(_, t) = &d.kind {
                    go(t);
                }
            }
        }
        TermKind::Var(_)
        | TermKind::Int(_)
        | TermKind::Bool(_)
        | TermKind::Unit
        | TermKind::Str(_)
        | TermKind::TypeArg(_)
        | TermKind::Get(_)
        | TermKind::Foreign(..) => {}
    }
}

fn is_lambda(t: &Term) -> bool {
    match &t.kind {
        TermKind::Lam(..) => true,
        TermKind::Ascribe(t, _) => is_lambda(t),
        _ => false,
    }
}

impl<'a> Typer<'a> {
    pub fn new(names: &'a mut Names) -> Self {
        Typer {
            names,
            env: HashMap::new(),
            mutables: HashMap::new(),
            fuel: FUEL,
            notes: HashMap::new(),
            implicit: HashMap::new(),
            known: HashMap::new(),
        }
    }

    fn tick(&mut self) -> bool {
        if self.fuel == 0 {
            return false;
        }
        self.fuel -= 1;
        true
    }

    fn show(&self, t: &Type) -> String {
        self.names.show(t)
    }

    fn error(&self, pos: usize, msg: String) -> Error {
        if self.fuel == 0 {
            Error::at(pos, "type checking ran out of fuel: the types here are too complicated")
        } else {
            Error::at(pos, &msg)
        }
    }

    fn fresh_like(&mut self, x: Var) -> Var {
        let name = self.names.name(x).to_string();
        self.names.fresh(&name)
    }

    /// Runs `f` with `x: t` in scope.
    fn with<T>(&mut self, x: Var, t: Type, f: impl FnOnce(&mut Self) -> T) -> T {
        let old = self.env.insert(x, t);
        let r = f(self);
        match old {
            Some(old) => self.env.insert(x, old),
            None => self.env.remove(&x),
        };
        r
    }

    /// The type of a path, unfolded at it.
    fn path_type(&mut self, p: &Path) -> Option<Type> {
        match p {
            Path::Var(x) => self.env.get(x).cloned().map(|t| unfold(&t, p)),
            Path::Sel(q, a) => {
                let t = self.path_type(q)?;
                let f = self.field_of(&t, a, q, 0)?;
                Some(unfold(&f, p))
            }
        }
    }

    /// The members strings have.
    fn string_member(&mut self, a: &str) -> Option<Type> {
        let fun = |x: Var, a: Type, b: Type| Type::Fun(x, Box::new(a), Box::new(b));
        match a {
            "length" => Some(Type::Int),
            "charAt" => Some(fun(self.names.fresh("i"), Type::Int, Type::Int)),
            "substring" => {
                let (i, j) = (self.names.fresh("from"), self.names.fresh("to"));
                Some(fun(i, Type::Int, fun(j, Type::Int, Type::Str)))
            }
            _ => None,
        }
    }

    /// The type of field `a` of a value at `at` of type `t`.
    fn field_of(&mut self, t: &Type, a: &str, at: &Path, depth: usize) -> Option<Type> {
        if depth > DEPTH || !self.tick() {
            return None;
        }
        match t {
            Type::Field(b, u) | Type::VarField(b, u) if b == a => Some((**u).clone()),
            Type::And(l, r) => match (self.field_of(l, a, at, depth + 1), self.field_of(r, a, at, depth + 1)) {
                (Some(x), Some(y)) if x == y => Some(x),
                (Some(x), Some(y)) => Some(Type::And(Box::new(x), Box::new(y))),
                (x, y) => x.or(y),
            },
            Type::Rec(z, body) => self.field_of(&body.subst(*z, at), a, at, depth + 1),
            Type::Select(p, m) => {
                for (_, upper) in self.bounds(p, m, depth + 1) {
                    if let Some(f) = self.field_of(&upper, a, at, depth + 1) {
                        return Some(f);
                    }
                }
                None
            }
            Type::Str => self.string_member(a),
            Type::Bot => Some(Type::Bot),
            _ => None,
        }
    }

    /// The bounds of `p.m`: one pair for each declaration of `m` that `p`'s
    /// type has.
    fn bounds(&mut self, p: &Path, m: &str, depth: usize) -> Vec<(Type, Type)> {
        let Some(t) = self.path_type(p) else { return vec![] };
        let mut out = vec![];
        self.collect_bounds(&t, m, p, depth, &mut out);
        out
    }

    fn collect_bounds(&mut self, t: &Type, m: &str, at: &Path, depth: usize, out: &mut Vec<(Type, Type)>) {
        if depth > DEPTH || !self.tick() {
            return;
        }
        match t {
            Type::Member(n, l, u) if n == m => out.push(((**l).clone(), (**u).clone())),
            Type::And(a, b) => {
                self.collect_bounds(a, m, at, depth + 1, out);
                self.collect_bounds(b, m, at, depth + 1, out);
            }
            Type::Rec(z, body) => self.collect_bounds(&body.subst(*z, at), m, at, depth + 1, out),
            Type::Select(q, n) => {
                for (_, upper) in self.bounds(q, n, depth + 1) {
                    self.collect_bounds(&upper, m, at, depth + 1, out);
                }
            }
            Type::Bot => out.push((Type::Top, Type::Bot)),
            _ => {}
        }
    }

    /// `p.m`'s upper bound: all of its upper bounds at once.
    fn upper(&mut self, p: &Path, m: &str) -> Option<Type> {
        let uppers: Vec<Type> = self.bounds(p, m, 0).into_iter().map(|(_, u)| u).collect();
        if uppers.is_empty() { None } else { Some(Type::and(uppers)) }
    }

    /// The function type a value at `at` of type `t` has.
    fn fun_of(&mut self, t: &Type, at: &Path, depth: usize) -> Option<(Var, Type, Type)> {
        if depth > DEPTH || !self.tick() {
            return None;
        }
        match t {
            Type::Fun(x, s, r) => Some((*x, (**s).clone(), (**r).clone())),
            Type::And(a, b) => self.fun_of(a, at, depth + 1).or_else(|| self.fun_of(b, at, depth + 1)),
            Type::Rec(z, body) => self.fun_of(&body.subst(*z, at), at, depth + 1),
            Type::Select(p, m) => {
                for (_, upper) in self.bounds(p, m, depth + 1) {
                    if let Some(f) = self.fun_of(&upper, at, depth + 1) {
                        return Some(f);
                    }
                }
                None
            }
            Type::Bot => Some((self.names.fresh("_"), Type::Top, Type::Bot)),
            _ => None,
        }
    }

    /// Whether `s` is a subtype of `t`.
    pub fn sub(&mut self, s: &Type, t: &Type) -> bool {
        self.subtype(s, t, 0)
    }

    fn subtype(&mut self, s: &Type, t: &Type, depth: usize) -> bool {
        if depth > DEPTH || !self.tick() {
            return false;
        }
        if s == t || matches!(t, Type::Top | Type::Params(_)) || matches!(s, Type::Bot) {
            return true;
        }
        let d = depth + 1;
        if let Type::And(a, b) = t {
            return self.subtype(s, a, d) && self.subtype(s, b, d);
        }
        // a type that's exactly a bound of the other side (before either is
        // unfolded, so that two unfoldings of one recursive type aren't
        // compared as if they described different values)
        if let Type::Select(p, m) = t {
            if self.bounds(p, m, d).iter().any(|(l, _)| l == s) {
                return true;
            }
        }
        if let Type::Select(p, m) = s {
            if self.bounds(p, m, d).iter().any(|(_, u)| u == t) {
                return true;
            }
        }
        // a recursive type on either side: name the value
        if let Type::Rec(z, body) = s {
            let y = self.fresh_like(*z);
            let body = body.subst(*z, &Path::Var(y));
            // a recursive type on the right, maybe behind an alias, is about
            // the same value
            let mut targets = vec![];
            match t {
                Type::Rec(w, c) => targets.push(c.subst(*w, &Path::Var(y))),
                Type::Select(p, m) => {
                    for (lower, _) in self.bounds(p, m, d) {
                        if let Type::Rec(w, c) = lower {
                            targets.push(c.subst(w, &Path::Var(y)));
                        }
                    }
                    targets.push(t.clone());
                }
                t => targets.push(t.clone()),
            }
            return self.with(y, s.clone(), |me| targets.iter().any(|t| me.subtype(&body, t, d)));
        }
        if let Type::Rec(w, c) = t {
            let y = self.fresh_like(*w);
            let c = c.subst(*w, &Path::Var(y));
            return self.with(y, s.clone(), |me| me.subtype(s, &c, d));
        }
        match (s, t) {
            (Type::Field(a, x) | Type::VarField(a, x), Type::Field(b, y)) if a == b => return self.subtype(x, y, d),
            // a var field can be written as well as read, so its type can't
            // change
            (Type::VarField(a, x), Type::VarField(b, y)) if a == b => return self.subtype(x, y, d) && self.subtype(y, x, d),
            (Type::Member(a, l1, u1), Type::Member(b, l2, u2)) if a == b => {
                return self.subtype(l2, l1, d) && self.subtype(u1, u2, d);
            }
            (Type::Fun(x, s1, r1), Type::Fun(y, s2, r2)) => {
                if !self.subtype(s2, s1, d) {
                    return false;
                }
                let z = self.fresh_like(*y);
                let (r1, r2) = (r1.subst(*x, &Path::Var(z)), r2.subst(*y, &Path::Var(z)));
                return self.with(z, (**s2).clone(), |me| me.subtype(&r1, &r2, d));
            }
            _ => {}
        }
        if let Type::And(a, b) = s {
            if self.subtype(a, t, d) || self.subtype(b, t, d) {
                return true;
            }
            // a field or member declared in several parts has all of their
            // types at once
            let mut parts = vec![];
            components(s, &mut parts);
            match t {
                Type::Field(name, want) => {
                    let found: Vec<Type> = parts
                        .iter()
                        .filter_map(|p| match p {
                            Type::Field(n, u) | Type::VarField(n, u) if n == name => Some((**u).clone()),
                            _ => None,
                        })
                        .collect();
                    if found.len() > 1 && self.subtype(&Type::and(found), want, d) {
                        return true;
                    }
                }
                Type::Member(name, lower, upper) => {
                    let (lowers, uppers): (Vec<Type>, Vec<Type>) = parts
                        .iter()
                        .filter_map(|p| match p {
                            Type::Member(n, l, u) if n == name => Some(((**l).clone(), (**u).clone())),
                            _ => None,
                        })
                        .unzip();
                    if uppers.len() > 1
                        && lowers.iter().any(|l| self.subtype(lower, l, d))
                        && self.subtype(&Type::and(uppers), upper, d)
                    {
                        return true;
                    }
                }
                _ => {}
            }
        }
        if let Type::Select(p, m) = s {
            for (_, upper) in self.bounds(p, m, d) {
                if self.subtype(&upper, t, d) {
                    return true;
                }
            }
        }
        if let Type::Select(p, m) = t {
            for (lower, _) in self.bounds(p, m, d) {
                if self.subtype(s, &lower, d) {
                    return true;
                }
            }
        }
        false
    }

    /// The least type that both `a` and `b` are subtypes of, as far as the
    /// checker can tell.
    pub fn join(&mut self, a: &Type, b: &Type) -> Type {
        self.join_at(a, b, 0)
    }

    fn join_at(&mut self, a: &Type, b: &Type, depth: usize) -> Type {
        if self.sub(a, b) {
            return b.clone();
        }
        if self.sub(b, a) {
            return a.clone();
        }
        if depth > AVOID_DEPTH {
            return Type::Top;
        }
        let d = depth + 1;
        match (a, b) {
            (Type::Select(p, m), _) => match self.upper(p, m) {
                Some(u) => self.join_at(&u, b, d),
                None => Type::Top,
            },
            (_, Type::Select(p, m)) => match self.upper(p, m) {
                Some(u) => self.join_at(a, &u, d),
                None => Type::Top,
            },
            (Type::Fun(x, s1, r1), Type::Fun(y, s2, r2)) => {
                let z = self.fresh_like(*x);
                let s = if s1 == s2 { (**s1).clone() } else { Type::And(s1.clone(), s2.clone()) };
                let (r1, r2) = (r1.subst(*x, &Path::Var(z)), r2.subst(*y, &Path::Var(z)));
                let r = self.with(z, s.clone(), |me| me.join_at(&r1, &r2, d));
                Type::Fun(z, Box::new(s), Box::new(r))
            }
            _ if is_record(a) && is_record(b) => self.join_records(a, b, d),
            _ => Type::Top,
        }
    }

    /// The join of two record types: what they have in common.
    fn join_records(&mut self, a: &Type, b: &Type, depth: usize) -> Type {
        let w = self.names.fresh("this");
        let open = |t: &Type| match t {
            Type::Rec(z, body) => body.subst(*z, &Path::Var(w)),
            t => t.clone(),
        };
        let (a, b) = (open(a), open(b));
        let both = Type::And(Box::new(a.clone()), Box::new(b.clone()));
        let body = self.with(w, both, |me| {
            let (mut pa, mut pb) = (vec![], vec![]);
            components(&a, &mut pa);
            components(&b, &mut pb);
            let mut out: Vec<Type> = vec![];
            let mut done: HashSet<String> = HashSet::new();
            for p in &pa {
                match p {
                    Type::Field(name, ta) | Type::VarField(name, ta) => {
                        let tb: Vec<(Type, bool)> = pb
                            .iter()
                            .filter_map(|q| match q {
                                Type::Field(n, u) if n == name => Some(((**u).clone(), false)),
                                Type::VarField(n, u) if n == name => Some(((**u).clone(), true)),
                                _ => None,
                            })
                            .collect();
                        if !tb.is_empty() && done.insert(format!("val {name}")) {
                            let both_var = matches!(p, Type::VarField(..)) && tb.iter().all(|(_, v)| *v);
                            let tb = Type::and(tb.into_iter().map(|(t, _)| t).collect());
                            // both var fields of the same type stay one;
                            // otherwise all that's left is reading
                            if both_var && me.sub(ta, &tb) && me.sub(&tb, ta) {
                                out.push(Type::VarField(name.clone(), ta.clone()));
                            } else {
                                let j = me.join_at(ta, &tb, depth);
                                out.push(Type::Field(name.clone(), Box::new(j)));
                            }
                        }
                    }
                    Type::Member(name, la, ua) => {
                        let other = pb.iter().find_map(|q| match q {
                            Type::Member(n, l, u) if n == name => Some(((**l).clone(), (**u).clone())),
                            _ => None,
                        });
                        if let Some((lb, ub)) = other {
                            if done.insert(format!("type {name}")) {
                                let lower = if **la == lb { lb } else { Type::And(la.clone(), Box::new(lb)) };
                                let upper = me.join_at(ua, &ub, depth);
                                out.push(Type::Member(name.clone(), Box::new(lower), Box::new(upper)));
                            }
                        }
                    }
                    // a part both have, like a type member they both are
                    p if pb.contains(p) && !out.contains(p) => out.push((*p).clone()),
                    _ => {}
                }
            }
            Type::and(out)
        });
        if body.mentions(w) { Type::Rec(w, Box::new(body)) } else { body }
    }

    /// `t` without `x`, made a supertype of `t` if `covariant`, else a
    /// subtype.
    fn avoid(&mut self, t: &Type, x: Var, covariant: bool, depth: usize) -> Type {
        if !t.mentions(x) {
            return t.clone();
        }
        let extreme = if covariant { Type::Top } else { Type::Bot };
        if depth > AVOID_DEPTH {
            return extreme;
        }
        let go = |me: &mut Self, t: &Type, cov: bool| Box::new(me.avoid(t, x, cov, depth));
        match t {
            Type::Select(p, m) => {
                let bounds = self.bounds(p, m, 0);
                let bound = if covariant {
                    let uppers: Vec<Type> = bounds.into_iter().map(|(_, u)| u).collect();
                    if uppers.is_empty() { None } else { Some(Type::and(uppers)) }
                } else {
                    bounds.into_iter().next().map(|(l, _)| l)
                };
                match bound {
                    Some(b) => self.avoid(&b, x, covariant, depth + 1),
                    None => extreme,
                }
            }
            Type::Field(a, u) => Type::Field(a.clone(), go(self, u, covariant)),
            // a var field whose type changes can only be read
            Type::VarField(a, u) => Type::Field(a.clone(), go(self, u, covariant)),
            Type::Member(a, l, u) => {
                let l = go(self, l, !covariant);
                Type::Member(a.clone(), l, go(self, u, covariant))
            }
            Type::And(a, b) => {
                let a = go(self, a, covariant);
                Type::And(a, go(self, b, covariant))
            }
            Type::Fun(y, s, r) => {
                let s = go(self, s, !covariant);
                let r = self.with(*y, (*s).clone(), |me| go(me, r, covariant));
                Type::Fun(*y, s, r)
            }
            Type::Rec(z, body) => {
                let body = self.with(*z, t.clone(), |me| go(me, body, covariant));
                Type::Rec(*z, body)
            }
            t => t.clone(),
        }
    }

    /// Checks that every `p.A` in `t` names a type member of a path in
    /// scope.
    fn well_formed(&mut self, t: &Type, pos: usize) -> Result<()> {
        match t {
            Type::Select(p, m) => {
                if self.path_type(p).is_none() {
                    return Err(self.error(pos, format!("`{}` has no type here", self.names.path(p))));
                }
                if !self.stable(p) {
                    return Err(self.error(
                        pos,
                        format!("types can't depend on `{}`: it goes through a var, which can change", self.names.path(p)),
                    ));
                }
                if self.bounds(p, m, 0).is_empty() {
                    return Err(self.error(pos, format!("`{}` has no type member `{m}`", self.names.path(p))));
                }
                Ok(())
            }
            Type::Field(_, u) | Type::VarField(_, u) => self.well_formed(u, pos),
            Type::Member(_, l, u) | Type::And(l, u) => {
                self.well_formed(l, pos)?;
                self.well_formed(u, pos)
            }
            Type::Fun(x, s, r) => {
                self.well_formed(s, pos)?;
                self.with(*x, (**s).clone(), |me| me.well_formed(r, pos))
            }
            Type::Rec(z, body) => self.with(*z, t.clone(), |me| me.well_formed(body, pos)),
            Type::Top | Type::Bot | Type::Int | Type::Bool | Type::Unit | Type::Str | Type::Params(_) => Ok(()),
            Type::Applied(..) => {
                let resolved = self.resolve(t, pos)?;
                self.well_formed(&resolved, pos)
            }
        }
    }

    /// A path for the value of `t`: `t` itself if it's one, or else a fresh
    /// variable of its type, which the caller must avoid and drop.
    fn as_path(&mut self, t: &Term) -> Result<(Path, Option<Var>)> {
        let ty = match self.known.remove(&t.pos) {
            Some(ty) => ty,
            None => self.infer(t)?,
        };
        if let Some(p) = term_path(t) {
            if self.stable(&p) {
                return Ok((p, None));
            }
        }
        Ok(self.bind_fresh(ty))
    }

    /// Whether a path always means the same value: whether it doesn't go
    /// through a var field.
    fn stable(&mut self, p: &Path) -> bool {
        match p {
            Path::Var(_) => true,
            Path::Sel(q, a) => {
                if !self.stable(q) {
                    return false;
                }
                let Some(t) = self.path_type(q) else { return true };
                !self.has_var_field(&t, a, q, 0)
            }
        }
    }

    /// Whether a value at `at` of type `t` has a var field `a`.
    fn has_var_field(&mut self, t: &Type, a: &str, at: &Path, depth: usize) -> bool {
        if depth > DEPTH || !self.tick() {
            return false;
        }
        match t {
            Type::VarField(b, _) => b == a,
            Type::And(l, r) => self.has_var_field(l, a, at, depth + 1) || self.has_var_field(r, a, at, depth + 1),
            Type::Rec(z, body) => self.has_var_field(&body.subst(*z, at), a, at, depth + 1),
            Type::Select(p, m) => {
                for (_, upper) in self.bounds(p, m, depth + 1) {
                    if self.has_var_field(&upper, a, at, depth + 1) {
                        return true;
                    }
                }
                false
            }
            _ => false,
        }
    }

    fn bind_fresh(&mut self, ty: Type) -> (Path, Option<Var>) {
        let y = self.names.fresh("it");
        self.env.insert(y, ty);
        (Path::Var(y), Some(y))
    }

    /// `ty` without the fresh variable `y`, if there is one, which goes out of
    /// scope.
    fn release(&mut self, ty: Type, y: Option<Var>) -> Type {
        match y {
            Some(y) => {
                let ty = self.avoid(&ty, y, true, 0);
                self.env.remove(&y);
                ty
            }
            None => ty,
        }
    }

    pub fn infer(&mut self, t: &Term) -> Result<Type> {
        let pos = t.pos;
        match &t.kind {
            TermKind::Var(x) => {
                self.path_type(&Path::Var(*x)).ok_or_else(|| self.error(pos, format!("`{}` has no type here", self.names.name(*x))))
            }
            TermKind::Int(_) => Ok(Type::Int),
            TermKind::Bool(_) => Ok(Type::Bool),
            TermKind::Unit => Ok(Type::Unit),
            TermKind::Str(_) => Ok(Type::Str),
            TermKind::Lam(x, Some(ty), body) => {
                let ty = self.resolve(ty, pos)?;
                self.well_formed(&ty, pos)?;
                let r = self.with(*x, ty.clone(), |me| me.infer(body))?;
                Ok(Type::Fun(*x, Box::new(ty), Box::new(r)))
            }
            TermKind::Lam(x, None, _) => Err(self.error(
                pos,
                format!("can't tell what type `{0}` is here: write `({0}: T) => ...`", self.names.name(*x)),
            )),
            TermKind::App(..) => {
                let mut args = vec![];
                let mut head = t;
                while let TermKind::App(fun, arg) = &head.kind {
                    args.push(&**arg);
                    head = fun;
                }
                args.reverse();
                let mut fresh = vec![];
                let r = self.call(head, &args, &mut fresh, pos, None);
                // the variables made along the way go out of scope
                let mut ty = r?;
                for y in fresh.into_iter().rev() {
                    ty = self.avoid(&ty, y, true, 0);
                    self.env.remove(&y);
                }
                Ok(ty)
            }
            TermKind::TypeArg(ty) => {
                let ty = self.resolve(ty, pos)?;
                self.well_formed(&ty, pos)?;
                Ok(Type::Member("T".to_string(), Box::new(ty.clone()), Box::new(ty)))
            }
            TermKind::LetVar(x, ann, value, body) => {
                let ty = self.bind(ann.as_ref(), value)?;
                self.mutables.insert(*x, ty);
                let r = self.infer(body);
                self.mutables.remove(x);
                r
            }
            TermKind::Get(x) => Ok(self.mutables[x].clone()),
            TermKind::Set(x, value) => {
                let ty = self.mutables[x].clone();
                self.check(value, &ty)?;
                Ok(Type::Unit)
            }
            TermKind::Assign(recv, a, value) => {
                let (p, y) = self.as_path(recv)?;
                let rt = self.path_type(&p).unwrap();
                let field = match self.field_of(&rt, a, &p, 0) {
                    Some(ft) if self.has_var_field(&rt, a, &p, 0) => Ok(ft),
                    Some(_) => Err(self.error(pos, format!("`{a}` is a val, so it can't be assigned to"))),
                    None => Err(self.error(pos, format!("there's no `{a}` in {}", self.show(&rt)))),
                };
                let r = field.and_then(|ft| self.check(value, &ft));
                if let Some(y) = y {
                    self.env.remove(&y);
                }
                r.map(|_| Type::Unit)
            }
            TermKind::While(c, body) => {
                self.check(c, &Type::Bool)?;
                self.infer(body)?;
                Ok(Type::Unit)
            }
            TermKind::Foreign(..) => Err(self.error(pos, "a function declared without a body needs its type".to_string())),
            TermKind::Sel(recv, a) => {
                let (p, y) = self.as_path(recv)?;
                let rt = self.path_type(&p).unwrap();
                if self.sub(&rt, &Type::Str) && !matches!(rt, Type::Bot) {
                    self.notes.insert(pos, Note::StrMember);
                }
                match self.field_of(&rt, a, &p, 0) {
                    Some(ft) => {
                        let ft = unfold(&ft, &p.sel(a));
                        Ok(self.release(ft, y))
                    }
                    None => {
                        let shown = self.show(&rt);
                        self.release(Type::Top, y);
                        Err(self.error(pos, format!("there's no `{a}` in {shown}")))
                    }
                }
            }
            TermKind::New(z, ann, defs) => self.object(*z, ann.as_ref(), defs, pos),
            TermKind::Let(x, ann, value, body) => {
                let ty = self.bind(ann.as_ref(), value)?;
                self.with(*x, ty, |me| {
                    let r = me.infer(body)?;
                    Ok(me.avoid(&r, *x, true, 0))
                })
            }
            TermKind::If(c, a, b) => {
                self.check(c, &Type::Bool)?;
                let ta = self.infer(a)?;
                let tb = self.infer(b)?;
                Ok(self.join(&ta, &tb))
            }
            TermKind::Prim(prim, args) => self.prim(prim, args, pos),
            TermKind::Ascribe(e, ty) => {
                let ty = self.resolve(ty, pos)?;
                self.well_formed(&ty, pos)?;
                self.check(e, &ty)?;
                Ok(ty)
            }
        }
    }

    /// The type of `head(args[0])(args[1])...`. A type parameter whose
    /// argument isn't given is worked out from the arguments that are, and
    /// passed before them. Fresh variables made for values that aren't paths
    /// go in `fresh`, for the caller to avoid and drop.
    fn call(&mut self, head: &Term, args: &[&Term], fresh: &mut Vec<Var>, pos: usize, expected: Option<&Type>) -> Result<Type> {
        let (mut fp, fy) = self.as_path(head)?;
        fresh.extend(fy);
        let mut ty = self.path_type(&fp).unwrap();
        let mut i = 0;
        // how many type arguments go before each argument (a term can be
        // checked more than once, so these are set, not added to)
        let mut implicit: HashMap<usize, usize> = HashMap::new();
        while i < args.len() {
            let Some((x, param, result)) = self.fun_of(&ty, &fp, 0) else {
                return Err(self.error(pos, format!("this isn't a function: it has type {}", self.show(&ty))));
            };
            let arg = args[i];
            if self.takes_type(x, &param) && !matches!(arg.kind, TermKind::TypeArg(_)) && !self.fits(arg, &param)? {
                let found = self.type_argument(x, &param, &result, &args[i..], expected)?;
                let object = Type::Member("T".to_string(), Box::new(found.clone()), Box::new(found.clone()));
                if !self.sub(&object, &param) {
                    return Err(self.error(
                        arg.pos,
                        format!(
                            "{} doesn't fit `{}`, whose bounds are {}",
                            self.show(&found),
                            self.names.name(x),
                            self.show(&param)
                        ),
                    ));
                }
                *implicit.entry(arg.pos).or_insert(0) += 1;
                let (yp, y) = self.bind_fresh(object);
                fresh.extend(y);
                ty = result.subst(x, &yp);
            } else {
                let (ap, ay) = self.check_path(arg, &param)?;
                fresh.extend(ay);
                ty = result.subst(x, &ap);
                i += 1;
            }
            if i < args.len() {
                let (p, y) = self.bind_fresh(ty.clone());
                fresh.extend(y);
                ty = self.path_type(&p).unwrap();
                fp = p;
            }
        }
        for a in args {
            match implicit.get(&a.pos) {
                Some(&n) => self.implicit.insert(a.pos, n),
                None => self.implicit.remove(&a.pos),
            };
        }
        Ok(ty)
    }

    /// Whether a parameter is a type parameter: an object that's only a type
    /// member `T`, whether written `[A]` or `(A: { type T })`.
    fn takes_type(&self, x: Var, param: &Type) -> bool {
        self.names.is_type_param(x) || matches!(param, Type::Member(n, ..) if n == "T")
    }

    /// Whether `arg` is a value of type `param` already (so it's not a type
    /// argument that's been left out). Its type is kept, so it's only found
    /// once.
    fn fits(&mut self, arg: &Term, param: &Type) -> Result<bool> {
        if matches!(arg.kind, TermKind::Lam(_, None, _)) {
            return Ok(false);
        }
        let actual = match self.known.get(&arg.pos) {
            Some(t) => t.clone(),
            None => {
                let t = self.infer(arg)?;
                self.known.insert(arg.pos, t.clone());
                t
            }
        };
        Ok(self.sub(&actual, param))
    }

    /// What the type parameter `x` (an object with bounds `bound`) of a
    /// function with the rest of its type `rest` must be, for it to take
    /// `args`: the join of what the arguments say it must be at least, or
    /// else the meet of what it must be at most, or else its lower bound.
    fn type_argument(&mut self, x: Var, bound: &Type, rest: &Type, args: &[&Term], expected: Option<&Type>) -> Result<Type> {
        let (mut lowers, mut uppers) = (vec![], vec![]);
        let mut chain = rest.clone();
        let mut lambdas = vec![];
        let mut used = 0;
        for &arg in args {
            // later type parameters take no arguments of their own here
            while let Type::Fun(y, p, result) = &chain {
                if !self.takes_type(*y, p) || matches!(arg.kind, TermKind::TypeArg(_)) {
                    break;
                }
                chain = (**result).clone();
            }
            let Type::Fun(_, param, result) = &chain else { break };
            if param.mentions(x) {
                if matches!(arg.kind, TermKind::Lam(_, None, _)) {
                    lambdas.push((arg, (**param).clone()));
                } else {
                    let actual = match self.known.get(&arg.pos) {
                        Some(t) => t.clone(),
                        None => {
                            let t = self.infer(arg)?;
                            self.known.insert(arg.pos, t.clone());
                            t
                        }
                    };
                    // a path's type members are best named through it
                    let at = term_path(arg).filter(|p| self.stable(p));
                    self.constrain(param, &actual, at.as_ref(), x, true, &mut lowers, &mut uppers);
                }
            }
            chain = (**result).clone();
            used += 1;
        }
        // the result, given every argument, has to fit what's expected of it
        if let (Some(expected), true) = (expected, used == args.len()) {
            if chain.mentions(x) {
                self.constrain(&chain, expected, None, x, false, &mut lowers, &mut uppers);
            }
        }
        // a lambda whose parameter is known says what its result is
        for (arg, param) in lambdas {
            let (Type::Fun(_, domain, codomain), TermKind::Lam(v, None, body)) = (&param, &arg.kind) else { continue };
            if domain.mentions(x) || !codomain.mentions(x) {
                continue;
            }
            if let Ok(r) = self.with(*v, (**domain).clone(), |me| me.infer(body)) {
                self.constrain(codomain, &r, None, x, true, &mut lowers, &mut uppers);
            }
        }
        if let Some(first) = lowers.first().cloned() {
            return Ok(lowers[1..].iter().fold(first, |acc, t| self.join(&acc, t)));
        }
        if !uppers.is_empty() {
            return Ok(Type::and(uppers));
        }
        Ok(match bound {
            Type::Member(_, lower, _) => (**lower).clone(),
            _ => Type::Bot,
        })
    }

    /// Adds what `x.T` must be at least (or at most, where it's
    /// contravariant) for `actual`, the type of the value at `at` if that's
    /// a path, to be a subtype of `param`.
    #[allow(clippy::too_many_arguments)]
    fn constrain(
        &mut self,
        param: &Type,
        actual: &Type,
        at: Option<&Path>,
        x: Var,
        positive: bool,
        lowers: &mut Vec<Type>,
        uppers: &mut Vec<Type>,
    ) {
        if !param.mentions(x) || !self.tick() {
            return;
        }
        // what `actual` has, looked up at a fresh variable that's then
        // avoided
        let lookup = |me: &mut Self, f: &dyn Fn(&mut Self, &Path) -> Vec<(Type, bool)>| -> Vec<(Type, bool)> {
            let (w, y) = me.bind_fresh(actual.clone());
            let y = y.unwrap();
            let found: Vec<(Type, bool)> = f(me, &w).into_iter().map(|(t, cov)| (me.avoid(&t, y, cov, 0), cov)).collect();
            me.env.remove(&y);
            found
        };
        match param {
            Type::Select(Path::Var(v), m) if *v == x && m == "T" => {
                if positive {
                    lowers.push(actual.clone());
                } else {
                    uppers.push(actual.clone());
                }
            }
            Type::Fun(_, p, r) => {
                let found = lookup(self, &|me, w| {
                    let t = unfold(&me.env[&w.root()].clone(), w);
                    match me.fun_of(&t, w, 0) {
                        Some((_, a, b)) => vec![(a, false), (b, true)],
                        None => vec![],
                    }
                });
                if let [(a, _), (b, _)] = &found[..] {
                    self.constrain(p, a, None, x, !positive, lowers, uppers);
                    self.constrain(r, b, None, x, positive, lowers, uppers);
                }
            }
            Type::And(l, r) => {
                self.constrain(l, actual, at, x, positive, lowers, uppers);
                self.constrain(r, actual, at, x, positive, lowers, uppers);
            }
            Type::Field(n, p) | Type::VarField(n, p) => {
                let found = lookup(self, &|me, w| {
                    let t = unfold(&me.env[&w.root()].clone(), w);
                    me.field_of(&t, n, w, 0).map(|f| vec![(f, true)]).unwrap_or_default()
                });
                if let [(f, _)] = &found[..] {
                    let inner = at.map(|q| q.sel(n)).filter(|q| self.stable(q));
                    self.constrain(p, f, inner.as_ref(), x, positive, lowers, uppers);
                    if matches!(param, Type::VarField(..)) {
                        self.constrain(p, f, None, x, !positive, lowers, uppers);
                    }
                }
            }
            // a path's type member is a type of its own
            Type::Member(n, pl, pu) if at.is_some() => {
                let member = Type::Select(at.unwrap().clone(), n.clone());
                self.constrain(pu, &member, None, x, positive, lowers, uppers);
                self.constrain(pl, &member, None, x, !positive, lowers, uppers);
            }
            Type::Member(n, pl, pu) => {
                // the member's bounds, all at once: its upper bounds meet
                let found = lookup(self, &|me, w| {
                    let bounds = me.bounds(w, n, 0);
                    let upper: Vec<Type> = bounds.iter().map(|(_, u)| u.clone()).filter(|u| *u != Type::Top).collect();
                    let lower = bounds.iter().map(|(l, _)| l.clone()).find(|l| *l != Type::Bot);
                    if bounds.is_empty() {
                        return vec![];
                    }
                    vec![(lower.unwrap_or(Type::Bot), false), (Type::and(upper), true)]
                });
                if let [(l, _), (u, _)] = &found[..] {
                    self.constrain(pu, u, None, x, positive, lowers, uppers);
                    self.constrain(pl, l, None, x, !positive, lowers, uppers);
                }
            }
            Type::Rec(_, body) => self.constrain(body, actual, at, x, positive, lowers, uppers),
            _ => {}
        }
    }

    /// The type a `let` gives its variable.
    fn bind(&mut self, ann: Option<&Type>, value: &Term) -> Result<Type> {
        match ann {
            Some(ty) => {
                let ty = self.resolve(ty, value.pos)?;
                self.well_formed(&ty, value.pos)?;
                self.check(value, &ty)?;
                Ok(ty)
            }
            None => self.infer(value),
        }
    }

    /// The function type `expected` is, if it is one, with the fresh
    /// variable it was looked up at, which the caller must drop.
    fn expected_fun(&mut self, expected: &Type) -> Option<((Var, Type, Type), Var)> {
        let (at, y) = self.bind_fresh(expected.clone());
        let y = y.unwrap();
        let unfolded = unfold(expected, &at);
        match self.fun_of(&unfolded, &at, 0) {
            Some(f) if !matches!(expected, Type::Bot) => Some((f, y)),
            _ => {
                self.env.remove(&y);
                None
            }
        }
    }

    /// Checks the lambda `(x: param) => body` against the function type
    /// `(y: wanted) => result`.
    fn check_lambda(&mut self, t: &Term, (y, wanted, result): (Var, Type, Type)) -> Result<()> {
        let TermKind::Lam(x, param, body) = &t.kind else { unreachable!() };
        let param = match param {
            Some(param) => {
                let param = &self.resolve(param, t.pos)?;
                self.well_formed(param, t.pos)?;
                if !self.sub(&wanted, param) {
                    return Err(self.error(
                        t.pos,
                        format!("expected a function taking {}, but this takes {}", self.show(&wanted), self.show(param)),
                    ));
                }
                param.clone()
            }
            None => wanted,
        };
        let result = result.subst(y, &Path::Var(*x));
        self.with(*x, param, |me| me.check(body, &result))
    }

    /// Checks that `t` has type `expected`.
    pub fn check(&mut self, t: &Term, expected: &Type) -> Result<()> {
        match &t.kind {
            TermKind::If(c, a, b) => {
                self.check(c, &Type::Bool)?;
                self.check(a, expected)?;
                self.check(b, expected)
            }
            TermKind::Let(x, ann, value, body) => {
                let ty = self.bind(ann.as_ref(), value)?;
                self.with(*x, ty, |me| me.check(body, expected))
            }
            // an external or built-in function is trusted to be what it says it is
            TermKind::Foreign(..) => Ok(()),
            // what's expected of a call can say what its type arguments are
            TermKind::App(..) => {
                let mut args = vec![];
                let mut head = t;
                while let TermKind::App(fun, arg) = &head.kind {
                    args.push(&**arg);
                    head = fun;
                }
                args.reverse();
                let mut fresh = vec![];
                let r = self.call(head, &args, &mut fresh, t.pos, Some(expected));
                let mut ty = match r {
                    Ok(ty) => ty,
                    Err(e) => {
                        for y in fresh {
                            self.env.remove(&y);
                        }
                        return Err(e);
                    }
                };
                for y in fresh.into_iter().rev() {
                    ty = self.avoid(&ty, y, true, 0);
                    self.env.remove(&y);
                }
                if self.sub(&ty, expected) {
                    Ok(())
                } else {
                    Err(self.error(t.pos, format!("expected {}, but this has type {}", self.show(expected), self.show(&ty))))
                }
            }
            // a lambda's body is checked against the result expected, so
            // errors are found where they are, and its parameters' types can
            // come from what's expected
            TermKind::Lam(_, param, _) => match self.expected_fun(expected) {
                Some((fun, y)) => {
                    let r = self.check_lambda(t, fun);
                    self.env.remove(&y);
                    r
                }
                None if param.is_some() => self.check_by_subtyping(t, expected),
                None => Err(self.error(t.pos, format!("expected {}, but this is a function", self.show(expected)))),
            },
            _ => self.check_by_subtyping(t, expected),
        }
    }

    fn check_by_subtyping(&mut self, t: &Term, expected: &Type) -> Result<()> {
        let (_, y) = self.check_path(t, expected)?;
        if let Some(y) = y {
            self.env.remove(&y);
        }
        Ok(())
    }

    /// Checks that `t` has type `expected`, giving it a path, as `as_path`
    /// does.
    fn check_path(&mut self, t: &Term, expected: &Type) -> Result<(Path, Option<Var>)> {
        if let TermKind::Lam(..) = t.kind {
            if let Some((fun, y)) = self.expected_fun(expected) {
                let r = self.check_lambda(t, fun);
                self.env.remove(&y);
                r?;
                return Ok(self.bind_fresh(expected.clone()));
            }
        }
        let (p, y) = self.as_path(t)?;
        let actual = self.path_type(&p).unwrap();
        // a recursive type expected of a path is expected unfolded at it
        let unfolded = match expected {
            Type::Rec(w, c) => c.subst(*w, &p),
            e => e.clone(),
        };
        if self.sub(&actual, &unfolded) {
            return Ok((p, y));
        }
        // a path's type members are themselves: `p: { type A = p.A }`
        if y.is_none() {
            let mut names = vec![];
            self.type_member_names(&actual, &p, 0, &mut names);
            if !names.is_empty() {
                let selves: Vec<Type> = names
                    .into_iter()
                    .map(|n| {
                        let own = Type::Select(p.clone(), n.clone());
                        Type::Member(n, Box::new(own.clone()), Box::new(own))
                    })
                    .collect();
                let refined = Type::And(Box::new(actual.clone()), Box::new(Type::and(selves)));
                if self.sub(&refined, &unfolded) {
                    return Ok((p, y));
                }
            }
        }
        let shown = match y {
            Some(y) => self.env[&y].clone(),
            None => actual,
        };
        if let Some(y) = y {
            self.env.remove(&y);
        }
        Err(self.error(t.pos, format!("expected {}, but this has type {}", self.show(expected), self.show(&shown))))
    }

    /// The names of the type members a value at `at` of type `t` has.
    fn type_member_names(&mut self, t: &Type, at: &Path, depth: usize, out: &mut Vec<String>) {
        if depth > AVOID_DEPTH || !self.tick() {
            return;
        }
        match t {
            Type::Member(n, ..) => {
                if !out.contains(n) {
                    out.push(n.clone());
                }
            }
            Type::And(a, b) => {
                self.type_member_names(a, at, depth + 1, out);
                self.type_member_names(b, at, depth + 1, out);
            }
            Type::Rec(z, body) => self.type_member_names(&body.subst(*z, at), at, depth + 1, out),
            Type::Select(q, m) => {
                for (_, upper) in self.bounds(q, m, depth + 1) {
                    self.type_member_names(&upper, at, depth + 1, out);
                }
            }
            _ => {}
        }
    }

    /// `t` with each `F[X]` whose parameters the parser couldn't see
    /// worked out, from the parameters noted in `F`'s bounds.
    fn resolve(&mut self, t: &Type, pos: usize) -> Result<Type> {
        if !has_applied(t) {
            return Ok(t.clone());
        }
        let b = |t: Type| Box::new(t);
        Ok(match t {
            Type::Applied(f, args) => {
                let f = self.resolve(f, pos)?;
                let args: Vec<Type> = args.iter().map(|a| self.resolve(a, pos)).collect::<Result<_>>()?;
                let Some(params) = self.params_of(&f) else {
                    return Err(self.error(pos, format!("{} doesn't take type parameters", self.show(&f))));
                };
                if params.len() != args.len() {
                    return Err(self.error(
                        pos,
                        format!("{} takes {} type parameters, not {}", self.show(&f), params.len(), args.len()),
                    ));
                }
                let members = params.into_iter().zip(args).map(|((name, variance), arg)| {
                    let (l, u) = match variance {
                        Variance::Co => (Type::Bot, arg),
                        Variance::Contra => (arg, Type::Top),
                        Variance::In => (arg.clone(), arg),
                    };
                    Type::Member(name, b(l), b(u))
                });
                Type::and(std::iter::once(f).chain(members).collect())
            }
            Type::Field(a, u) => Type::Field(a.clone(), b(self.resolve(u, pos)?)),
            Type::VarField(a, u) => Type::VarField(a.clone(), b(self.resolve(u, pos)?)),
            Type::Member(a, l, u) => Type::Member(a.clone(), b(self.resolve(l, pos)?), b(self.resolve(u, pos)?)),
            Type::And(l, r) => Type::And(b(self.resolve(l, pos)?), b(self.resolve(r, pos)?)),
            Type::Fun(x, s, r) => {
                let s = self.resolve(s, pos)?;
                let r = self.with(*x, s.clone(), |me| me.resolve(r, pos))?;
                Type::Fun(*x, b(s), b(r))
            }
            Type::Rec(z, body) => {
                let body = self.with(*z, t.clone(), |me| me.resolve(body, pos))?;
                Type::Rec(*z, b(body))
            }
            t => t.clone(),
        })
    }

    /// The parameters `f` takes, from the note in its bounds.
    fn params_of(&mut self, f: &Type) -> Option<Vec<(String, Variance)>> {
        fn find(me: &mut Typer, t: &Type, depth: usize) -> Option<Vec<(String, Variance)>> {
            if depth > AVOID_DEPTH || !me.tick() {
                return None;
            }
            match t {
                Type::Params(ps) => Some(ps.clone()),
                Type::And(a, b) => find(me, a, depth + 1).or_else(|| find(me, b, depth + 1)),
                Type::Rec(_, body) => find(me, body, depth + 1),
                Type::Select(p, m) => {
                    for (l, u) in me.bounds(p, m, depth + 1) {
                        if let Some(ps) = find(me, &u, depth + 1).or_else(|| find(me, &l, depth + 1)) {
                            return Some(ps);
                        }
                    }
                    None
                }
                _ => None,
            }
        }
        find(self, f, 0)
    }

    /// The type of `new { z: ann => defs }`, once the parameters of any type
    /// it's applied to are known.
    fn object(&mut self, z: Var, ann: Option<&Type>, defs: &[Def], pos: usize) -> Result<Type> {
        let applied = ann.is_some_and(has_applied)
            || defs.iter().any(|d| match &d.kind {
                DefKind::Type(t) | DefKind::Val(Some(t), _) | DefKind::Var(Some(t), _) => has_applied(t),
                _ => false,
            });
        if !applied {
            return self.object_of(z, ann, defs, pos);
        }
        // the object's own types are what the others can be applied to
        let types = Type::and(
            defs.iter()
                .filter_map(|d| match &d.kind {
                    DefKind::Type(t) => Some(Type::Member(d.name.clone(), Box::new(t.clone()), Box::new(t.clone()))),
                    _ => None,
                })
                .collect(),
        );
        let (ann, defs) = self.with(z, types, |me| -> Result<(Option<Type>, Vec<Def>)> {
            let mut defs = defs.to_vec();
            // `new F[X] { ... }`: the parameters' members are what it's
            // applied to
            if let Some(Type::Applied(f, args)) = ann {
                if let Some(params) = me.params_of(f) {
                    for ((name, _), arg) in params.into_iter().zip(args) {
                        if !defs.iter().any(|d| d.name == name) {
                            defs.insert(0, Def { name, kind: DefKind::Type(arg.clone()), pos });
                        }
                    }
                }
            }
            for d in &mut defs {
                if let DefKind::Type(t) | DefKind::Val(Some(t), _) | DefKind::Var(Some(t), _) = &mut d.kind {
                    *t = me.resolve(t, d.pos)?;
                }
            }
            let ann = ann.map(|a| me.resolve(a, pos)).transpose()?;
            Ok((ann, defs))
        })?;
        self.object_of(z, ann.as_ref(), &defs, pos)
    }

    fn object_of(&mut self, z: Var, ann: Option<&Type>, defs: &[Def], pos: usize) -> Result<Type> {
        let mut seen = HashSet::new();
        for d in defs {
            if !seen.insert(&d.name) {
                return Err(self.error(d.pos, format!("`{}` is defined twice", d.name)));
            }
        }
        self.initialization_order(z, defs)?;

        // the declared members first
        let mut parts = vec![];
        for d in defs {
            match &d.kind {
                DefKind::Type(t) => parts.push(Type::Member(d.name.clone(), Box::new(t.clone()), Box::new(t.clone()))),
                DefKind::Val(Some(t), _) => parts.push(Type::Field(d.name.clone(), Box::new(t.clone()))),
                DefKind::Var(Some(t), _) => parts.push(Type::VarField(d.name.clone(), Box::new(t.clone()))),
                DefKind::Val(None, _) | DefKind::Var(None, _) => {}
            }
        }
        let declared = Type::and(parts.clone());
        self.with(z, declared.clone(), |me| {
            for d in defs {
                match &d.kind {
                    DefKind::Type(t) | DefKind::Val(Some(t), _) | DefKind::Var(Some(t), _) => me.well_formed(t, d.pos)?,
                    DefKind::Val(None, _) | DefKind::Var(None, _) => {}
                }
            }
            if let Some(ann) = ann {
                me.with(z, Type::And(Box::new(ann.clone()), Box::new(declared.clone())), |me| me.well_formed(ann, pos))?;
            }
            Ok(())
        })?;

        // then the others' types, inferred together: each round assumes what
        // the last found, until that's as general as what each member is
        let unknown: Vec<&Def> = defs.iter().filter(|d| matches!(d.kind, DefKind::Val(None, _) | DefKind::Var(None, _))).collect();
        let field = |d: &Def, t: Type| match d.kind {
            DefKind::Var(..) => Type::VarField(d.name.clone(), Box::new(t)),
            _ => Type::Field(d.name.clone(), Box::new(t)),
        };
        let mut assumed: Vec<Type> = vec![Type::Bot; unknown.len()];
        for round in 0.. {
            let known = Type::and(
                ann.into_iter()
                    .cloned()
                    .chain(parts.iter().cloned())
                    .chain(unknown.iter().zip(&assumed).map(|(d, t)| field(d, t.clone())))
                    .collect(),
            );
            let found: Vec<Type> = self.with(z, known.clone(), |me| {
                unknown
                    .iter()
                    .map(|d| match &d.kind {
                        DefKind::Val(None, t) | DefKind::Var(None, t) => me.infer(t),
                        _ => unreachable!(),
                    })
                    .collect::<Result<_>>()
            })?;
            let mut stable = true;
            for (i, ty) in found.into_iter().enumerate() {
                let fits = self.with(z, known.clone(), |me| me.sub(&ty, &assumed[i]));
                if !fits {
                    stable = false;
                    if round + 1 == ROUNDS {
                        return Err(self.error(
                            unknown[i].pos,
                            format!("can't work out the type of `{}`: write its result type", unknown[i].name),
                        ));
                    }
                    assumed[i] = self.with(z, known.clone(), |me| me.join(&assumed[i], &ty));
                }
            }
            if stable {
                break;
            }
        }
        parts.extend(unknown.iter().zip(assumed).map(|(d, t)| field(d, t)));

        // then check the declared ones, with the self variable of the type
        // the object's been given
        let sig = Type::and(parts);
        let view = match ann {
            Some(ann) => Type::And(Box::new(ann.clone()), Box::new(sig.clone())),
            None => sig.clone(),
        };
        self.with(z, view, |me| {
            for d in defs {
                if let DefKind::Val(Some(ty), t) | DefKind::Var(Some(ty), t) = &d.kind {
                    me.check(t, ty)?;
                }
            }
            if let Some(ann) = ann {
                if !me.sub(&sig, ann) {
                    return Err(me.error(
                        pos,
                        format!("this object has type {}, which isn't its self type {}", me.show(&sig), me.show(ann)),
                    ));
                }
            }
            Ok(())
        })?;
        let ty = ann.cloned().unwrap_or(sig);
        Ok(if ty.mentions(z) { Type::Rec(z, Box::new(ty)) } else { ty })
    }

    /// Checks that an object's values only use what's been computed before
    /// them: the members before them, and functions that only use those.
    /// Only functions (which run later) can use the object itself.
    fn initialization_order(&self, z: Var, defs: &[Def]) -> Result<()> {
        let vals: Vec<(&Def, &Term)> = defs
            .iter()
            .filter_map(|d| match &d.kind {
                DefKind::Val(_, t) | DefKind::Var(_, t) => Some((d, t)),
                DefKind::Type(_) => None,
            })
            .collect();
        let order: HashMap<&str, usize> = vals.iter().enumerate().map(|(i, (d, _))| (d.name.as_str(), i)).collect();
        // what each member uses, anywhere in it
        let uses: HashMap<&str, (HashSet<String>, bool)> = vals
            .iter()
            .map(|(d, t)| {
                let (mut out, mut bare) = (HashSet::new(), false);
                uses_of(t, z, &mut out, &mut bare);
                (d.name.as_str(), (out, bare))
            })
            .collect();
        let me = self.names.name(z);
        for (i, (d, t)) in vals.iter().enumerate() {
            if is_lambda(t) {
                continue;
            }
            // what computing it can read: what it uses, and what the
            // functions among those use, which it may call
            let (direct, bare) = &uses[d.name.as_str()];
            if *bare {
                return Err(self.error(d.pos, format!("`{}` uses `{me}` before it's built: only a def can", d.name)));
            }
            let mut reads: Vec<String> = direct.iter().cloned().collect();
            let mut seen: HashSet<String> = reads.iter().cloned().collect();
            while let Some(m) = reads.pop() {
                let Some(&j) = order.get(m.as_str()) else { continue };
                if j >= i {
                    let what = if j == i { "itself".to_string() } else { format!("`{m}`, which comes after it") };
                    return Err(self.error(d.pos, format!("`{}` uses {what}, before it's been computed", d.name)));
                }
                if is_lambda(vals[j].1) {
                    let (more, bare) = &uses[m.as_str()];
                    if *bare {
                        return Err(self.error(
                            d.pos,
                            format!("`{}` uses `{m}`, which uses `{me}` before it's built", d.name),
                        ));
                    }
                    for n in more {
                        if seen.insert(n.clone()) {
                            reads.push(n.clone());
                        }
                    }
                }
            }
        }
        Ok(())
    }

    /// The kind of value `ty` is, if it's one `+`, `==` and `print` know.
    fn kind(&mut self, ty: &Type) -> Option<Kind> {
        if self.sub(ty, &Type::Int) {
            Some(Kind::Int)
        } else if self.sub(ty, &Type::Bool) {
            Some(Kind::Bool)
        } else if self.sub(ty, &Type::Str) {
            Some(Kind::Str)
        } else {
            None
        }
    }

    fn prim(&mut self, prim: &Prim, args: &[Term], pos: usize) -> Result<Type> {
        use Prim::*;
        let all = |me: &mut Self, ty: Type| args.iter().try_for_each(|a| me.check(a, &ty));
        match prim {
            Add => {
                let (ta, tb) = (self.infer(&args[0])?, self.infer(&args[1])?);
                let (ka, kb) = (self.kind(&ta), self.kind(&tb));
                if ka == Some(Kind::Str) || kb == Some(Kind::Str) {
                    for (k, t, a) in [(ka, &ta, &args[0]), (kb, &tb, &args[1])] {
                        if k.is_none() {
                            return Err(self.error(a.pos, format!("can't add {} to a String", self.show(t))));
                        }
                    }
                    self.notes.insert(pos, Note::Concat(ka.unwrap(), kb.unwrap()));
                    return Ok(Type::Str);
                }
                all(self, Type::Int)?;
                Ok(Type::Int)
            }
            Sub | Mul | Div | Rem | Neg => {
                all(self, Type::Int)?;
                Ok(Type::Int)
            }
            Lt | Le | Gt | Ge => {
                all(self, Type::Int)?;
                Ok(Type::Bool)
            }
            And | Or | Not => {
                all(self, Type::Bool)?;
                Ok(Type::Bool)
            }
            Eq | Ne => {
                let (ta, tb) = (self.infer(&args[0])?, self.infer(&args[1])?);
                match (self.kind(&ta), self.kind(&tb)) {
                    (Some(a), Some(b)) if a == b => {
                        if a == Kind::Str {
                            self.notes.insert(pos, Note::StrEq);
                        }
                    }
                    // anything else is compared by identity
                    (None, None) => {}
                    _ => {
                        return Err(self.error(pos, format!("can't compare {} with {}", self.show(&ta), self.show(&tb))));
                    }
                }
                Ok(Type::Bool)
            }
            Print | PrintLn => {
                let ty = self.infer(&args[0])?;
                match self.kind(&ty) {
                    Some(Kind::Int) => {}
                    Some(Kind::Bool) => {
                        self.notes.insert(pos, Note::PrintBool);
                    }
                    Some(Kind::Str) => {
                        self.notes.insert(pos, Note::PrintStr);
                    }
                    None => {
                        return Err(self.error(
                            args[0].pos,
                            format!("can only print an Int, a Bool or a String, not {}", self.show(&ty)),
                        ));
                    }
                }
                Ok(Type::Unit)
            }
            PrintChar => {
                all(self, Type::Int)?;
                Ok(Type::Unit)
            }
            Puts(_) => Ok(Type::Unit),
            Read | ReadChar => Ok(Type::Int),
            ReadLine => Ok(Type::Str),
            Error => {
                all(self, Type::Str)?;
                Ok(Type::Bot)
            }
        }
    }
}

/// Whether `t` is made of fields and type members.
/// Whether `t` has an `F[X]` still to work out.
fn has_applied(t: &Type) -> bool {
    match t {
        Type::Applied(..) => true,
        Type::Field(_, u) | Type::VarField(_, u) | Type::Rec(_, u) => has_applied(u),
        Type::Member(_, a, b) | Type::And(a, b) | Type::Fun(_, a, b) => has_applied(a) || has_applied(b),
        _ => false,
    }
}

fn is_record(t: &Type) -> bool {
    match t {
        Type::Field(..) | Type::VarField(..) | Type::Member(..) | Type::Rec(..) => true,
        Type::And(a, b) => is_record(a) || is_record(b),
        _ => false,
    }
}
