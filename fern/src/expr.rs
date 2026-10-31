//! Inferring expressions' types (and turning them into core), and
//! patterns'.
//!
//! Each `infer` gives an expression's core and its type, unifying as it
//! goes. Effects: `self.effect` is the row of effects the function (or
//! lambda) being checked may have; every call adds the callee's effects to
//! it, by unifying, and a `handle` takes one away from its body's.

use crate::ast::{self, BinOp, Expr, ExprKind, PatKind, Pattern, Stmt, UnOp};
use crate::checker::{Checker, Local, Res, Use, UseKind, Wanted};
use crate::core::{Cmp, Core, Eff, Pat, Prim};
use crate::lexer::Pos;
use crate::modules::{Def, ItemKind, Ns};
use crate::types::{substitute, Pred, Type};
use bf::asm::fx::HashMap;

pub const EQ: &str = "std::Eq";
pub const ORD: &str = "std::Ord";
/// The traits behind + - * / % and negation, and their methods.
pub const ARITH: &[(Prim, &str, &str)] =
    &[(Prim::Add, "std::Add", "add"), (Prim::Sub, "std::Sub", "sub"), (Prim::Mul, "std::Mul", "mul"), (Prim::Div, "std::Div", "div"), (Prim::Rem, "std::Rem", "rem"), (Prim::Neg, "std::Neg", "neg")];

/// The trait and method of an arithmetic op.
pub fn arith_trait(p: Prim) -> (&'static str, &'static str) {
    let (_, t, m) = ARITH.iter().find(|(q, _, _)| *q == p).expect("an arithmetic op");
    (t, m)
}
pub const LIST: &str = "std::List";

/// A record's fields, if they're all known (its row isn't open).
fn record_labels(row: &Type) -> Option<Vec<String>> {
    match row {
        Type::RowEmpty => Some(vec![]),
        Type::RowExtend(label, _, rest) => {
            let mut ls = record_labels(rest)?;
            ls.push(label.clone());
            Some(ls)
        }
        _ => None,
    }
}

/// `c` (of type `t`), at `pos`.
fn located(pos: Pos, (c, t): (Core, Type)) -> (Core, Type) {
    (Core::Located(pos, Box::new(c)), t)
}

impl Checker<'_> {
    fn push_scope(&mut self) {
        self.scopes.push(HashMap::default());
    }

    fn pop_scope(&mut self) {
        self.scopes.pop();
    }

    /// The local variable `name`, if there is one: which is then used.
    fn find_local(&self, name: &str) -> Option<Local> {
        let local = self.scopes.iter().rev().find_map(|s| s.get(name).cloned())?;
        if let Some(at) = local.at {
            self.used.borrow_mut().insert((at.file, at.line, at.col));
        }
        Some(local)
    }

    /// A new local variable in the innermost scope: its unique name. With
    /// `at` (where it's declared), it's warned of if it's never used,
    /// unless its name starts with `_` (or it's the standard library's).
    fn bind_local(&mut self, name: &str, ty: Type, mutable: bool, at: Option<Pos>) -> String {
        let unique = self.fresh_name(name);
        let at = at.filter(|p| p.file != 0 && !name.starts_with('_'));
        if let Some(pos) = at {
            self.declared.push((pos, name.to_string()));
        }
        self.scopes.last_mut().unwrap().insert(name.to_string(), Local { name: unique.clone(), ty, mutable, at });
        unique
    }

    /// A requirement to meet with a dictionary: its number.
    pub fn new_hole(&mut self, pred: Pred, pos: Pos) -> usize {
        let hole = self.holes.len();
        self.holes.push(None);
        self.wanted.push(Wanted { pred, hole, pos });
        hole
    }

    /// A row of effects, open: if it ends (a function type written with
    /// `with`), it ends in a new variable instead, so it can be part of a
    /// bigger row (calling such a function is fine wherever more is allowed).
    fn open(&mut self, eff: &Type) -> Type {
        match self.u.zonk(eff) {
            Type::RowEmpty => self.u.fresh(),
            Type::RowExtend(l, t, rest) => {
                let rest = self.open(&rest);
                Type::RowExtend(l, t, Box::new(rest))
            }
            other => other,
        }
    }

    /// The effects of something done here: part of what's allowed here.
    fn performs(&mut self, eff: &Type, pos: Pos) -> Res<()> {
        let here = self.effect.clone();
        self.performs_in(eff, &here, pos)
    }

    /// That code whose effects are `here` does what `eff` says.
    fn performs_in(&mut self, eff: &Type, here: &Type, pos: Pos) -> Res<()> {
        let eff = self.open(eff);
        self.u.unify(&eff, here).map_err(|e| {
            let why = match e.strip_prefix("missing ") {
                Some(effect) => format!("this has the effect {effect}, which isn't allowed here"),
                None => format!("this has an effect that isn't allowed here: {e}"),
            };
            (pos, why)
        })
    }

    pub fn infer(&mut self, e: &Expr) -> Res<(Core, Type)> {
        let pos = e.pos;
        Ok(match &e.kind {
            ExprKind::Int(n) => (Core::Int(*n), Type::int()),
            ExprKind::Str(s) => (Core::Str(s.clone()), Type::string()),
            ExprKind::Bool(b) => (Core::Int(*b as i64), Type::bool()),
            ExprKind::Unit => (Core::Int(0), Type::unit()),
            ExprKind::Path(path) => {
                if path.segments.len() == 1 {
                    if let Some(l) = self.find_local(&path.segments[0]) {
                        let core = if l.mutable { Core::GetRef(Box::new(Core::Local(l.name))) } else { Core::Local(l.name) };
                        return Ok((core, l.ty));
                    }
                }
                let def = self.lookup(path, Ns::Value)?;
                self.value(def, pos)?
            }
            // (calls are where runtime errors can be: see `Core::Located`)
            ExprKind::Call(f, args) => located(pos, self.call(f, args, pos)?),
            ExprKind::Method(recv, name, args) => located(pos, self.method_call(recv, name, args, pos)?),
            ExprKind::Field(r, name) => {
                let (recv, recv_ty) = self.infer(r)?;
                let u = Use { recv, recv_ty, name: name.clone(), what: UseKind::Get, result: self.u.fresh(), here: self.effect.clone(), module: self.module, pos, id: 0 };
                self.use_or_wait(u)?
            }
            ExprKind::Binary(op, a, b) => self.binary(*op, a, b, pos)?,
            ExprKind::Unary(UnOp::Neg, a) => {
                let (c, t) = self.infer(a)?;
                self.arith(Prim::Neg, vec![c], t, pos)?
            }
            ExprKind::Unary(UnOp::Not, a) => {
                let (c, t) = self.infer(a)?;
                self.unify(&t, &Type::bool(), a.pos)?;
                (Core::Prim(Prim::Not, vec![c]), Type::bool())
            }
            ExprKind::Block(stmts, tail) => {
                self.push_scope();
                let r = self.block(stmts, tail.as_deref(), pos);
                self.pop_scope();
                r?
            }
            ExprKind::If(c, t, els) => {
                let (cc, ct) = self.infer(c)?;
                self.unify(&ct, &Type::bool(), c.pos)?;
                let (tc, tt) = self.infer(t)?;
                let (ec, et) = match els {
                    Some(e) => self.infer(e)?,
                    None => (Core::Int(0), Type::unit()),
                };
                self.unify(&tt, &et, pos).map_err(|(p, m)| (p, format!("the branches of this if: {m}")))?;
                (Core::If(Box::new(cc), Box::new(tc), Box::new(ec)), tt)
            }
            ExprKind::Match(scrutinee, arms) => {
                let (sc, st) = self.infer(scrutinee)?;
                let result = self.u.fresh();
                let mut out = vec![];
                for (pat, body) in arms {
                    self.push_scope();
                    let p = self.pattern(pat, &st);
                    let b = p.and_then(|p| Ok((p, self.infer(body)?)));
                    self.pop_scope();
                    let (p, (bc, bt)) = b?;
                    self.unify(&bt, &result, body.pos)?;
                    out.push((p, bc));
                }
                let pats: Vec<Pat> = out.iter().map(|(p, _)| p.clone()).collect();
                self.exhaustive(&pats, pos)?;
                (Core::Match(Box::new(sc), out), result)
            }
            ExprKind::While(c, body) => {
                let (cc, ct) = self.infer(c)?;
                self.unify(&ct, &Type::bool(), c.pos)?;
                self.loops += 1;
                let r = self.infer(body);
                self.loops -= 1;
                let (bc, _) = r?;
                (Core::While(Box::new(cc), Box::new(bc)), Type::unit())
            }
            ExprKind::Loop(body) => {
                self.loops += 1;
                let r = self.infer(body);
                self.loops -= 1;
                (Core::Loop(Box::new(r?.0)), Type::unit())
            }
            ExprKind::Break | ExprKind::Continue => {
                if self.loops == 0 {
                    return Err((pos, "break or continue outside a loop".into()));
                }
                let c = if matches!(e.kind, ExprKind::Break) { Core::Break } else { Core::Continue };
                (c, self.u.fresh())
            }
            ExprKind::Return(v) => {
                let (vc, vt) = match v {
                    Some(v) => self.infer(v)?,
                    None => (Core::Int(0), Type::unit()),
                };
                let ret = self.ret.clone().expect("in a function");
                self.unify(&vt, &ret, pos)?;
                (Core::Return(Box::new(vc)), self.u.fresh())
            }
            ExprKind::Lambda(params, body) => self.lambda(params, body)?,
            ExprKind::Tuple(es) => {
                let mut cs = vec![];
                let mut ts = vec![];
                for e in es {
                    let (c, t) = self.infer(e)?;
                    cs.push(c);
                    ts.push(t);
                }
                (Core::Tuple(cs), Type::Tuple(ts))
            }
            ExprKind::List(es) => {
                let elem = self.u.fresh();
                let (nil, cons) = self.list_tags();
                let mut cs = vec![];
                for e in es {
                    let (c, t) = self.infer(e)?;
                    self.unify(&t, &elem, e.pos)?;
                    cs.push(c);
                }
                let list = cs.into_iter().rev().fold(Core::Con(nil, vec![]), |rest, c| Core::Con(cons, vec![c, rest]));
                (list, Type::Con(LIST.into(), vec![elem]))
            }
            ExprKind::Record(fields, base) => {
                let mut row = match base {
                    Some(_) => self.u.fresh(),
                    None => Type::RowEmpty,
                };
                let base_core = match base {
                    Some(b) => {
                        let (bc, bt) = self.infer(b)?;
                        self.unify(&bt, &Type::Record(Box::new(row.clone())), b.pos)?;
                        Some(bc)
                    }
                    None => None,
                };
                let mut cs: Vec<(String, Core)> = vec![];
                let mut types = vec![];
                for (f, v) in fields {
                    if base.is_none() && cs.iter().any(|(g, _)| g == f) {
                        return Err((v.pos, format!("the field {f} twice")));
                    }
                    let (c, t) = self.infer(v)?;
                    cs.push((f.clone(), c));
                    types.push((f.clone(), t));
                }
                // (the type: each field in front of the rest)
                for (f, t) in types.into_iter().rev() {
                    row = Type::extend(&f, t, row);
                }
                let core = match base_core {
                    Some(b) => Core::RecExtend(Box::new(b), cs),
                    None => Core::Record(cs),
                };
                (core, Type::Record(Box::new(row)))
            }
            ExprKind::StructLit(path, fields) => self.struct_lit(path, fields, pos)?,
            ExprKind::Assign(name, v) => {
                let Some(l) = self.find_local(name) else { return Err((pos, format!("{name} isn't a variable here"))) };
                if !l.mutable {
                    return Err((pos, format!("{name} isn't mutable (declare it with `let mut`)")));
                }
                let (vc, vt) = self.infer(v)?;
                self.unify(&vt, &l.ty, v.pos)?;
                (Core::SetRef(Box::new(Core::Local(l.name)), Box::new(vc)), Type::unit())
            }
            ExprKind::SetField(r, name, v) => self.assign_field(r, name, v, pos)?,
            ExprKind::Handle(body, arms) => self.handle(body, arms, pos)?,
        })
    }

    pub fn list_tags(&self) -> (i64, i64) {
        let list = &self.enums[LIST];
        let tag = |n: &str| list.variants.iter().position(|(v, _)| v == n).unwrap() as i64;
        (tag("Nil"), tag("Cons"))
    }

    fn block(&mut self, stmts: &[Stmt], tail: Option<&Expr>, pos: Pos) -> Res<(Core, Type)> {
        let Some((first, rest)) = stmts.split_first() else {
            return match tail {
                Some(t) => self.infer(t),
                None => Ok((Core::Int(0), Type::unit())),
            };
        };
        match first {
            Stmt::Expr(e) => {
                let (c, _) = self.infer(e)?;
                let (r, t) = self.block(rest, tail, pos)?;
                Ok((Core::Seq(Box::new(c), Box::new(r)), t))
            }
            Stmt::Let { pat, mutable, ty, value } => {
                let (vc, vt) = self.infer(value)?;
                if let Some(t) = ty {
                    let written = self.ty(t, &self.body_ctx.clone())?;
                    self.unify(&vt, &written, value.pos)?;
                }
                if let PatKind::Bind(name) = &pat.kind {
                    let unique = self.bind_local(name, vt, *mutable, Some(pat.pos));
                    let (r, t) = self.block(rest, tail, pos)?;
                    let init = if *mutable { Core::NewRef(Box::new(vc)) } else { vc };
                    return Ok((Core::Let(unique, Box::new(init), Box::new(r)), t));
                }
                if *mutable {
                    return Err((pat.pos, "only a variable can be `mut`".into()));
                }
                // a pattern: a match with one arm, which has to always match
                let p = self.pattern(pat, &vt)?;
                self.exhaustive(std::slice::from_ref(&p), pat.pos)?;
                let (r, t) = self.block(rest, tail, pos)?;
                Ok((destructure(vc, p, r), t))
            }
        }
    }

    fn lambda(&mut self, params: &[ast::Param], body: &Expr) -> Res<(Core, Type)> {
        let saved = (self.effect.clone(), self.ret.take(), self.loops);
        self.effect = self.u.fresh();
        self.loops = 0;
        let ret = self.u.fresh();
        self.ret = Some(ret.clone());
        self.push_scope();
        let mut names = vec![];
        let mut types = vec![];
        let mut cells = vec![];
        for p in params {
            let t = self.param_ty(p, &self.body_ctx.clone(), body.pos)?;
            let name = self.fresh_name(&p.name);
            if p.mutable {
                let cell = self.bind_local(&p.name, t.clone(), true, None);
                cells.push((cell, name.clone()));
            } else {
                self.scopes.last_mut().unwrap().insert(p.name.clone(), Local { name: name.clone(), ty: t.clone(), mutable: false, at: None });
            }
            names.push(name);
            types.push(t);
        }
        let r = self.infer(body);
        self.pop_scope();
        let eff = std::mem::replace(&mut self.effect, saved.0);
        self.ret = saved.1;
        self.loops = saved.2;
        let (mut bc, bt) = r?;
        self.unify(&bt, &ret, body.pos)?;
        for (cell, arg) in cells.into_iter().rev() {
            bc = Core::Let(cell, Box::new(Core::NewRef(Box::new(Core::Local(arg)))), Box::new(bc));
        }
        Ok((Core::Lam(self.lam_id(), names, Box::new(bc), Eff::Row(eff.clone())), Type::func(types, ret, eff)))
    }

    /// Something a path names, used as a value (not called).
    fn value(&mut self, def: Def, pos: Pos) -> Res<(Core, Type)> {
        // a constructor with no fields is a value already
        if let Def::Variant(e, k) = def {
            let (fields, ty) = self.variant(e, k);
            if fields.is_empty() {
                return Ok((Core::Con(k as i64, vec![]), ty));
            }
        }
        // anything else that's called: a function value (a lambda that calls
        // it), whose effects are what calling it does (and, like a call's,
        // open: a pure function is fine where effects are allowed)
        let (ty, _) = self.callee_type(def, pos)?;
        let Type::Fn(params, ret, eff) = ty else { return Err((pos, "not a function".into())) };
        let names: Vec<String> = (0..params.len()).map(|_| self.fresh_name("arg")).collect();
        let args: Vec<Core> = names.iter().map(|n| Core::Local(n.clone())).collect();
        let call = self.direct_call(def, args, (*eff).clone(), pos)?;
        let open = self.open(&eff);
        Ok((Core::Lam(self.lam_id(), names, Box::new(call), Eff::Row(open.clone())), Type::Fn(params, ret, Box::new(open))))
    }

    /// The type of something that can be called, as this use sees it, and
    /// whether it's an effect operation.
    fn callee_type(&mut self, def: Def, pos: Pos) -> Res<(Type, bool)> {
        Ok(match def {
            Def::Item(i) => match &self.prog.items[i].kind {
                ItemKind::Fn(fdef) => {
                    if let Some(t) = self.group.get(&i) {
                        (t.clone(), false)
                    } else if !self.schemes.contains_key(&i) {
                        // (a function whose signature had an error, already
                        // reported: a function of anything, to anything, so
                        // this isn't one as well)
                        let params = fdef.params.iter().map(|_| self.u.fresh()).collect();
                        (Type::func(params, self.u.fresh(), self.u.fresh()), false)
                    } else {
                        let scheme = self.schemes[&i].clone();
                        let (t, preds) = self.u.instantiate(&scheme);
                        self.pending_preds = preds;
                        (t, false)
                    }
                }
                ItemKind::Extern(_) => {
                    let (params, ret, _, io) = self.extern_sigs[&i].clone();
                    let tail = self.u.fresh();
                    let eff = if io { Type::extend("Io", Type::con("Io"), tail) } else { tail };
                    (Type::func(params, ret, eff), false)
                }
                _ => return Err((pos, format!("{} isn't a function", self.prog.items[i].name))),
            },
            Def::Variant(e, k) => {
                let (fields, ty) = self.variant(e, k);
                (Type::func(fields, ty, self.u.fresh()), false)
            }
            Def::Op(e, k) => {
                let (params, ret, eff) = self.op_type(e, k);
                (Type::func(params, ret, eff), true)
            }
            Def::Method(t, k) => {
                let tname = self.prog.items[t].name.clone();
                let (params, ret, eff, pred) = self.method_type(&tname, k);
                self.pending_preds = vec![pred];
                (Type::func(params, ret, eff), false)
            }
            Def::Builtin(b) => {
                let (params, ret, io) = builtin_type(b, || self.u.fresh());
                let tail = self.u.fresh();
                let eff = if io { Type::extend("Io", Type::con("Io"), tail) } else { tail };
                (Type::func(params, ret, eff), false)
            }
            Def::Module(_) => return Err((pos, "a module isn't a value".into())),
        })
    }

    /// The core of calling `def` with `args` (after `callee_type` gave its
    /// type, and its requirements in `pending_preds`), whose effects are `eff`.
    fn direct_call(&mut self, def: Def, args: Vec<Core>, eff: Type, pos: Pos) -> Res<Core> {
        let preds = std::mem::take(&mut self.pending_preds);
        Ok(match def {
            Def::Item(i) if matches!(self.prog.items[i].kind, ItemKind::Extern(_)) => Core::Prim(Prim::Extern(self.extern_sigs[&i].2), args),
            Def::Item(i) => {
                let name = self.prog.items[i].name.clone();
                let mut all = vec![];
                if self.group.contains_key(&i) {
                    all.push(Core::DictArgs);
                } else {
                    for p in preds {
                        let hole = self.new_hole(p, pos);
                        all.push(Core::DictHole(hole));
                    }
                }
                all.extend(args);
                Core::CallGlobal(name, all, Eff::Row(eff))
            }
            Def::Variant(_, k) => Core::Con(k as i64, args),
            Def::Op(e, k) => Core::Perform { eff: e as i64, op: k, args },
            Def::Method(t, k) => {
                let pred = preds.into_iter().next().unwrap();
                let hole = self.new_hole(pred, pos);
                Core::MethodCall(hole, self.prog.items[t].name.clone(), k, args, Eff::Row(eff))
            }
            Def::Builtin(b) => {
                self.reads_input |= b == "read_int";
                builtin_core(b, args)
            }
            Def::Module(_) => unreachable!(),
        })
    }

    fn call(&mut self, f: &Expr, args: &[Expr], pos: Pos) -> Res<(Core, Type)> {
        // a call of something a path names (not a local): directly
        if let ExprKind::Path(path) = &f.kind {
            let local = path.segments.len() == 1 && self.find_local(&path.segments[0]).is_some();
            if !local {
                let def = self.lookup(path, Ns::Value)?;
                let (ty, _) = self.callee_type(def, pos)?;
                let Type::Fn(params, ret, eff) = ty else { return Err((pos, format!("{path} isn't a function"))) };
                if params.len() != args.len() {
                    return Err((pos, format!("{path} takes {} arguments, not {}", params.len(), args.len())));
                }
                let preds = std::mem::take(&mut self.pending_preds);
                let mut cs = vec![];
                for (a, p) in args.iter().zip(&params) {
                    let (c, t) = self.infer(a)?;
                    self.unify(&t, p, a.pos)?;
                    cs.push(c);
                }
                self.performs(&eff, pos)?;
                self.pending_preds = preds;
                let numbers = matches!(def, Def::Builtin("array")) && self.numbers_only(&params[1]);
                let core = match self.direct_call(def, cs, (*eff).clone(), pos)? {
                    // (an array of numbers is one the collector needn't look in)
                    Core::Prim(Prim::ArrayNew, a) if numbers => Core::Prim(Prim::ArrayNewData, a),
                    core => core,
                };
                return Ok((core, *ret));
            }
        }
        // anything else: a function value
        let (fc, ft) = self.infer(f)?;
        let mut cs = vec![];
        let mut ts = vec![];
        for a in args {
            let (c, t) = self.infer(a)?;
            cs.push(c);
            ts.push(t);
        }
        let ret = self.u.fresh();
        let eff = self.u.fresh();
        let want = Type::func(ts, ret.clone(), eff.clone());
        self.unify(&ft, &want, pos).map_err(|(p, m)| (p, format!("calling this: {m}")))?;
        self.performs(&eff, pos)?;
        Ok((Core::App(Box::new(fc), cs, Eff::Row(eff)), ret))
    }

    /// Whether values of a type are known by now to be numbers, never
    /// pointers: `Int`s, `Bool`s, `()`.
    fn numbers_only(&mut self, t: &Type) -> bool {
        matches!(self.u.zonk(t), Type::Con(n, args) if args.is_empty() && (n == "Int" || n == "Bool" || n == "()"))
    }

    /// `recv.name(args)`: a method of the receiver's type, a trait's
    /// method, or a function in a field; which, once the receiver's type is
    /// known (see `resolve_uses`).
    fn method_call(&mut self, recv: &Expr, name: &str, args: &[Expr], pos: Pos) -> Res<(Core, Type)> {
        let (recv, recv_ty) = self.infer(recv)?;
        let mut cargs = vec![];
        for a in args {
            cargs.push(self.infer(a)?);
        }
        let u = Use { recv, recv_ty, name: name.to_string(), what: UseKind::Call(cargs), result: self.u.fresh(), here: self.effect.clone(), module: self.module, pos, id: 0 };
        self.use_or_wait(u)
    }

    /// A method call or field now, if its receiver's type is known; else a
    /// placeholder, filled in when it is.
    fn use_or_wait(&mut self, mut u: Use) -> Res<(Core, Type)> {
        let t = u.result.clone();
        if !matches!(self.u.zonk(&u.recv_ty), Type::Var(_)) {
            return Ok((self.resolve(u, false)?, t));
        }
        u.id = self.resolved.len();
        self.resolved.push(None);
        let core = Core::Pending(u.id);
        self.uses.push(u);
        Ok((core, t))
    }

    /// The method calls and fields still waiting, at the end of a group of
    /// functions: each as soon as its receiver's type is known (working one
    /// out can tell another's); and those nothing decides, as a trait's
    /// method or a record's field (which can decide more).
    pub fn resolve_uses(&mut self) -> Res<()> {
        let mut waiting = std::mem::take(&mut self.uses);
        while !waiting.is_empty() {
            let (known, unknown): (Vec<Use>, Vec<Use>) = waiting.into_iter().partition(|u| !matches!(self.u.zonk(&u.recv_ty), Type::Var(_)));
            waiting = unknown;
            let progress = !known.is_empty();
            for u in known {
                let id = u.id;
                self.resolved[id] = Some(self.resolve(u, false)?);
            }
            if !progress {
                let u = waiting.remove(0);
                let id = u.id;
                self.resolved[id] = Some(self.resolve(u, true)?);
            }
        }
        Ok(())
    }

    /// What a method call or field is, given what its receiver's type is
    /// now (`last`: and nothing more will be known about it).
    fn resolve(&mut self, u: Use, last: bool) -> Res<Core> {
        let ty = self.u.zonk(&u.recv_ty);
        let args = match u.what {
            // a field: a struct's, or else a record's
            UseKind::Get => {
                let (c, t) = self.field(u.recv, u.recv_ty, &u.name, u.pos)?;
                self.unify(&t, &u.result, u.pos)?;
                return Ok(c);
            }
            UseKind::Set(vc, vt) => return self.set_field(u.recv, ty, &u.name, vc, vt, u.pos),
            UseKind::Call(args) => args,
        };
        // the type's own method (a tuple's by its size; a record's by its
        // fields, if they're all known)
        let table = match &ty {
            Type::Con(n, _) => Some(n.clone()),
            Type::Tuple(ts) if ts.len() >= 2 => Some(crate::modules::tuple_key(ts.len())),
            Type::Record(row) => record_labels(&self.u.zonk(row)).map(|ls| crate::modules::record_key(ls.iter().map(|s| s.as_str()))),
            _ => None,
        };
        let own = table.and_then(|n| self.prog.methods.get(&n).and_then(|t| t.get(&u.name)).copied());
        if let Some(id) = own {
            return self.call_method(u.recv, u.recv_ty, args, u.result, &u.here, u.module, id, u.pos);
        }
        // a trait's
        let found: Vec<(String, usize)> = self
            .traits
            .values()
            .filter_map(|t| t.methods.iter().position(|m| m.name == u.name).map(|k| (t.name.clone(), k)))
            .collect();
        if found.len() > 1 {
            let names: Vec<&str> = found.iter().map(|(t, _)| t.as_str()).collect();
            return Err((u.pos, format!("{} is a method of more than one trait ({}): say which, as Trait::{}(x)", u.name, names.join(", "), u.name)));
        }
        if let Some((tname, k)) = found.into_iter().next() {
            let (params, ret, eff, pred) = self.method_type(&tname, k);
            if params.len() != args.len() + 1 {
                return Err((u.pos, format!("{} takes {} arguments, not {}", u.name, params.len() - 1, args.len())));
            }
            self.unify(&u.recv_ty, &params[0], u.pos)?;
            let mut cs = vec![u.recv];
            for ((c, t), p) in args.into_iter().zip(&params[1..]) {
                self.unify(&t, p, u.pos)?;
                cs.push(c);
            }
            self.unify(&ret, &u.result, u.pos)?;
            self.performs_in(&eff, &u.here, u.pos)?;
            let hole = self.new_hole(pred, u.pos);
            return Ok(Core::MethodCall(hole, tname, k, cs, Eff::Row(eff)));
        }
        // a function in a field (of a struct, or a record)
        let has_field = match &ty {
            Type::Con(n, _) => self.structs.get(n).is_some_and(|s| s.fields.iter().any(|(f, _)| *f == u.name)),
            // (a record whose fields are all known has it only if it's one)
            Type::Record(row) => record_labels(&self.u.zonk(row)).is_none_or(|ls| ls.contains(&u.name)),
            _ => false,
        };
        if !has_field {
            return Err((u.pos, match ty {
                Type::Var(_) if last => format!("can't tell what type this is, to find its method {}: annotate it", u.name),
                other => format!("{} has no method {}", self.u.show(&other), u.name),
            }));
        }
        let (fc, ft) = self.field(u.recv, u.recv_ty, &u.name, u.pos)?;
        let (cs, ts): (Vec<Core>, Vec<Type>) = args.into_iter().unzip();
        let eff = self.u.fresh();
        self.unify(&ft, &Type::func(ts, u.result.clone(), eff.clone()), u.pos).map_err(|(p, m)| (p, format!("calling this: {m}")))?;
        self.performs_in(&eff, &u.here, u.pos)?;
        Ok(Core::App(Box::new(fc), cs, Eff::Row(eff)))
    }

    /// A call of method `id` (a function, `self` first) on `recv`.
    #[allow(clippy::too_many_arguments)]
    fn call_method(&mut self, recv: Core, recv_ty: Type, args: Vec<(Core, Type)>, result: Type, here: &Type, module: usize, id: usize, pos: Pos) -> Res<Core> {
        let ItemKind::Fn(f) = &self.prog.items[id].kind else { unreachable!() };
        let (name, has_self) = (f.name.clone(), f.has_self);
        if !self.prog.can_see(module, id) {
            return Err((pos, format!("{name} is private")));
        }
        if !has_self {
            return Err((pos, format!("{name} takes no self: call it as {name}(..)")));
        }
        let (ty, _) = self.callee_type(Def::Item(id), pos)?;
        let Type::Fn(params, ret, eff) = ty else { unreachable!() };
        if params.len() != args.len() + 1 {
            return Err((pos, format!("{name} takes {} arguments, not {}", params.len() - 1, args.len())));
        }
        self.unify(&recv_ty, &params[0], pos)?;
        let mut all = vec![recv];
        for ((c, t), p) in args.into_iter().zip(&params[1..]) {
            self.unify(&t, p, pos)?;
            all.push(c);
        }
        self.unify(&ret, &result, pos)?;
        self.performs_in(&eff, here, pos)?;
        self.direct_call(Def::Item(id), all, *eff, pos)
    }

    /// A trait method's type for one use: parameters, result, effects, and
    /// the requirement that its `Self` has the trait.
    pub fn method_type(&mut self, tname: &str, k: usize) -> (Vec<Type>, Type, Type, Pred) {
        let t = &self.traits[tname];
        let sig = &t.methods[k];
        let mut map = HashMap::default();
        let self_ty = self.u.fresh();
        map.insert(t.self_var, self_ty.clone());
        let vars: Vec<_> = sig.vars.iter().copied().chain([sig.tail]).collect();
        let (params, ret, eff) = (sig.params.clone(), sig.ret.clone(), sig.eff.clone());
        for v in vars {
            map.insert(v, self.u.fresh());
        }
        let params = params.iter().map(|p| substitute(p, &map)).collect();
        (params, substitute(&ret, &map), substitute(&eff, &map), Pred { trait_: tname.to_string(), ty: self_ty })
    }

    /// An enum variant's fields and the enum's type, for one use.
    fn variant(&mut self, e: usize, k: usize) -> (Vec<Type>, Type) {
        let name = self.prog.items[e].name.clone();
        let info = &self.enums[&name];
        let vars = info.vars.clone();
        let fields = info.variants[k].1.clone();
        let map: HashMap<_, _> = vars.iter().map(|&v| (v, self.u.fresh())).collect();
        let args = vars.iter().map(|v| map[v].clone()).collect();
        (fields.iter().map(|f| substitute(f, &map)).collect(), Type::Con(name, args))
    }

    /// An effect operation's parameters, result and effect row, for one use.
    fn op_type(&mut self, e: usize, k: usize) -> (Vec<Type>, Type, Type) {
        let name = self.prog.items[e].name.clone();
        let info = &self.effects[&name];
        let vars = info.vars.clone();
        let op = &info.ops[k];
        let (own, params, ret) = (op.vars.clone(), op.params.clone(), op.ret.clone());
        let mut map: HashMap<_, _> = vars.iter().map(|&v| (v, self.u.fresh())).collect();
        for v in own {
            map.insert(v, self.u.fresh());
        }
        let args = vars.iter().map(|v| map[v].clone()).collect();
        let tail = self.u.fresh();
        let eff = Type::extend(&name, Type::Con(name.clone(), args), tail);
        (params.iter().map(|p| substitute(p, &map)).collect(), substitute(&ret, &map), eff)
    }

    /// `r.name`: a struct's field, if `r` is known to be a struct; else a
    /// record's (any record with that field).
    fn field(&mut self, rc: Core, rt: Type, name: &str, pos: Pos) -> Res<(Core, Type)> {
        match self.u.zonk(&rt) {
            Type::Con(s, args) if self.structs.contains_key(&s) => {
                let info = &self.structs[&s];
                let Some(k) = info.fields.iter().position(|(f, _)| f == name) else {
                    return Err((pos, format!("{s} has no field {name}")));
                };
                let map: HashMap<_, _> = info.vars.iter().copied().zip(args).collect();
                let t = substitute(&info.fields[k].1, &map);
                // (a struct of one field may be that field: see `struct_lit`)
                Ok((
                    if info.unboxed {
                        rc
                    } else if info.set[k] {
                        Core::Field(Box::new(rc), k)
                    } else {
                        Core::Proj(Box::new(rc), k)
                    },
                    t,
                ))
            }
            Type::Var(_) | Type::Record(_) => {
                let t = self.u.fresh();
                let rest = self.u.fresh();
                let want = Type::Record(Box::new(Type::extend(name, t.clone(), rest)));
                self.u.unify(&rt, &want).map_err(|e| (pos, if e.starts_with("missing ") { format!("{} has no field {name}", self.u.show(&rt)) } else { e }))?;
                Ok((Core::RecGet(Box::new(rc), name.to_string()), t))
            }
            other => Err((pos, format!("{} has no fields", self.u.show(&other)))),
        }
    }

    /// `r.name = v`: a struct's field set, in place (once r's type is
    /// known: see `resolve_uses`). A struct is shared, not copied, so
    /// whatever else holds it sees the change.
    fn assign_field(&mut self, r: &Expr, name: &str, v: &Expr, pos: Pos) -> Res<(Core, Type)> {
        let (recv, recv_ty) = self.infer(r)?;
        let (vc, vt) = self.infer(v)?;
        let u = Use { recv, recv_ty, name: name.to_string(), what: UseKind::Set(vc, vt), result: Type::unit(), here: self.effect.clone(), module: self.module, pos, id: 0 };
        self.use_or_wait(u)
    }

    /// A field set, its receiver's type (`ty`) as known as it'll be.
    fn set_field(&mut self, rc: Core, ty: Type, name: &str, vc: Core, vt: Type, pos: Pos) -> Res<Core> {
        match ty {
            Type::Con(s, args) if self.structs.contains_key(&s) => {
                let info = &self.structs[&s];
                let Some(k) = info.fields.iter().position(|(f, _)| f == name) else {
                    return Err((pos, format!("{s} has no field {name}")));
                };
                let map: HashMap<_, _> = info.vars.iter().copied().zip(args).collect();
                let t = substitute(&info.fields[k].1, &map);
                self.unify(&vt, &t, pos)?;
                Ok(Core::SetProj(Box::new(rc), k, Box::new(vc)))
            }
            Type::Record(_) => Err((pos, format!("a record's fields can't be set (a struct's can): {name}"))),
            Type::Var(_) => Err((pos, format!("can't tell whose field {name} this is, to set it: annotate it"))),
            other => Err((pos, format!("{} has no fields", self.u.show(&other)))),
        }
    }

    fn struct_lit(&mut self, path: &ast::Path, fields: &[(String, Expr)], pos: Pos) -> Res<(Core, Type)> {
        let Def::Item(i) = self.lookup(path, Ns::Type)? else { return Err((pos, format!("{path} isn't a struct"))) };
        let name = self.prog.items[i].name.clone();
        let Some(info) = self.structs.get(&name) else { return Err((pos, format!("{path} isn't a struct"))) };
        let vars = info.vars.clone();
        let decl = info.fields.clone();
        let unboxed = info.unboxed;
        let map: HashMap<_, _> = vars.iter().map(|&v| (v, self.u.fresh())).collect();
        // (the values in the order they're written, then the struct in its
        // fields' order)
        let mut temps: HashMap<String, String> = HashMap::default();
        let mut lets = vec![];
        for (f, v) in fields {
            let Some((_, ft)) = decl.iter().find(|(g, _)| g == f) else { return Err((v.pos, format!("{name} has no field {f}"))) };
            if temps.contains_key(f) {
                return Err((v.pos, format!("the field {f} twice")));
            }
            let (c, t) = self.infer(v)?;
            self.unify(&t, &substitute(ft, &map), v.pos)?;
            let temp = self.fresh_name(f);
            temps.insert(f.clone(), temp.clone());
            lets.push((temp, c));
        }
        let mut items = vec![];
        for (f, _) in &decl {
            let Some(t) = temps.get(f) else { return Err((pos, format!("{name} needs the field {f}"))) };
            items.push(Core::Local(t.clone()));
        }
        // A struct of one field is just that field, at no cost: a wrapper
        // (`struct Meters { m: Int }`) is as cheap as what it wraps. Unless
        // that field is ever set: then it needs a block to be set in.
        let built = if unboxed { items.pop().unwrap() } else { Core::Tuple(items) };
        let core = lets.into_iter().rev().fold(built, |body, (t, c)| Core::Let(t, Box::new(c), Box::new(body)));
        Ok((core, Type::Con(name, vars.iter().map(|v| map[v].clone()).collect())))
    }

    fn binary(&mut self, op: BinOp, a: &Expr, b: &Expr, pos: Pos) -> Res<(Core, Type)> {
        let (ac, at) = self.infer(a)?;
        let (bc, bt) = self.infer(b)?;
        // + - * / % are traits' (Add's, ...: Int's, Rational's, ...)
        let num_op = match op {
            BinOp::Add => Some(Prim::Add),
            BinOp::Sub => Some(Prim::Sub),
            BinOp::Mul => Some(Prim::Mul),
            BinOp::Div => Some(Prim::Div),
            BinOp::Rem => Some(Prim::Rem),
            _ => None,
        };
        if let Some(p) = num_op {
            self.unify(&at, &bt, pos).map_err(|(p, m)| (p, format!("this arithmetic: {m}")))?;
            return self.arith(p, vec![ac, bc], at, pos);
        }
        // the rest are Int's alone
        let int_op = |p| Some(p);
        let prim = match op {
            BinOp::BitAnd => int_op(Prim::BitAnd),
            BinOp::BitOr => int_op(Prim::BitOr),
            BinOp::BitXor => int_op(Prim::BitXor),
            BinOp::Shl => int_op(Prim::Shl),
            BinOp::Shr => int_op(Prim::Shr),
            _ => None,
        };
        if let Some(p) = prim {
            self.unify(&at, &Type::int(), a.pos)?;
            self.unify(&bt, &Type::int(), b.pos)?;
            return Ok((Core::Prim(p, vec![ac, bc]), Type::int()));
        }
        match op {
            BinOp::Concat => {
                self.unify(&at, &Type::string(), a.pos)?;
                self.unify(&bt, &Type::string(), b.pos)?;
                Ok((Core::Prim(Prim::Concat, vec![ac, bc]), Type::string()))
            }
            BinOp::And | BinOp::Or => {
                self.unify(&at, &Type::bool(), a.pos)?;
                self.unify(&bt, &Type::bool(), b.pos)?;
                let core = if op == BinOp::And {
                    Core::If(Box::new(ac), Box::new(bc), Box::new(Core::Int(0)))
                } else {
                    Core::If(Box::new(ac), Box::new(Core::Int(1)), Box::new(bc))
                };
                Ok((core, Type::bool()))
            }
            _ => {
                self.unify(&at, &bt, pos).map_err(|(p, m)| (p, format!("comparing: {m}")))?;
                let (cmp, trait_) = match op {
                    BinOp::Eq => (Cmp::Eq, EQ),
                    BinOp::Ne => (Cmp::Ne, EQ),
                    BinOp::Lt => (Cmp::Lt, ORD),
                    BinOp::Le => (Cmp::Le, ORD),
                    BinOp::Gt => (Cmp::Gt, ORD),
                    _ => (Cmp::Ge, ORD),
                };
                let hole = self.new_hole(Pred { trait_: trait_.into(), ty: at }, pos);
                Ok((Core::Compare(cmp, hole, Box::new(ac), Box::new(bc)), Type::bool()))
            }
        }
    }

    /// Arithmetic on values of type `t`: the machine's for an Int, else
    /// its trait's method (decided once `t` is known: see `finalize`).
    fn arith(&mut self, p: Prim, args: Vec<Core>, t: Type, pos: Pos) -> Res<(Core, Type)> {
        if self.u.zonk(&t) == Type::int() {
            return Ok((Core::Prim(p, args), t));
        }
        let hole = self.new_hole(Pred { trait_: arith_trait(p).0.into(), ty: t.clone() }, pos);
        Ok((Core::Arith(p, hole, args), t))
    }

    /// `handle body { return(v) => .., op(x) => .. }`
    fn handle(&mut self, body: &Expr, arms: &[ast::HandlerArm], pos: Pos) -> Res<(Core, Type)> {
        // which effect: the one the arms' operations are of
        let mut eff_item = None;
        for arm in arms {
            if arm.op.segments == ["return"] {
                continue;
            }
            match self.lookup(&arm.op, Ns::Value)? {
                Def::Op(e, _) if eff_item.is_none_or(|x| x == e) => eff_item = Some(e),
                Def::Op(..) => return Err((arm.op.pos, "a handler's operations have to be of one effect".into())),
                _ => return Err((arm.op.pos, format!("{} isn't an effect's operation", arm.op))),
            }
        }
        let Some(e) = eff_item else { return Err((pos, "a handler needs an operation to handle".into())) };
        let ename = self.prog.items[e].name.clone();
        let vars = self.effects[&ename].vars.clone();
        let args: Vec<Type> = vars.iter().map(|_| self.u.fresh()).collect();
        let map: HashMap<_, _> = vars.iter().copied().zip(args.iter().cloned()).collect();
        let outer = self.effect.clone();
        // the body may have this effect too
        self.effect = Type::extend(&ename, Type::Con(ename.clone(), args), outer.clone());
        let r = self.infer(body);
        self.effect = outer.clone();
        let (bc, bt) = r?;
        let result = self.u.fresh();
        // what the body gives back
        let ret = match arms.iter().find(|a| a.op.segments == ["return"]) {
            Some(arm) => {
                if arm.params.len() != 1 {
                    return Err((arm.op.pos, "return(v) takes one parameter".into()));
                }
                self.push_scope();
                let v = self.bind_local(&arm.params[0], bt.clone(), false, None);
                let r = self.infer(&arm.body);
                self.pop_scope();
                let (rc, rt) = r?;
                self.unify(&rt, &result, arm.body.pos)?;
                (v, Box::new(rc))
            }
            None => {
                self.unify(&bt, &result, pos)?;
                let v = self.fresh_name("v");
                (v.clone(), Box::new(Core::Local(v)))
            }
        };
        // each operation
        let n_ops = self.effects[&ename].ops.len();
        let mut ops: Vec<Option<(Vec<String>, String, Core)>> = vec![None; n_ops];
        for arm in arms {
            if arm.op.segments == ["return"] {
                continue;
            }
            let Def::Op(_, k) = self.lookup(&arm.op, Ns::Value)? else { unreachable!() };
            if ops[k].is_some() {
                return Err((arm.op.pos, format!("{} is handled twice", arm.op)));
            }
            let op = &self.effects[&ename].ops[k];
            let (own, params, op_ret) = (op.vars.clone(), op.params.clone(), op.ret.clone());
            if arm.params.len() != params.len() {
                return Err((arm.op.pos, format!("{} takes {} parameters", arm.op, params.len())));
            }
            // (the operation's own type parameters, like fail's A, are
            // whatever each place that performs it needs: here, a type the
            // clause knows nothing about, so it can't make one up to resume
            // with)
            let names_of: Vec<String> = match &self.prog.items[e].kind {
                ItemKind::Effect(d) => d.ops[k].generics.iter().map(|g| g.name.clone()).collect(),
                _ => vec![],
            };
            let mut m = map.clone();
            for (i, v) in own.into_iter().enumerate() {
                let name = names_of.get(i).cloned().unwrap_or_else(|| "A".into());
                m.insert(v, self.u.skolem(&name));
            }
            self.push_scope();
            let mut names = vec![];
            for (p, t) in arm.params.iter().zip(&params) {
                names.push(self.bind_local(p, substitute(t, &m), false, None));
            }
            // resume: carries on from the operation, with what it's given as
            // the operation's result, to what the handle gives back
            let resume_ty = Type::func(vec![substitute(&op_ret, &m)], result.clone(), outer.clone());
            let resume = self.bind_local("resume", resume_ty, false, None);
            let r = self.infer(&arm.body);
            self.pop_scope();
            let (ac, at) = r?;
            self.unify(&at, &result, arm.body.pos)?;
            ops[k] = Some((names, resume, ac));
        }
        let mut out = vec![];
        for (k, op) in ops.into_iter().enumerate() {
            match op {
                Some(op) => out.push(op),
                None => return Err((pos, format!("this handler doesn't handle {}", self.effects[&ename].ops[k].name))),
            }
        }
        Ok((Core::Handle { eff: e as i64, body: Box::new(bc), ret, ops: out }, result))
    }

    // ---- patterns

    /// Checks a pattern against the type it matches, binding its variables:
    /// its core.
    pub fn pattern(&mut self, p: &Pattern, ty: &Type) -> Res<Pat> {
        let pos = p.pos;
        Ok(match &p.kind {
            PatKind::Wild => Pat::Wild,
            PatKind::Unit => {
                self.unify(ty, &Type::unit(), pos)?;
                Pat::Wild
            }
            PatKind::Bind(name) => Pat::Bind(self.bind_local(name, ty.clone(), false, Some(pos))),
            PatKind::Int(n) => {
                self.unify(ty, &Type::int(), pos)?;
                Pat::Int(*n)
            }
            PatKind::Bool(b) => {
                self.unify(ty, &Type::bool(), pos)?;
                Pat::Con("Bool".into(), *b as i64, vec![])
            }
            PatKind::Str(s) => {
                self.unify(ty, &Type::string(), pos)?;
                Pat::Str(s.clone())
            }
            PatKind::Tuple(ps) => {
                let ts: Vec<Type> = ps.iter().map(|_| self.u.fresh()).collect();
                self.unify(ty, &Type::Tuple(ts.clone()), pos)?;
                Pat::Tuple(ps.iter().zip(&ts).map(|(p, t)| self.pattern(p, t)).collect::<Res<_>>()?)
            }
            PatKind::Ctor(path, ps) => {
                let Def::Variant(e, k) = self.lookup(path, Ns::Value)? else { return Err((pos, format!("{path} isn't a variant"))) };
                let (fields, ety) = self.variant(e, k);
                self.unify(ty, &ety, pos)?;
                if fields.len() != ps.len() {
                    return Err((pos, format!("{path} has {} fields", fields.len())));
                }
                let subs = ps.iter().zip(&fields).map(|(p, t)| self.pattern(p, t)).collect::<Res<_>>()?;
                Pat::Con(self.prog.items[e].name.clone(), k as i64, subs)
            }
            PatKind::List(items, rest) => {
                let elem = self.u.fresh();
                let list = Type::Con(LIST.into(), vec![elem.clone()]);
                self.unify(ty, &list, pos)?;
                let (nil, cons) = self.list_tags();
                let mut pat = match rest {
                    Some(r) => self.pattern(r, &list)?,
                    None => Pat::Con(LIST.into(), nil, vec![]),
                };
                let mut subs = vec![];
                for p in items {
                    subs.push(self.pattern(p, &elem)?);
                }
                for s in subs.into_iter().rev() {
                    pat = Pat::Con(LIST.into(), cons, vec![s, pat]);
                }
                pat
            }
        })
    }

    /// Whether `pats`, in order, match every value: an error if not.
    pub fn exhaustive(&self, pats: &[Pat], pos: Pos) -> Res<()> {
        let variants = |e: &str| -> Vec<usize> {
            if e == "Bool" {
                vec![0, 0]
            } else {
                self.enums[e].variants.iter().map(|(_, f)| f.len()).collect()
            }
        };
        match crate::exhaust::missing(pats, &variants) {
            None => Ok(()),
            Some(example) => Err((pos, format!("this match doesn't handle every case: for example {}", example.show(&|e, k| self.variant_name(e, k))))),
        }
    }

    fn variant_name(&self, e: &str, k: i64) -> String {
        if e == "Bool" {
            return if k == 1 { "true".into() } else { "false".into() };
        }
        self.enums[e].variants[k as usize].0.clone()
    }
}

/// A built-in function's parameters, result, and whether it has `Io`.
/// `let p = v; body`: a match with one arm, except that a tuple written
/// out and taken apart at once (`let (x, y) = (a, b)`) is never made: its
/// parts are bound to the pattern's, one by one, in order.
fn destructure(v: Core, p: Pat, body: Core) -> Core {
    match (v, p) {
        (Core::Tuple(vs), Pat::Tuple(ps)) if vs.len() == ps.len() => {
            // (from the last part in: the first is evaluated first)
            let parts: Vec<(Core, Pat)> = vs.into_iter().zip(ps).collect();
            bind_parts(parts, body)
        }
        (v, Pat::Bind(n)) => Core::Let(n, Box::new(v), Box::new(body)),
        (v, Pat::Wild) => Core::Seq(Box::new(v), Box::new(body)),
        (v, p) => Core::Match(Box::new(v), vec![(p, body)]),
    }
}

fn bind_parts(mut parts: Vec<(Core, Pat)>, body: Core) -> Core {
    if parts.is_empty() {
        return body;
    }
    let (v, p) = parts.remove(0);
    let rest = bind_parts(parts, body);
    destructure(v, p, rest)
}

fn builtin_type(name: &str, mut fresh: impl FnMut() -> Type) -> (Vec<Type>, Type, bool) {
    let (s, i, b) = (Type::string(), Type::int(), Type::bool());
    match name {
        "print" | "println" => (vec![s], Type::unit(), true),
        "read_int" => (vec![], i, true),
        "int_to_string" => (vec![i], s, false),
        "string_length" => (vec![s], i, false),
        "char_at" => (vec![s, i.clone()], i, false),
        "char_to_string" => (vec![i], s, false),
        "panic" => (vec![s], fresh(), false),
        "int_eq" | "int_lt" => (vec![i.clone(), i], b, false),
        "array" => {
            let t = fresh();
            (vec![i, t.clone()], Type::Con("Array".into(), vec![t]), false)
        }
        "array_get" => {
            let t = fresh();
            (vec![Type::Con("Array".into(), vec![t.clone()]), i], t, false)
        }
        "array_set" => {
            let t = fresh();
            (vec![Type::Con("Array".into(), vec![t.clone()]), i, t], Type::unit(), false)
        }
        "array_length" => (vec![Type::Con("Array".into(), vec![fresh()])], i, false),
        "string_eq" | "string_lt" => (vec![s.clone(), s], b, false),
        _ => unreachable!("builtin {name}"),
    }
}

fn builtin_core(name: &str, mut args: Vec<Core>) -> Core {
    let prim = |p| Core::Prim(p, args.clone());
    match name {
        "print" => prim(Prim::Print),
        "println" => Core::Seq(Box::new(prim(Prim::Print)), Box::new(Core::Prim(Prim::Print, vec![Core::Str("\n".into())]))),
        "read_int" => prim(Prim::ReadInt),
        "int_to_string" => prim(Prim::IntToString),
        "string_length" => prim(Prim::StrLength),
        "char_at" => prim(Prim::CharAt),
        "char_to_string" => prim(Prim::CharToString),
        "panic" => Core::Seq(Box::new(Core::Prim(Prim::Print, vec![args.remove(0)])), Box::new(Core::Panic(String::new()))),
        "int_eq" => prim(Prim::IntEq),
        "int_lt" => prim(Prim::IntLt),
        "string_eq" => prim(Prim::StrEq),
        "string_lt" => prim(Prim::StrLt),
        "array" => prim(Prim::ArrayNew),
        "array_get" => prim(Prim::ArrayGet),
        "array_set" => prim(Prim::ArraySet),
        "array_length" => prim(Prim::ArrayLength),
        _ => unreachable!(),
    }
}
