//! Continuation-passing style: every function gets two more parameters,
//! `k`, what to do with its result (a closure taking the result and the
//! handler stack), and `h`, the handlers in effect; and instead of
//! returning, it calls `k`. Then "the rest of the program" is a value, so:
//!
//! - `return`, `break` and `continue` call a continuation saved for them;
//! - `handle` pushes a frame on `h` with the handler's clauses and the
//!   continuation after the `handle`, and performing an operation finds the
//!   nearest frame for its effect and calls the clause, giving it `resume`:
//!   a closure that carries on from the operation (deep handlers: the frame
//!   stays in effect).
//!
//! A frame is a block: the effect's number, the return clause, where the
//! handle's result goes (its continuation and handler stack: `resume` sets
//! these to its own caller's, so the result goes back to it), the next frame
//! out, then a clause for each operation.
//!
//! The output still has nested lambdas; `codegen` turns them into closures.
//!
//! A call that does nothing (see `direct.rs`) isn't converted: it's a call
//! of the function's direct version, a value like a built-in operation's.

use crate::core::{Core, Eff, Pat, Prim};
use bf::asm::fx::HashMap;
use std::rc::Rc;

pub type Var = String;

#[derive(Clone, Debug)]
pub enum Atom {
    Var(Var),
    Int(i64),
    /// A top-level function, as a value.
    Global(String),
}

#[derive(Debug)]
pub enum Val {
    Atom(Atom),
    Str(String),
    Prim(Prim, Vec<Atom>),
    /// A block of these cells.
    Alloc(Vec<Atom>),
    /// Cell `i` of a block, which never changes once the block's made.
    Proj(Atom, usize),
    /// Cell `i` of a block that can change (set with `Set`).
    Field(Atom, usize),
    /// Sets cell `i` of a block (giving 0).
    Set(Atom, usize, Atom),
    Record(Vec<(String, Atom)>),
    RecGet(Atom, String),
    RecExtend(Atom, Vec<(String, Atom)>),
    /// The nearest frame on handler stack `h` for effect `eff`.
    FindHandler(Atom, i64),
    /// What calling a direct function gives.
    Direct(String, Vec<Atom>),
    /// A function value: its parameters (a lambda's own, then `k` and `h`;
    /// a continuation's: the value and `h`), body, and what it is.
    Lambda(Vec<Var>, Box<Term>, Kind),
}

/// What a function value is, which says how it can be called.
#[derive(Clone, Copy, Debug, PartialEq)]
pub enum Kind {
    /// One of the continuations and handler clauses CPS makes: called only
    /// in CPS.
    Internal,
    /// A lambda of the program, by number: with a direct entry too, unless
    /// it may perform operations (`false`).
    Source(usize, bool),
    /// An operation's `resume`, which the program calls as it would any
    /// function: with a direct entry that runs it to the end.
    Resume,
}

#[derive(Debug)]
pub enum Term {
    Let(Var, Val, Box<Term>),
    /// A function value that can call itself by its name: a loop.
    LetRec(Var, Vec<Var>, Box<Term>, Box<Term>),
    If(Atom, Box<Term>, Box<Term>),
    /// Calls (in tail position: the rest is in the continuation argument).
    CallGlobal(String, Vec<Atom>),
    Call(Atom, Vec<Atom>),
    Panic(String),
    /// What follows is at this place in the source (see `Core::Located`).
    Located(crate::lexer::Pos, Box<Term>),
}

pub struct Func {
    pub params: Vec<Var>,
    pub body: Term,
}

/// The continuation of an expression being converted: code to make from
/// its value and the handler stack then (`Meta`), or a continuation closure
/// to call (`Var`).
enum K<'a> {
    Meta(Box<dyn FnOnce(&mut Cps<'_>, Atom, Atom) -> Term + 'a>),
    Var(Atom),
}

/// Where `return`, `break` and `continue` go: a continuation, and the
/// handler stack to give it.
#[derive(Clone, Default)]
struct Env {
    ret: Option<(Atom, Atom)>,
    brk: Option<(Atom, Atom)>,
    cont: Option<(Atom, Atom)>,
}

type Then<'a> = Box<dyn FnOnce(&mut Cps<'_>, Vec<Atom>, Atom) -> Term + 'a>;

pub struct Cps<'d> {
    counter: usize,
    /// What calling each top-level function may do.
    own: &'d HashMap<String, Eff>,
}

impl<'d> Cps<'d> {
    pub fn new(own: &'d HashMap<String, Eff>) -> Cps<'d> {
        Cps { counter: 0, own }
    }

    /// A function's CPS version.
    pub fn function(&mut self, f: &crate::core::Func) -> Func {
        let (k, h) = (self.fresh("k"), self.fresh("h"));
        let env = Rc::new(Env { ret: Some((Atom::Var(k.clone()), Atom::Var(h.clone()))), ..Env::default() });
        let body = self.cps(&f.body, Atom::Var(h.clone()), env, K::Var(Atom::Var(k.clone())));
        let mut params = f.params.clone();
        params.extend([k, h]);
        Func { params, body }
    }

    /// A lambda (in a direct version), as a function value in CPS.
    pub fn lambda(&mut self, lam: &Core) -> Val {
        let h = Atom::Var(self.fresh("h"));
        let mut out = None;
        let t = self.cps(lam, h.clone(), Rc::new(Env::default()), meta(|_, _, _| Term::Panic(String::new())));
        if let Term::Let(_, v, _) = t {
            out = Some(v);
        }
        out.expect("a lambda is a value")
    }
}

fn meta<'a>(f: impl FnOnce(&mut Cps<'_>, Atom, Atom) -> Term + 'a) -> K<'a> {
    K::Meta(Box::new(f))
}

fn var(v: &Var) -> Atom {
    Atom::Var(v.clone())
}

/// `let name = val; rest`
fn let_(name: Var, val: Val, rest: Term) -> Term {
    Term::Let(name, val, Box::new(rest))
}

impl Cps<'_> {
    fn fresh(&mut self, base: &str) -> Var {
        self.counter += 1;
        format!("{base}%{}", self.counter)
    }

    /// Gives `v` to continuation `k`.
    fn apply(&mut self, k: K, v: Atom, h: Atom) -> Term {
        match k {
            K::Meta(f) => f(self, v, h),
            K::Var(kv) => Term::Call(kv, vec![v, h]),
        }
    }

    /// `k` as a continuation closure, for code that needs to call it from
    /// more than one place, or pass it on: `body` gets the closure.
    fn reify(&mut self, k: K, body: impl FnOnce(&mut Cps<'_>, Atom) -> Term) -> Term {
        match k {
            K::Var(kv) => body(self, kv),
            K::Meta(f) => {
                let (name, v, h) = (self.fresh("j"), self.fresh("v"), self.fresh("h"));
                let inner = f(self, var(&v), var(&h));
                let rest = body(self, var(&name));
                let_(name, Val::Lambda(vec![v, h], Box::new(inner), Kind::Internal), rest)
            }
        }
    }

    /// A value computed, given to `k`.
    fn bind(&mut self, val: Val, h: Atom, k: K) -> Term {
        let x = self.fresh("x");
        let rest = self.apply(k, var(&x), h);
        let_(x, val, rest)
    }

    /// Converts `es` in order, then gives their atoms to `then`.
    fn atoms<'a>(&mut self, es: Vec<&'a Core>, h: Atom, env: Rc<Env>, then: Then<'a>) -> Term {
        fn go<'a>(c: &mut Cps<'_>, mut es: std::vec::IntoIter<&'a Core>, mut done: Vec<Atom>, h: Atom, env: Rc<Env>, then: Then<'a>) -> Term {
            match es.next() {
                None => then(c, done, h),
                Some(e) => {
                    let env2 = env.clone();
                    c.cps(
                        e,
                        h,
                        env,
                        meta(move |c, a, h| {
                            done.push(a);
                            go(c, es, done, h, env2, then)
                        }),
                    )
                }
            }
        }
        go(self, es.into_iter(), vec![], h, env, then)
    }

    fn cps<'a>(&mut self, e: &'a Core, h: Atom, env: Rc<Env>, k: K<'a>) -> Term {
        match e {
            Core::Located(pos, e) => Term::Located(*pos, Box::new(self.cps(e, h, env, k))),
            Core::Int(n) => self.apply(k, Atom::Int(*n), h),
            Core::Str(s) => self.bind(Val::Str(s.clone()), h, k),
            Core::Local(n) => self.apply(k, var(n), h),
            Core::Lam(id, params, body, eff) => {
                let (kk, hh) = (self.fresh("k"), self.fresh("h"));
                let inner = Rc::new(Env { ret: Some((var(&kk), var(&hh))), ..Env::default() });
                let b = self.cps(body, var(&hh), inner, K::Var(var(&kk)));
                let mut ps = params.clone();
                ps.extend([kk, hh]);
                self.bind(Val::Lambda(ps, Box::new(b), Kind::Source(*id, *eff != Eff::Impure)), h, k)
            }
            Core::App(f, args, _) => {
                let env2 = env.clone();
                self.cps(
                    f,
                    h,
                    env,
                    meta(move |c, fa, h| {
                        c.atoms(
                            args.iter().collect(),
                            h,
                            env2,
                            Box::new(move |c, mut atoms, h| {
                                c.reify(k, |_, kv| {
                                    atoms.extend([kv, h]);
                                    Term::Call(fa, atoms)
                                })
                            }),
                        )
                    }),
                )
            }
            // (a call that does nothing, here or anywhere: of its direct version)
            Core::CallGlobal(name, args, eff) if *eff == Eff::Pure || self.own[name] == Eff::Pure => {
                self.atoms(args.iter().collect(), h, env, Box::new(move |c, atoms, h| c.bind(Val::Direct(name.clone(), atoms), h, k)))
            }
            Core::CallGlobal(name, args, _) => self.atoms(
                args.iter().collect(),
                h,
                env,
                Box::new(move |c, mut atoms, h| {
                    c.reify(k, |_, kv| {
                        atoms.extend([kv, h]);
                        Term::CallGlobal(name.clone(), atoms)
                    })
                }),
            ),
            Core::Let(n, v, b) => {
                let env2 = env.clone();
                self.cps(
                    v,
                    h,
                    env,
                    meta(move |c, a, h| {
                        let rest = c.cps(b, h, env2, k);
                        let_(n.clone(), Val::Atom(a), rest)
                    }),
                )
            }
            Core::If(cond, t, els) => {
                let env2 = env.clone();
                self.cps(
                    cond,
                    h,
                    env,
                    meta(move |c, ca, h| {
                        c.reify(k, |c, j| {
                            let tt = c.cps(t, h.clone(), env2.clone(), K::Var(j.clone()));
                            let et = c.cps(els, h, env2, K::Var(j));
                            Term::If(ca, Box::new(tt), Box::new(et))
                        })
                    }),
                )
            }
            Core::Match(s, arms) => {
                let env2 = env.clone();
                self.cps(s, h, env, meta(move |c, sa, h| c.reify(k, |c, j| c.arms(&sa, arms, h, env2, j))))
            }
            Core::Con(tag, args) => {
                let tag = *tag;
                self.atoms(
                    args.iter().collect(),
                    h,
                    env,
                    Box::new(move |c, atoms, h| {
                        let mut cells = vec![Atom::Int(tag)];
                        cells.extend(atoms);
                        c.bind(Val::Alloc(cells), h, k)
                    }),
                )
            }
            Core::Tuple(xs) => self.atoms(xs.iter().collect(), h, env, Box::new(move |c, atoms, h| c.bind(Val::Alloc(atoms), h, k))),
            Core::Proj(x, i) => self.cps(x, h, env, meta(move |c, a, h| c.bind(Val::Proj(a, *i), h, k))),
            Core::Field(x, i) => self.cps(x, h, env, meta(move |c, a, h| c.bind(Val::Field(a, *i), h, k))),
            Core::SetProj(x, i, v) => {
                let env2 = env.clone();
                self.cps(x, h, env, meta(move |c, xa, h| c.cps(v, h, env2, meta(move |c, va, h| c.bind(Val::Set(xa, *i, va), h, k)))))
            }
            Core::Record(fs) => {
                let labels: Vec<String> = fs.iter().map(|(l, _)| l.clone()).collect();
                self.atoms(
                    fs.iter().map(|(_, v)| v).collect(),
                    h,
                    env,
                    Box::new(move |c, atoms, h| c.bind(Val::Record(labels.into_iter().zip(atoms).collect()), h, k)),
                )
            }
            Core::RecGet(r, l) => self.cps(r, h, env, meta(move |c, a, h| c.bind(Val::RecGet(a, l.clone()), h, k))),
            Core::RecExtend(r, fs) => {
                let labels: Vec<String> = fs.iter().map(|(l, _)| l.clone()).collect();
                let env2 = env.clone();
                self.cps(
                    r,
                    h,
                    env,
                    meta(move |c, ra, h| {
                        c.atoms(
                            fs.iter().map(|(_, v)| v).collect(),
                            h,
                            env2,
                            Box::new(move |c, atoms, h| c.bind(Val::RecExtend(ra, labels.into_iter().zip(atoms).collect()), h, k)),
                        )
                    }),
                )
            }
            Core::Prim(p, args) => {
                let p = *p;
                self.atoms(args.iter().collect(), h, env, Box::new(move |c, atoms, h| c.bind(Val::Prim(p, atoms), h, k)))
            }
            Core::Seq(a, b) => {
                let env2 = env.clone();
                self.cps(a, h, env, meta(move |c, _, h| c.cps(b, h, env2, k)))
            }
            Core::NewRef(v) => self.cps(v, h, env, meta(move |c, a, h| c.bind(Val::Alloc(vec![a]), h, k))),
            Core::GetRef(r) => self.cps(r, h, env, meta(move |c, a, h| c.bind(Val::Field(a, 0), h, k))),
            Core::SetRef(r, v) => {
                let env2 = env.clone();
                self.cps(r, h, env, meta(move |c, ra, h| c.cps(v, h, env2, meta(move |c, va, h| c.bind(Val::Set(ra, 0, va), h, k)))))
            }
            Core::While(cond, body) => self.reify(k, |c, exit| c.loop_(Some(cond), body, h, &env, exit)),
            Core::Loop(body) => self.reify(k, |c, exit| c.loop_(None, body, h, &env, exit)),
            Core::Break => {
                let (kv, hv) = env.brk.clone().expect("break in a loop");
                Term::Call(kv, vec![Atom::Int(0), hv])
            }
            Core::Continue => {
                let (kv, hv) = env.cont.clone().expect("continue in a loop");
                Term::Call(kv, vec![Atom::Int(0), hv])
            }
            Core::Return(v) => {
                let (kv, hv) = env.ret.clone().expect("return in a function");
                self.cps(v, h, env, meta(move |_, a, _| Term::Call(kv, vec![a, hv])))
            }
            Core::Handle { eff, body, ret: (rv, rb), ops } => self.reify(k, |c, after| c.handle(*eff, body, rv, rb, ops, h, &env, after)),
            Core::Perform { eff, op, args } => {
                let (eff, op) = (*eff, *op);
                self.atoms(args.iter().collect(), h, env, Box::new(move |c, atoms, h| c.reify(k, |c, kv| c.perform(eff, op, atoms, h, kv))))
            }
            Core::Panic(msg) => Term::Panic(msg.clone()),
            Core::DictHole(_) | Core::MethodCall(..) | Core::Compare(..) | Core::Arith(..) | Core::DictArgs | Core::Pending(_) => unreachable!("filled in by the type checker"),
        }
    }

    /// A loop: a function that calls itself to go round again (and the
    /// condition, for `while`), with `break` going to `exit`.
    fn loop_(&mut self, cond: Option<&Core>, body: &Core, h: Atom, env: &Rc<Env>, exit: Atom) -> Term {
        let (lp, u, hl) = (self.fresh("loop"), self.fresh("u"), self.fresh("h"));
        let again = var(&lp);
        let inner = Rc::new(Env { ret: env.ret.clone(), brk: Some((exit.clone(), var(&hl))), cont: Some((again.clone(), var(&hl))) });
        let a2 = again.clone();
        let go_round = move |c: &mut Cps<'_>, h: Atom, inner: Rc<Env>| {
            c.cps(body, h, inner, meta(move |_, _, h| Term::Call(a2, vec![Atom::Int(0), h])))
        };
        let b = match cond {
            None => go_round(self, var(&hl), inner),
            Some(cond) => {
                let inner2 = inner.clone();
                self.cps(
                    cond,
                    var(&hl),
                    inner,
                    meta(move |c, ca, h| {
                        let more = go_round(c, h.clone(), inner2);
                        Term::If(ca, Box::new(more), Box::new(Term::Call(exit, vec![Atom::Int(0), h])))
                    }),
                )
            }
        };
        Term::LetRec(lp, vec![u, hl], Box::new(b), Box::new(Term::Call(again, vec![Atom::Int(0), h])))
    }

    /// `handle`: the clauses as functions, the frame, and the body run with
    /// the frame as its handler stack.
    #[allow(clippy::too_many_arguments)]
    fn handle(&mut self, eff: i64, body: &Core, rv: &str, rb: &Core, ops: &[(Vec<String>, String, Core)], h: Atom, env: &Rc<Env>, after: Atom) -> Term {
        let mut lets = vec![];
        let (rk, rh) = (self.fresh("k"), self.fresh("h"));
        let ret_body = self.cps(rb, var(&rh), env.clone(), K::Var(var(&rk)));
        let ret_clause = self.fresh("ret");
        lets.push((ret_clause.clone(), Val::Lambda(vec![rv.to_string(), rk, rh], Box::new(ret_body), Kind::Internal)));
        let mut cells = vec![Atom::Int(eff), var(&ret_clause), after, h.clone(), h];
        for (params, resume, b) in ops {
            let (ok, oh) = (self.fresh("k"), self.fresh("h"));
            let b = self.cps(b, var(&oh), env.clone(), K::Var(var(&ok)));
            let mut ps = params.clone();
            ps.extend([resume.clone(), ok, oh]);
            let name = self.fresh("op");
            lets.push((name.clone(), Val::Lambda(ps, Box::new(b), Kind::Internal)));
            cells.push(var(&name));
        }
        // what the body gives back: to the return clause, then to where the
        // frame says (the handle's continuation, or a resume's caller's)
        let frame = self.fresh("frame");
        let fa = var(&frame);
        let (bv, bh, r, tk, th) = (self.fresh("v"), self.fresh("h"), self.fresh("r"), self.fresh("k"), self.fresh("h"));
        let body_k = let_(
            r.clone(),
            Val::Proj(fa.clone(), 1),
            // (where it goes is set by each resume: see `perform`)
            let_(tk.clone(), Val::Field(fa.clone(), 2), let_(th.clone(), Val::Field(fa.clone(), 3), Term::Call(var(&r), vec![var(&bv), var(&tk), var(&th)]))),
        );
        let kb = self.fresh("kb");
        let run = self.cps(body, fa, env.clone(), K::Var(var(&kb)));
        let mut term = let_(frame, Val::Alloc(cells), let_(kb, Val::Lambda(vec![bv, bh], Box::new(body_k), Kind::Internal), run));
        for (name, val) in lets.into_iter().rev() {
            term = let_(name, val, term);
        }
        term
    }

    /// Performing an operation: the nearest frame for its effect, and its
    /// clause, called with `resume` and the frame's continuation.
    fn perform(&mut self, eff: i64, op: usize, mut args: Vec<Atom>, h: Atom, kv: Atom) -> Term {
        let (fr, x, k2, h2) = (self.fresh("frame"), self.fresh("x"), self.fresh("k"), self.fresh("h"));
        let fa = var(&fr);
        // resume: the handle's result goes to resume's caller from now on;
        // then carry on from the operation, with its handlers
        let (s1, s2) = (self.fresh("_"), self.fresh("_"));
        let resume_body = let_(
            s1,
            Val::Set(fa.clone(), 2, var(&k2)),
            let_(s2, Val::Set(fa.clone(), 3, var(&h2)), Term::Call(kv, vec![var(&x), h.clone()])),
        );
        let (resume, clause, tk, th) = (self.fresh("resume"), self.fresh("clause"), self.fresh("k"), self.fresh("h"));
        args.extend([var(&resume), var(&tk), var(&th)]);
        let_(
            fr,
            Val::FindHandler(h, eff),
            let_(
                resume,
                Val::Lambda(vec![x, k2, h2], Box::new(resume_body), Kind::Resume),
                let_(
                    clause.clone(),
                    Val::Proj(fa.clone(), 5 + op),
                    let_(tk, Val::Field(fa.clone(), 2), let_(th, Val::Field(fa, 3), Term::Call(var(&clause), args))),
                ),
            ),
        )
    }

    /// A match's arms, on scrutinee `s`, each going to `j`: an arm's tests,
    /// and if one fails, the next arm (a continuation, so each failing test
    /// can go there without a copy of the rest).
    fn arms(&mut self, s: &Atom, arms: &[(Pat, Core)], h: Atom, env: Rc<Env>, j: Atom) -> Term {
        let Some(((pat, body), rest)) = arms.split_first() else {
            return Term::Panic("no pattern matched".into());
        };
        let (next, u, hn) = (self.fresh("next"), self.fresh("u"), self.fresh("h"));
        let rest_term = self.arms(s, rest, var(&hn), env.clone(), j.clone());
        let fail = Term::Call(var(&next), vec![Atom::Int(0), h.clone()]);
        let test = self.test(pat, s.clone(), &fail, &mut |c| c.cps(body, h.clone(), env.clone(), K::Var(j.clone())));
        let_(next, Val::Lambda(vec![u, hn], Box::new(rest_term), Kind::Internal), test)
    }

    /// Code that checks `v` against `pat`, binding its variables: `success`
    /// if it matches, else `fail`.
    fn test(&mut self, pat: &Pat, v: Atom, fail: &Term, success: &mut dyn FnMut(&mut Cps<'_>) -> Term) -> Term {
        match pat {
            Pat::Wild => success(self),
            Pat::Bind(n) => {
                let rest = success(self);
                let_(n.clone(), Val::Atom(v), rest)
            }
            Pat::Int(n) => self.check(Val::Prim(Prim::IntEq, vec![v, Atom::Int(*n)]), fail, success),
            // (a Bool is a number, not a block)
            Pat::Con(e, k, subs) if e == "Bool" && subs.is_empty() => self.check(Val::Prim(Prim::IntEq, vec![v, Atom::Int(*k)]), fail, success),
            Pat::Str(s) => {
                let t = self.fresh("s");
                let inner = self.check(Val::Prim(Prim::StrEq, vec![v, var(&t)]), fail, success);
                let_(t, Val::Str(s.clone()), inner)
            }
            Pat::Con(_, k, subs) => {
                // the variant number, then the fields
                let tag = self.fresh("tag");
                let v2 = v.clone();
                let inner = self.check(Val::Prim(Prim::IntEq, vec![var(&tag), Atom::Int(*k)]), fail, &mut |c| c.fields(&v2, subs, 1, fail, success));
                let_(tag, Val::Proj(v, 0), inner)
            }
            Pat::Tuple(subs) => self.fields(&v, subs, 0, fail, success),
        }
    }

    /// The fields of block `v` from cell `first`, checked against `subs`.
    fn fields(&mut self, v: &Atom, subs: &[Pat], first: usize, fail: &Term, success: &mut dyn FnMut(&mut Cps<'_>) -> Term) -> Term {
        let Some((p, rest)) = subs.split_first() else { return success(self) };
        let x = self.fresh("f");
        let inner = self.test(p, var(&x), fail, &mut |c| c.fields(v, rest, first + 1, fail, success));
        let_(x, Val::Proj(v.clone(), first), inner)
    }

    /// `success` if `cond`, else `fail`.
    fn check(&mut self, cond: Val, fail: &Term, success: &mut dyn FnMut(&mut Cps<'_>) -> Term) -> Term {
        let c = self.fresh("c");
        let yes = success(self);
        let_(c.clone(), cond, Term::If(var(&c), Box::new(yes), Box::new(dup(fail))))
    }
}

/// A copy of a failure (a call of the next arm).
fn dup(t: &Term) -> Term {
    match t {
        Term::Call(f, args) => Term::Call(f.clone(), args.clone()),
        _ => unreachable!("failures are calls"),
    }
}
