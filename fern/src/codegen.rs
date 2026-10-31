//! The program into a `bf::ir::Program`.
//!
//! - Each function's versions (see `direct.rs`): a CPS one (`f12`), from
//!   `cps`, and a direct one (`d12`), compiled straight from the core
//!   language to an IR function, with loops as loops, called and returning
//!   as usual.
//! - Closure conversion: each lambda becomes a function of its own, taking
//!   its closure first; a lambda's value is a block: the function's address,
//!   then the variables it uses from outside (which its function reads back
//!   out of the closure). A lambda of the program has two entries, so its
//!   block starts with both: the CPS one (`s12`), and the direct one (`t12`,
//!   or 0 if it may perform operations); and the variables it uses are the
//!   same for both, worked out from its core.
//! - Calls: in CPS every call is a tail call, so the VM's stack would only
//!   grow. Each call counts how deep it is, and past `DEPTH` it returns the
//!   call (a "thunk") instead, all the way out to the trampoline, which makes
//!   it there. That's `main`'s, or, for a direct version that has to run CPS
//!   code (its body has a `handle`), one of its own.
//! - The runtime: strings (a length, then a character a cell), arrays (a
//!   length, then an element a cell), records (a field count, then each
//!   label's number and value), finding a handler, and making thunks'
//!   calls, written in the IR itself.
//! - `extern fn`s are the IR's external functions: C, called by name.

use crate::core::{Core, Eff, Pat, Prim};
use crate::cps::{Atom, Cps, Kind, Term, Val, Var};
use crate::direct::{children, compilable, free_locals, lambdas, only_through_refs};
use bf::ir::{Expr, Func as IrFunc, Program, Var as IrVar};
use bf::asm::fx::{HashMap, HashSet};
use std::collections::{BTreeMap, BTreeSet};

/// How deep calls go before returning to the trampoline.
const DEPTH: i64 = 100;

/// A function after closure conversion: no lambdas left in its body.
struct Flat {
    name: String,
    params: Vec<Var>,
    body: Term,
    /// The function it's (part of), by full name: for where a runtime error
    /// is.
    origin: String,
}

struct Gen<'c> {
    /// The function being worked on, by full name; the function each lambda
    /// is in (by number); and the one being emitted (for the messages of
    /// runtime errors, which say which function they're in).
    current: String,
    origins: HashMap<usize, String>,
    here: std::cell::RefCell<String>,
    /// Where in the source the code being emitted is, as far as it's been
    /// said (see `Core::Located`), and the files, by number.
    pos: std::cell::RefCell<Option<crate::lexer::Pos>>,
    files: &'c [String],
    /// The functions runtime errors have said they're in, by number (see
    /// `fail`).
    failing: std::cell::RefCell<Vec<String>>,
    /// IR names (at most 13 characters) of functions' CPS versions, and of
    /// their direct versions, by full name.
    names: HashMap<String, String>,
    direct_names: HashMap<String, String>,
    funcs: HashMap<String, &'c crate::core::Func>,
    /// Top-level functions' numbers of parameters.
    arity: HashMap<String, usize>,
    flats: Vec<Flat>,
    /// Top-level functions used as values (each needs a wrapper closure).
    wrapped: BTreeSet<String>,
    labels: BTreeMap<String, i64>,
    lambdas: usize,
    max_args: usize,
    /// The external functions: names and numbers of parameters.
    externs: Vec<(String, usize)>,
    /// The program's lambdas (`Core::Lam`s), by number, and those whose CPS
    /// entry has been made.
    source: HashMap<usize, &'c Core>,
    lifted: BTreeSet<usize>,
    /// The `resume`s' functions' numbers (each has a direct entry, `a12`).
    resumes: Vec<usize>,
}

/// A function's label: `unique` (its number, which is all it needs), and as
/// much of its name as fits, for whoever reads the C or a profile of it (a
/// label is at most 13 characters: see `bf::ir`).
fn label(unique: &str, name: &str) -> String {
    let base = name.rsplit("::").next().unwrap_or(name);
    let room = 13usize.saturating_sub(unique.len() + 1);
    let part: String = base.chars().filter(|c| c.is_ascii_alphanumeric() || *c == '_').take(room).collect();
    if part.is_empty() { unique.to_string() } else { format!("{unique}_{part}") }
}

pub fn generate<'c>(funcs: &'c [crate::core::Func], main: &str, effect_names: &HashMap<i64, String>, externs: Vec<(String, usize)>, files: &'c [String]) -> Program {
    let mut g = Gen {
        current: String::new(),
        origins: HashMap::default(),
        here: Default::default(),
        pos: Default::default(),
        files,
        failing: Default::default(),
        names: HashMap::default(),
        direct_names: HashMap::default(),
        funcs: HashMap::default(),
        arity: HashMap::default(),
        flats: vec![],
        wrapped: BTreeSet::new(),
        labels: BTreeMap::new(),
        lambdas: 0,
        max_args: 0,
        externs,
        source: HashMap::default(),
        lifted: BTreeSet::new(),
        resumes: vec![],
    };
    let own: HashMap<String, Eff> = funcs.iter().map(|f| (f.name.clone(), f.eff.clone())).collect();
    // (a CPS version: for calls that may perform operations, and for a
    // direct version that has to run one)
    let needs_cps = |f: &crate::core::Func| f.eff != Eff::Pure || !compilable(&f.body);
    for (i, f) in funcs.iter().enumerate() {
        if needs_cps(f) {
            g.names.insert(f.name.clone(), label(&format!("f{i}"), &f.name));
            g.arity.insert(f.name.clone(), f.params.len());
        }
        if f.eff != Eff::Impure {
            g.direct_names.insert(f.name.clone(), label(&format!("d{i}"), &f.name));
        }
        g.funcs.insert(f.name.clone(), f);
        g.note_labels(&f.body);
        g.current = f.name.clone();
        g.find_lambdas(&f.body);
    }
    let mut cps = Cps::new(&own);
    for f in funcs.iter().filter(|f| needs_cps(f)) {
        let c = cps.function(f);
        g.current = f.name.clone();
        let body = g.convert(c.body);
        let name = g.names[&f.name].clone();
        g.flats.push(Flat { name, params: c.params, body, origin: f.name.clone() });
    }
    // the lambdas direct code makes need CPS entries too: from the direct
    // versions' bodies, and the direct entries' (of lambdas already made,
    // and so on)
    let mut todo: Vec<(&'c Core, String)> = funcs.iter().filter(|f| f.eff != Eff::Impure && compilable(&f.body)).map(|f| (&f.body, f.name.clone())).collect();
    let mut scanned = HashSet::default();
    loop {
        while let Some((body, origin)) = todo.pop() {
            g.current = origin;
            let mut lams = vec![];
            lambdas(body, &mut lams);
            for lam in lams {
                let Core::Lam(id, ..) = lam else { unreachable!() };
                if !g.lifted.contains(id) {
                    let Val::Lambda(ps, b, kind) = cps.lambda(lam) else { unreachable!("a lambda") };
                    g.lift(None, ps, *b, kind);
                }
            }
        }
        let next: Vec<usize> = g.lifted.iter().filter(|id| !scanned.contains(*id)).copied().collect();
        if next.is_empty() {
            break;
        }
        for id in next {
            scanned.insert(id);
            let Core::Lam(_, _, body, eff) = g.source[&id] else { unreachable!() };
            if *eff != Eff::Impure && compilable(body) {
                todo.push((body, g.origins[&id].clone()));
            }
        }
    }
    // wrappers: closures for top-level functions used as values
    for name in g.wrapped.clone() {
        let n = g.arity[&name];
        let params: Vec<Var> = (0..n).map(|i| format!("p{i}")).collect();
        let mut all = vec!["env".to_string()];
        all.extend(params.iter().cloned());
        let body = Term::CallGlobal(name.clone(), params.iter().map(|p| Atom::Var(p.clone())).collect());
        g.max_args = g.max_args.max(n);
        g.flats.push(Flat { name: wrapper_name(&g.names[&name]), params: all, body, origin: name.clone() });
    }
    g.max_args = g.max_args.max(2) + 1;
    bf::log!(bf::asm::log::DEBUG, "{} direct versions, {} in CPS, {} lambdas", g.direct_names.len(), g.names.len(), g.source.len());
    g.emit(main, effect_names)
}

fn wrapper_name(ir: &str) -> String {
    format!("w{}", &ir[1..])
}

impl<'c> Gen<'c> {
    /// Closure conversion of a term: its lambdas lifted out, each a block
    /// made where the lambda was.
    fn convert(&mut self, t: Term) -> Term {
        match t {
            Term::Located(pos, t) => Term::Located(pos, Box::new(self.convert(*t))),
            Term::Let(x, Val::Lambda(params, body, kind), rest) => {
                let alloc = self.lift(None, params, *body, kind);
                Term::Let(x, alloc, Box::new(self.convert(*rest)))
            }
            Term::Let(x, v, rest) => {
                self.note(&v);
                Term::Let(x, v, Box::new(self.convert(*rest)))
            }
            Term::LetRec(x, params, body, rest) => {
                let alloc = self.lift(Some(x.clone()), params, *body, Kind::Internal);
                Term::Let(x, alloc, Box::new(self.convert(*rest)))
            }
            Term::If(c, a, b) => {
                self.note_atom(&c);
                Term::If(c, Box::new(self.convert(*a)), Box::new(self.convert(*b)))
            }
            Term::CallGlobal(f, args) => {
                args.iter().for_each(|a| self.note_atom(a));
                self.max_args = self.max_args.max(args.len());
                Term::CallGlobal(f, args)
            }
            Term::Call(f, args) => {
                self.note_atom(&f);
                args.iter().for_each(|a| self.note_atom(a));
                self.max_args = self.max_args.max(args.len() + 1);
                Term::Call(f, args)
            }
            t @ Term::Panic(_) => t,
        }
    }

    /// Lifts a lambda (called `me` inside itself, if it's recursive) to a
    /// function of its own: the block that's its closure. (A lambda of the
    /// program is lifted once, however many times it's met.)
    fn lift(&mut self, me: Option<Var>, params: Vec<Var>, body: Term, kind: Kind) -> Val {
        let free = match kind {
            Kind::Source(id, _) => free_locals(self.source[&id]),
            _ => {
                let mut bound: HashSet<Var> = params.iter().cloned().chain(me.clone()).collect();
                let mut free = vec![];
                free_vars(&body, &mut bound, &mut free);
                free
            }
        };
        let (name, direct) = match kind {
            Kind::Source(id, direct) => (format!("s{id}"), Some(if direct { Atom::Global(format!("@t{id}")) } else { Atom::Int(0) })),
            Kind::Resume => {
                self.lambdas += 1;
                self.resumes.push(self.lambdas);
                (format!("l{}", self.lambdas), Some(Atom::Global(format!("@a{}", self.lambdas))))
            }
            Kind::Internal => {
                self.lambdas += 1;
                (format!("l{}", self.lambdas), None)
            }
        };
        let first = if direct.is_some() { 2 } else { 1 };
        let new = match kind {
            Kind::Source(id, _) => self.lifted.insert(id),
            _ => true,
        };
        if new {
            // the body: the closure's variables read back, then the lambda's
            let env = format!("env%{name}");
            let mut inner = self.convert(body);
            for (i, v) in free.iter().enumerate().rev() {
                inner = Term::Let(v.clone(), Val::Proj(Atom::Var(env.clone()), i + first), Box::new(inner));
            }
            if let Some(m) = me {
                inner = Term::Let(m, Val::Atom(Atom::Var(env.clone())), Box::new(inner));
            }
            let mut ps = vec![env];
            ps.extend(params);
            let origin = match kind {
                Kind::Source(id, _) => self.origins.get(&id).cloned().unwrap_or_else(|| self.current.clone()),
                _ => self.current.clone(),
            };
            self.flats.push(Flat { name: name.clone(), params: ps, body: inner, origin });
        }
        let mut cells = vec![Atom::Global(format!("@{name}"))];
        cells.extend(direct);
        cells.extend(free.into_iter().map(Atom::Var));
        Val::Alloc(cells)
    }

    /// Notes the program's lambdas in `e`, by number.
    fn find_lambdas(&mut self, e: &'c Core) {
        if let Core::Lam(id, ..) = e {
            self.source.insert(*id, e);
            self.origins.entry(*id).or_insert_with(|| self.current.clone());
        }
        for c in children(e) {
            self.find_lambdas(c);
        }
    }

    /// Notes what a value needs: wrappers for functions used as values, and
    /// numbers for record labels.
    fn note(&mut self, v: &Val) {
        match v {
            Val::Atom(a) | Val::Proj(a, _) | Val::Field(a, _) | Val::FindHandler(a, _) => self.note_atom(a),
            Val::Prim(_, args) | Val::Alloc(args) | Val::Direct(_, args) => args.iter().for_each(|a| self.note_atom(a)),
            Val::Set(a, _, b) => {
                self.note_atom(a);
                self.note_atom(b);
            }
            Val::Record(fs) => fs.iter().for_each(|(l, a)| {
                self.label(l);
                self.note_atom(a);
            }),
            Val::RecGet(a, l) => {
                self.label(l);
                self.note_atom(a);
            }
            Val::RecExtend(a, fs) => {
                self.note_atom(a);
                fs.iter().for_each(|(l, b)| {
                    self.label(l);
                    self.note_atom(b);
                });
            }
            Val::Str(_) | Val::Lambda(..) => {}
        }
    }

    fn note_atom(&mut self, a: &Atom) {
        if let Atom::Global(g) = a {
            if !g.starts_with('@') {
                self.wrapped.insert(g.clone());
            }
        }
    }

    /// Numbers for the record labels a direct function uses.
    fn note_labels(&mut self, e: &Core) {
        match e {
            Core::Record(fs) | Core::RecExtend(_, fs) => fs.iter().for_each(|(l, _)| {
                self.label(l);
            }),
            Core::RecGet(_, l) => {
                self.label(l);
            }
            _ => {}
        }
        for c in children(e) {
            self.note_labels(c);
        }
    }

    fn label(&mut self, l: &str) -> i64 {
        let n = self.labels.len() as i64 + 1;
        *self.labels.entry(l.to_string()).or_insert(n)
    }

    // ---- the IR

    /// The functions `main` (by IR name) can reach (the rest, unused parts
    /// of the standard library say, aren't emitted).
    fn reachable(&self, main: &str) -> HashSet<String> {
        let by_name: HashMap<&str, &Flat> = self.flats.iter().map(|f| (f.name.as_str(), f)).collect();
        let direct: HashMap<&str, &str> = self.direct_names.iter().map(|(full, ir)| (ir.as_str(), full.as_str())).collect();
        let mut seen = HashSet::default();
        let mut todo = vec![main.to_string()];
        while let Some(n) = todo.pop() {
            if !seen.insert(n.clone()) {
                continue;
            }
            let mut out = vec![];
            if let Some(f) = by_name.get(n.as_str()) {
                self.refs(&f.body, &mut out);
            } else if let Some(full) = direct.get(n.as_str()) {
                let body = &self.funcs[*full].body;
                if compilable(body) {
                    self.direct_refs(body, &mut out);
                } else {
                    out.push(self.names[*full].clone());
                }
            } else if let Some(id) = n.strip_prefix('t').and_then(|k| k.parse::<usize>().ok()) {
                let Core::Lam(_, _, body, _) = self.source[&id] else { unreachable!() };
                if compilable(body) {
                    self.direct_refs(body, &mut out);
                } else {
                    out.push(format!("s{id}"));
                }
            } else if let Some(k) = n.strip_prefix('a') {
                out.push(format!("l{k}"));
            }
            todo.extend(out);
        }
        seen
    }

    /// The functions direct code `e` names.
    fn direct_refs(&self, e: &Core, out: &mut Vec<String>) {
        match e {
            Core::CallGlobal(g, args, _) => {
                out.push(self.direct_name(g).to_string());
                args.iter().for_each(|a| self.direct_refs(a, out));
            }
            Core::Lam(id, _, _, eff) => {
                out.push(format!("s{id}"));
                if *eff != Eff::Impure {
                    out.push(format!("t{id}"));
                }
            }
            _ => children(e).into_iter().for_each(|c| self.direct_refs(c, out)),
        }
    }

    fn direct_name(&self, g: &str) -> &str {
        self.direct_names.get(g).unwrap_or_else(|| panic!("{g} has no direct version"))
    }

    /// The functions a term names.
    fn refs(&self, t: &Term, out: &mut Vec<String>) {
        let atom = |a: &Atom, out: &mut Vec<String>| {
            if let Atom::Global(g) = a {
                match g.strip_prefix('@') {
                    Some(lambda) => out.push(lambda.to_string()),
                    None => out.push(wrapper_name(&self.names[g])),
                }
            }
        };
        match t {
            Term::Located(_, t) => self.refs(t, out),
            Term::Let(_, v, rest) => {
                match v {
                    Val::Atom(a) | Val::Proj(a, _) | Val::Field(a, _) | Val::FindHandler(a, _) | Val::RecGet(a, _) => atom(a, out),
                    Val::Prim(_, args) | Val::Alloc(args) => args.iter().for_each(|a| atom(a, out)),
                    Val::Direct(g, args) => {
                        out.push(self.direct_name(g).to_string());
                        args.iter().for_each(|a| atom(a, out));
                    }
                    Val::Set(a, _, b) => {
                        atom(a, out);
                        atom(b, out);
                    }
                    Val::Record(fs) => fs.iter().for_each(|(_, a)| atom(a, out)),
                    Val::RecExtend(a, fs) => {
                        atom(a, out);
                        fs.iter().for_each(|(_, b)| atom(b, out));
                    }
                    Val::Str(_) | Val::Lambda(..) => {}
                }
                self.refs(rest, out);
            }
            Term::If(c, a, b) => {
                atom(c, out);
                self.refs(a, out);
                self.refs(b, out);
            }
            Term::CallGlobal(g, args) => {
                out.push(self.names[g].clone());
                args.iter().for_each(|a| atom(a, out));
            }
            Term::Call(c, args) => {
                atom(c, out);
                args.iter().for_each(|a| atom(a, out));
            }
            Term::Panic(_) | Term::LetRec(..) => {}
        }
    }

    fn emit(&self, main: &str, effect_names: &HashMap<i64, String>) -> Program {
        let mut p = Program::new();
        for (name, params) in &self.externs {
            p.external(name, *params);
        }
        let depth = p.global(1);
        let result = p.global(1);
        let direct_main = self.funcs[main].eff != Eff::Impure;
        let main_ir = if direct_main { self.direct_name(main).to_string() } else { self.names[main].clone() };
        let reachable = self.reachable(&main_ir);
        for flat in self.flats.iter().filter(|f| reachable.contains(&f.name)) {
            let params: Vec<&str> = flat.params.iter().map(|s| s.as_str()).collect();
            *self.here.borrow_mut() = flat.origin.clone();
            *self.pos.borrow_mut() = None;
            p.function(&flat.name, &params, |f| {
                let mut env: HashMap<Var, Expr> = flat.params.iter().map(|n| (n.clone(), f.once(f.arg(n)))).collect();
                self.term(f, &flat.body, &mut env, &depth);
            });
        }
        // direct versions: compiled from the core, or running the CPS version
        for (full, name) in self.direct_names.iter().filter(|(_, n)| reachable.contains(*n)) {
            let func = self.funcs[full];
            let params: Vec<&str> = func.params.iter().map(|s| s.as_str()).collect();
            *self.here.borrow_mut() = full.clone();
            *self.pos.borrow_mut() = None;
            p.function(name, &params, |f| {
                let args: Vec<Expr> = func.params.iter().map(|n| f.once(f.arg(n))).collect();
                let v = if compilable(&func.body) {
                    let mut env: HashMap<String, Local> = func.params.iter().cloned().zip(args.into_iter().map(Local::Value)).collect();
                    self.direct(f, &func.body, &mut env)
                } else {
                    let cps = self.names[full].clone();
                    run_to_end(f, &depth, &result, |f, k| f.call(&cps, args.into_iter().chain([k, 0.into()]).collect::<Vec<Expr>>()).into())
                };
                f.ret(v);
            });
        }
        // lambdas' direct entries: likewise
        for &id in &self.lifted {
            let name = format!("t{id}");
            if !reachable.contains(&name) {
                continue;
            }
            let lam = self.source[&id];
            let Core::Lam(_, ps, body, _) = lam else { unreachable!() };
            let mut params = vec!["env"];
            params.extend(ps.iter().map(|s| s.as_str()));
            *self.here.borrow_mut() = self.origins.get(&id).cloned().unwrap_or_default();
            *self.pos.borrow_mut() = None;
            p.function(&name, &params, |f| {
                let closure = f.once(f.arg("env"));
                let args: Vec<Expr> = ps.iter().map(|n| f.once(f.arg(n))).collect();
                let v = if compilable(body) {
                    let mut env: HashMap<String, Local> = HashMap::default();
                    for (i, v) in free_locals(lam).into_iter().enumerate() {
                        let x = f.once(closure.at(i as i64 + 2));
                        env.insert(v, Local::Value(x));
                    }
                    env.extend(ps.iter().cloned().zip(args.into_iter().map(Local::Value)));
                    self.direct(f, body, &mut env)
                } else {
                    let all: Vec<Expr> = std::iter::once(closure.clone()).chain(args).collect();
                    run_to_end(f, &depth, &result, |f, k| f.call(&format!("s{id}"), all.into_iter().chain([k, 0.into()]).collect::<Vec<Expr>>()).into())
                };
                f.ret(v);
            });
        }
        // a resume's: carrying on from the operation, to the end
        for &n in &self.resumes {
            let name = format!("a{n}");
            if !reachable.contains(&name) {
                continue;
            }
            p.function(&name, &["env", "x"], |f| {
                let (env, x) = (f.once(f.arg("env")), f.once(f.arg("x")));
                let v = run_to_end(f, &depth, &result, |f, k| f.call(&format!("l{n}"), vec![env, x, k, 0.into()]).into());
                f.ret(v);
            });
        }
        // (what prints runtime errors, if anything can have one)
        if !self.failing.borrow().is_empty() {
            self.where_function(&mut p);
        }
        runtime(&mut p, self.max_args, effect_names);
        // a call with n arguments, or the thunk of one (see `tail_call`)
        for n in 0..=self.max_args {
            let mut params = vec!["addr".to_string()];
            params.extend((0..n).map(|i| format!("a{i}")));
            let ps: Vec<&str> = params.iter().map(|s| s.as_str()).collect();
            let d2 = depth.clone();
            p.function(&format!("rt_tc{n}"), &ps, move |f| {
                let addr = f.arg("addr");
                let args: Vec<Expr> = (0..n).map(|i| Expr::from(f.arg(&format!("a{i}")))).collect();
                f.set(d2.at(0), d2.at(0) + 1);
                f.if_(d2.at(0).gt(DEPTH), |f| {
                    let t = f.gc_alloc(n as i64 + 2);
                    f.set(t.at(0), n as i64);
                    f.set(t.at(1), addr);
                    for (i, a) in args.iter().enumerate() {
                        f.set(t.at(i as i64 + 2), a.clone());
                    }
                    f.ret(t);
                });
                let r = f.call_at(addr, args.clone());
                f.ret(r);
            });
        }
        // the end of a run of CPS code: where its result goes
        let r2 = result.clone();
        p.function("halt", &["env", "v", "h"], move |f| {
            f.set(r2.at(0), f.arg("v"));
            f.ret(0);
        });
        if direct_main {
            p.main(move |f| {
                f.call(&main_ir, Vec::<Expr>::new());
            });
        } else {
            p.main(move |f| {
                run_to_end(f, &depth, &result, |f, k| f.call(&main_ir, (k, 0)).into());
            });
        }
        p
    }

    fn atom(&self, f: &mut IrFunc, a: &Atom, env: &HashMap<Var, Expr>) -> Expr {
        match a {
            Atom::Var(v) => env.get(v).unwrap_or_else(|| panic!("no variable {v}")).clone(),
            Atom::Int(n) => (*n).into(),
            Atom::Global(g) if g.starts_with('@') => f.func_addr(&g[1..]),
            // a top-level function as a value: a closure of its wrapper
            Atom::Global(g) => {
                let c = f.gc_alloc(1);
                let w = f.func_addr(&wrapper_name(&self.names[g]));
                f.set(c.at(0), w);
                c.into()
            }
        }
    }

    fn term(&self, f: &mut IrFunc, t: &Term, env: &mut HashMap<Var, Expr>, depth: &Expr) {
        match t {
            Term::Located(pos, t) => {
                *self.pos.borrow_mut() = Some(*pos);
                self.term(f, t, env, depth);
            }
            Term::Let(x, v, rest) => {
                let value = self.val(f, v, env);
                env.insert(x.clone(), value);
                self.term(f, rest, env, depth);
            }
            Term::If(c, a, b) => {
                let c = self.atom(f, c, env);
                f.if_else(
                    c,
                    |f| self.term(f, a, &mut env.clone(), depth),
                    |f| self.term(f, b, &mut env.clone(), depth),
                );
            }
            Term::CallGlobal(g, args) => {
                let args: Vec<Expr> = args.iter().map(|a| self.atom(f, a, env)).collect();
                let name = self.names.get(g).unwrap_or_else(|| panic!("no function {g}")).clone();
                let addr = f.func_addr(&name);
                self.tail_call(f, addr, args);
            }
            Term::Call(c, args) => {
                let c = self.atom(f, c, env);
                let c = f.once(c);
                let mut all = vec![c.clone()];
                all.extend(args.iter().map(|a| self.atom(f, a, env)));
                self.tail_call(f, c.at(0), all);
            }
            Term::Panic(m) => self.panic(f, m),
            Term::LetRec(..) => unreachable!("converted"),
        }
    }

    /// A call, through the runtime's `rt_tc{n}`: it makes the call, or if
    /// calls have gone deep, returns it as a thunk to the trampoline.
    fn tail_call(&self, f: &mut IrFunc, addr: Expr, args: Vec<Expr>) {
        let mut all = vec![addr];
        all.extend(args.iter().cloned());
        let r = f.call(&format!("rt_tc{}", args.len()), all);
        f.ret(r);
    }

    fn val(&self, f: &mut IrFunc, v: &Val, env: &HashMap<Var, Expr>) -> Expr {
        let a = |f: &mut IrFunc, x: &Atom| self.atom(f, x, env);
        match v {
            Val::Atom(x) => a(f, x),
            Val::Alloc(cells) => {
                let b = f.gc_alloc(cells.len() as i64);
                for (i, c) in cells.iter().enumerate() {
                    let c = a(f, c);
                    f.set(b.at(i as i64), c);
                }
                b.into()
            }
            Val::Proj(x, i) => {
                let x = a(f, x);
                f.once(x.fixed_at(*i as i64))
            }
            Val::Field(x, i) => {
                let x = a(f, x);
                f.once(x.at(*i as i64))
            }
            Val::Set(x, i, y) => {
                let (x, y) = (a(f, x), a(f, y));
                f.set(x.at(*i as i64), y);
                0.into()
            }
            Val::Record(fs) => {
                let b = f.gc_alloc(fs.len() as i64 * 2 + 1);
                f.set(b.at(0), fs.len() as i64);
                for (i, (l, x)) in fs.iter().enumerate() {
                    let x = a(f, x);
                    f.set(b.at(2 * i as i64 + 1), self.labels[l]);
                    f.set(b.at(2 * i as i64 + 2), x);
                }
                b.into()
            }
            Val::RecGet(r, l) => {
                let r = a(f, r);
                f.call("rt_recget", (r, self.labels[l])).into()
            }
            Val::RecExtend(r, fs) => {
                // (the fields in front, the first frontmost)
                let mut r = a(f, r);
                for (l, x) in fs.iter().rev() {
                    let x = a(f, x);
                    r = f.call("rt_recext", (r, self.labels[l], x)).into();
                }
                r
            }
            Val::FindHandler(h, eff) => {
                let h = a(f, h);
                f.call("rt_find", (h, *eff)).into()
            }
            Val::Direct(g, args) => {
                let args: Vec<Expr> = args.iter().map(|x| a(f, x)).collect();
                f.call(self.direct_name(g), args).into()
            }
            Val::Str(s) => string(f, s),
            Val::Prim(p, args) => {
                let args: Vec<Expr> = args.iter().map(|x| a(f, x)).collect();
                self.prim(f, *p, args)
            }
            Val::Lambda(..) => unreachable!("converted"),
        }
    }

    /// Says a runtime error (one of `FAILURES`), and where it is: the place
    /// in the source and the function, which `rt_where` prints from their
    /// numbers, and stops the program (so each place costs one call, not the
    /// printing of its own message and then stopping).
    fn fail(&self, f: &mut IrFunc, what: &str) {
        let kind = FAILURES.iter().position(|m| *m == what).expect("one of FAILURES") as i64;
        let function = self.here.borrow().trim_start_matches("::").to_string();
        let mut failing = self.failing.borrow_mut();
        let func = match failing.iter().position(|n| *n == function) {
            Some(k) => k,
            None => {
                failing.push(function);
                failing.len() - 1
            }
        } as i64;
        // (all in one number, so each place costs one argument: the place
        // in the source, if it's known, as file + 1, else 0)
        let (file, line, col) = self.pos.borrow().filter(|p| p.line > 0).map_or((0, 0, 0), |p| (p.file as i64 + 1, p.line as i64, p.col as i64));
        let field = |v: i64, bits: u32| if v < (1 << bits) { v } else { 0 };
        let code = (kind << 58) | (field(func, 16) << 42) | (field(file, 10) << 32) | (field(line, 20) << 12) | field(col, 12);
        f.call(WHERE, vec![Expr::from(code)]);
    }

    /// `rt_where(code)`, which prints a runtime error's message (see `fail`,
    /// which packs the code), "what at file:line:col (in function)", and
    /// stops the program.
    fn where_function(&self, p: &mut Program) {
        let failing = self.failing.borrow().clone();
        // (each file's name from the root file's folder: the same wherever
        // the program was built from)
        let root = self.files.get(1).and_then(|r| std::path::Path::new(r).parent()).map(|d| d.to_path_buf()).unwrap_or_default();
        let files: Vec<String> = self.files.iter().map(|n| std::path::Path::new(n).strip_prefix(&root).map_or(n.clone(), |p| p.display().to_string())).collect();
        p.function(WHERE, &["code"], move |f| {
            let code = f.arg("code");
            let part = |f: &mut IrFunc, shift: i64, bits: i64| f.once((Expr::from(code) >> shift) & ((1i64 << bits) - 1));
            let (kind, func, file, line, col) = (part(f, 58, 4), part(f, 42, 16), part(f, 32, 10), part(f, 12, 20), part(f, 0, 12));
            let file = f.once(file - 1);
            for (k, what) in FAILURES.iter().enumerate() {
                f.if_(kind.eq(k as i64), |f| f.print(what));
            }
            f.if_(file.ge(0), |f| {
                f.print(" at ");
                for (k, name) in files.iter().enumerate() {
                    f.if_(file.eq(k as i64), |f| f.print(name));
                }
                f.print(":");
                f.print_int(line);
                f.if_(col.gt(0), |f| {
                    f.print(":");
                    f.print_int(col);
                });
            });
            for (k, name) in failing.iter().enumerate().filter(|(_, n)| !n.is_empty()) {
                f.if_(func.eq(k as i64), |f| f.print(&format!(" (in {name})")));
            }
            f.print("\n");
            f.abort();
            f.ret(0);
        });
    }

    /// Stops the program: for a `match` nothing matched, saying where;
    /// `panic`'s message (empty here) is the program's own, already printed.
    fn panic(&self, f: &mut IrFunc, message: &str) {
        if message.is_empty() {
            f.abort();
        } else {
            self.fail(f, message);
        }
    }

    /// Stops the program if `i` isn't an index of array `a`.
    fn check_index(&self, f: &mut IrFunc, a: &Expr, i: &Expr) {
        // (one unsigned comparison: a negative index is a huge one, and a
        // length is never negative)
        f.if_(i.geu(a.fixed_at(0)), |f| self.fail(f, "array index out of bounds"));
    }

    /// A built-in operation on `args`.
    fn prim(&self, f: &mut IrFunc, p: Prim, args: Vec<Expr>) -> Expr {
        {
            {
                let x = || args[0].clone();
                let y = || args[1].clone();
                let e: Expr = match p {
                    Prim::Add => x() + y(),
                    Prim::Sub => x() - y(),
                    Prim::Mul => x() * y(),
                    Prim::Div => x() / y(),
                    Prim::Rem => x() % y(),
                    Prim::BitAnd => x() & y(),
                    Prim::BitOr => x() | y(),
                    Prim::BitXor => x() ^ y(),
                    Prim::Shl => x() << y(),
                    Prim::Shr => x() >> y(),
                    Prim::Neg => -x(),
                    Prim::Not => !x(),
                    Prim::IntEq => x().eq(y()),
                    Prim::IntNe => x().ne(y()),
                    Prim::IntLt => x().lt(y()),
                    Prim::IntLe => x().le(y()),
                    Prim::IntGt => x().gt(y()),
                    Prim::IntGe => x().ge(y()),
                    Prim::StrEq => f.call("rt_streq", (x(), y())).into(),
                    Prim::StrLt => f.call("rt_strlt", (x(), y())).into(),
                    Prim::Concat => f.call("rt_concat", (x(), y())).into(),
                    Prim::Print => {
                        f.call("rt_print", x());
                        0.into()
                    }
                    Prim::ReadInt => f.read_int().into(),
                    Prim::IntToString => f.call("rt_itos", x()).into(),
                    Prim::StrLength => x().fixed_at(0),
                    Prim::CharAt => x().at(y() + 1),
                    Prim::CharToString => {
                        let b = f.gc_alloc_data(2);
                        f.set(b.at(0), 1);
                        f.set(b.at(1), x());
                        b.into()
                    }
                    Prim::ArrayNew | Prim::ArrayNewData => {
                        let (n, v) = (x(), y());
                        f.if_(n.lt(0), |f| self.fail(f, "an array can't have a negative length"));
                        let a = if p == Prim::ArrayNewData { f.gc_alloc_data(n.clone() + 1) } else { f.gc_alloc(n.clone() + 1) };
                        f.set(a.at(0), n.clone());
                        f.for_(0, n, |f, i| f.set(a.at(i + 1), v));
                        a.into()
                    }
                    Prim::ArrayGet => {
                        self.check_index(f, &x(), &y());
                        x().at(y() + 1)
                    }
                    Prim::ArraySet => {
                        self.check_index(f, &x(), &y());
                        f.set(x().at(y() + 1), args[2].clone());
                        0.into()
                    }
                    Prim::ArrayLength => x().fixed_at(0),
                    Prim::Extern(k) => f.call(&self.externs[k].0, args.clone()).into(),
                };
                // (worked out here, not wherever it's used)
                f.once(e)
            }
        }
    }
}

/// Runs CPS code to the end, in a trampoline of its own: `call` starts it,
/// given the continuation to finish with. Its result.
fn run_to_end(f: &mut IrFunc, depth: &Expr, result: &Expr, call: impl FnOnce(&mut IrFunc, Expr) -> Expr) -> Expr {
    let saved = f.var(depth.at(0));
    let k = f.gc_alloc(1);
    let halt = f.func_addr("halt");
    f.set(k.at(0), halt);
    f.set(depth.at(0), 0);
    let r = call(f, k.into());
    let r = f.var(r);
    f.while_(r.ne(0), |f| {
        f.set(depth.at(0), 0);
        let next = f.call("rt_run", r);
        f.set(r, next);
    });
    f.set(depth.at(0), saved);
    f.once(result.at(0))
}

/// A string: its length, then a character a cell.
fn string(f: &mut IrFunc, s: &str) -> Expr {
    let bytes = s.as_bytes();
    let b = f.gc_alloc_data(bytes.len() as i64 + 1);
    f.set(b.at(0), bytes.len() as i64);
    for (i, c) in bytes.iter().enumerate() {
        f.set(b.at(i as i64 + 1), *c as i64);
    }
    b.into()
}

/// The runtime errors there are (see `Gen::fail`).
const FAILURES: &[&str] = &["array index out of bounds", "an array can't have a negative length", "no pattern matched"];

/// The function that prints them.
const WHERE: &str = "rt_where";

// ---- direct functions

/// A local variable of a direct function: a value, or (a `let mut` only
/// read and set) an IR variable.
#[derive(Clone)]
enum Local {
    Value(Expr),
    Var(IrVar),
}

impl<'c> Gen<'c> {
    /// The code for `e`, and its value.
    fn direct(&self, f: &mut IrFunc, e: &Core, env: &mut HashMap<String, Local>) -> Expr {
        match e {
            Core::Located(pos, e) => {
                *self.pos.borrow_mut() = Some(*pos);
                self.direct(f, e, env)
            }
            Core::Int(n) => (*n).into(),
            Core::Str(s) => string(f, s),
            Core::Local(n) => match &env[n] {
                Local::Value(x) => x.clone(),
                Local::Var(v) => f.once(*v),
            },
            Core::CallGlobal(g, args, _) => {
                let args: Vec<Expr> = args.iter().map(|a| self.direct(f, a, env)).collect();
                f.call(self.direct_name(g), args).into()
            }
            // a closure, through its direct entry (which, being called from
            // direct code, it has)
            Core::App(c, args, _) => {
                let c = self.direct(f, c, env);
                let c = f.once(c);
                let mut all = vec![c.clone()];
                all.extend(args.iter().map(|a| self.direct(f, a, env)));
                f.call_at(c.at(1), all).into()
            }
            Core::Lam(id, _, _, eff) => {
                let mut cells: Vec<Expr> = vec![f.func_addr(&format!("s{id}"))];
                cells.push(if *eff != Eff::Impure { f.func_addr(&format!("t{id}")) } else { 0.into() });
                for v in free_locals(e) {
                    match &env[&v] {
                        Local::Value(x) => cells.push(x.clone()),
                        Local::Var(_) => unreachable!("a variable a lambda uses is a cell"),
                    }
                }
                block(f, cells)
            }
            Core::Let(n, v, body) => {
                match &**v {
                    Core::NewRef(init) if only_through_refs(n, body) => {
                        let init = self.direct(f, init, env);
                        let var = f.var(init);
                        env.insert(n.clone(), Local::Var(var));
                    }
                    _ => {
                        let x = self.direct(f, v, env);
                        let x = f.once(x);
                        env.insert(n.clone(), Local::Value(x));
                    }
                }
                self.direct(f, body, env)
            }
            Core::If(c, a, b) => {
                let c = self.direct(f, c, env);
                let r = f.var(0);
                f.if_else(
                    c,
                    |f| {
                        let v = self.direct(f, a, &mut env.clone());
                        f.set(r, v);
                    },
                    |f| {
                        let v = self.direct(f, b, &mut env.clone());
                        f.set(r, v);
                    },
                );
                f.once(r)
            }
            Core::Match(s, arms) => {
                let s = self.direct(f, s, env);
                let s = f.once(s);
                // each arm tried while none has matched
                let (r, done) = (f.var(0), f.var(0));
                for (pat, body) in arms {
                    f.if_(Expr::from(done).eq(0), |f| {
                        self.test(f, pat, s.clone(), &mut env.clone(), &mut |f, env| {
                            f.set(done, 1);
                            let v = self.direct(f, body, env);
                            f.set(r, v);
                        })
                    });
                }
                f.if_(Expr::from(done).eq(0), |f| {
                    f.print("no pattern matched");
                    f.abort();
                });
                f.once(r)
            }
            Core::Con(tag, args) => {
                let mut cells: Vec<Expr> = vec![(*tag).into()];
                cells.extend(args.iter().map(|a| self.direct(f, a, env)));
                block(f, cells)
            }
            Core::Tuple(xs) => {
                let cells = xs.iter().map(|a| self.direct(f, a, env)).collect();
                block(f, cells)
            }
            Core::Proj(x, i) => {
                let x = self.direct(f, x, env);
                f.once(x.fixed_at(*i as i64))
            }
            Core::Field(x, i) => {
                let x = self.direct(f, x, env);
                f.once(x.at(*i as i64))
            }
            Core::SetProj(x, i, v) => {
                let x = self.direct(f, x, env);
                let v = self.direct(f, v, env);
                f.set(x.at(*i as i64), v);
                0.into()
            }
            Core::Record(fs) => {
                let mut cells: Vec<Expr> = vec![(fs.len() as i64).into()];
                for (l, v) in fs {
                    cells.push(self.labels[l].into());
                    cells.push(self.direct(f, v, env));
                }
                block(f, cells)
            }
            Core::RecGet(r, l) => {
                let r = self.direct(f, r, env);
                f.call("rt_recget", (r, self.labels[l])).into()
            }
            Core::RecExtend(r, fs) => {
                let mut r = self.direct(f, r, env);
                let values: Vec<Expr> = fs.iter().map(|(_, v)| self.direct(f, v, env)).collect();
                for ((l, _), x) in fs.iter().zip(values).rev() {
                    r = f.call("rt_recext", (r, self.labels[l], x)).into();
                }
                r
            }
            Core::Prim(p, args) => {
                let args = args.iter().map(|a| self.direct(f, a, env)).collect();
                self.prim(f, *p, args)
            }
            Core::Seq(a, b) => {
                self.direct(f, a, env);
                self.direct(f, b, env)
            }
            Core::While(c, body) => {
                f.loop_(|f| {
                    let c = self.direct(f, c, &mut env.clone());
                    f.if_(!c, |f| f.break_());
                    self.direct(f, body, &mut env.clone());
                });
                0.into()
            }
            Core::Loop(body) => {
                f.loop_(|f| {
                    self.direct(f, body, &mut env.clone());
                });
                0.into()
            }
            Core::Break => {
                f.break_();
                0.into()
            }
            Core::Continue => {
                f.continue_();
                0.into()
            }
            Core::Return(v) => {
                let v = self.direct(f, v, env);
                f.ret(v);
                0.into()
            }
            Core::NewRef(v) => {
                let v = self.direct(f, v, env);
                block(f, vec![v])
            }
            Core::GetRef(r) => match &**r {
                Core::Local(n) if matches!(env.get(n), Some(Local::Var(_))) => self.direct(f, r, env),
                _ => {
                    let r = self.direct(f, r, env);
                    f.once(r.at(0))
                }
            },
            Core::SetRef(r, v) => {
                let place = match &**r {
                    Core::Local(n) => env.get(n).cloned(),
                    _ => None,
                };
                let v = self.direct(f, v, env);
                match place {
                    Some(Local::Var(var)) => f.set(var, v),
                    _ => {
                        let r = self.direct(f, r, env);
                        f.set(r.at(0), v);
                    }
                }
                0.into()
            }
            Core::Panic(m) => {
                self.panic(f, m);
                0.into()
            }
            _ => unreachable!("not in a direct function: {e:?}"),
        }
    }

    /// Code that checks `v` against `pat`, binding its variables, and runs
    /// `success` if it matches.
    fn test(&self, f: &mut IrFunc, pat: &Pat, v: Expr, env: &mut HashMap<String, Local>, success: &mut dyn FnMut(&mut IrFunc, &mut HashMap<String, Local>)) {
        match pat {
            Pat::Wild => success(f, env),
            Pat::Bind(n) => {
                env.insert(n.clone(), Local::Value(v));
                success(f, env)
            }
            Pat::Int(n) => f.if_(v.eq(*n), |f| success(f, env)),
            // (a Bool is a number, not a block)
            Pat::Con(e, k, subs) if e == "Bool" && subs.is_empty() => f.if_(v.eq(*k), |f| success(f, env)),
            Pat::Str(s) => {
                let s = string(f, s);
                let same = f.call("rt_streq", (v, s));
                f.if_(same, |f| success(f, env))
            }
            Pat::Con(_, k, subs) => f.if_(v.at(0).eq(*k), |f| self.fields(f, &v, subs, 1, env, success)),
            Pat::Tuple(subs) => self.fields(f, &v, subs, 0, env, success),
        }
    }

    /// The fields of block `v` from cell `first`, checked against `subs`.
    fn fields(&self, f: &mut IrFunc, v: &Expr, subs: &[Pat], first: i64, env: &mut HashMap<String, Local>, success: &mut dyn FnMut(&mut IrFunc, &mut HashMap<String, Local>)) {
        let Some((p, rest)) = subs.split_first() else { return success(f, env) };
        let x = f.once(v.at(first));
        self.test(f, p, x, env, &mut |f, env| self.fields(f, v, rest, first + 1, env, success))
    }
}

/// A block of these cells.
fn block(f: &mut IrFunc, cells: Vec<Expr>) -> Expr {
    let b = f.gc_alloc(cells.len() as i64);
    for (i, c) in cells.into_iter().enumerate() {
        f.set(b.at(i as i64), c);
    }
    b.into()
}

/// The variables `t` uses that it doesn't bind (in the order it first uses
/// them).
fn free_vars(t: &Term, bound: &mut HashSet<Var>, out: &mut Vec<Var>) {
    let use_atom = |a: &Atom, bound: &HashSet<Var>, out: &mut Vec<Var>| {
        if let Atom::Var(v) = a {
            if !bound.contains(v) && !out.contains(v) {
                out.push(v.clone());
            }
        }
    };
    match t {
        Term::Located(_, t) => free_vars(t, bound, out),
        Term::Let(x, v, rest) => {
            match v {
                Val::Atom(a) | Val::Proj(a, _) | Val::Field(a, _) | Val::FindHandler(a, _) | Val::RecGet(a, _) => use_atom(a, bound, out),
                Val::Prim(_, args) | Val::Alloc(args) | Val::Direct(_, args) => args.iter().for_each(|a| use_atom(a, bound, out)),
                Val::Set(a, _, b) => {
                    use_atom(a, bound, out);
                    use_atom(b, bound, out);
                }
                Val::Record(fs) => fs.iter().for_each(|(_, a)| use_atom(a, bound, out)),
                Val::RecExtend(a, fs) => {
                    use_atom(a, bound, out);
                    fs.iter().for_each(|(_, b)| use_atom(b, bound, out));
                }
                Val::Lambda(ps, body, _) => {
                    let mut inner = bound.clone();
                    inner.extend(ps.iter().cloned());
                    free_vars(body, &mut inner, out);
                }
                Val::Str(_) => {}
            }
            let fresh = bound.insert(x.clone());
            free_vars(rest, bound, out);
            if fresh {
                bound.remove(x);
            }
        }
        Term::LetRec(x, ps, body, rest) => {
            let mut inner = bound.clone();
            inner.insert(x.clone());
            inner.extend(ps.iter().cloned());
            free_vars(body, &mut inner, out);
            let fresh = bound.insert(x.clone());
            free_vars(rest, bound, out);
            if fresh {
                bound.remove(x);
            }
        }
        Term::If(c, a, b) => {
            use_atom(c, bound, out);
            free_vars(a, bound, out);
            free_vars(b, bound, out);
        }
        Term::CallGlobal(_, args) => args.iter().for_each(|a| use_atom(a, bound, out)),
        Term::Call(c, args) => {
            use_atom(c, bound, out);
            args.iter().for_each(|a| use_atom(a, bound, out));
        }
        Term::Panic(_) => {}
    }
}

/// The runtime's functions.
fn runtime(p: &mut Program, max_args: usize, effect_names: &HashMap<i64, String>) {
    p.function("rt_print", &["s"], |f| {
        let s = f.arg("s");
        f.for_(0, s.fixed_at(0), |f, i| f.print_char(s.at(i + 1)));
        f.ret(0);
    });
    p.function("rt_concat", &["a", "b"], |f| {
        let (a, b) = (f.arg("a"), f.arg("b"));
        let (na, nb) = (f.var(a.fixed_at(0)), f.var(b.fixed_at(0)));
        let r = f.gc_alloc_data(na + nb + 1);
        f.set(r.at(0), na + nb);
        f.for_(0, na, |f, i| f.set(r.at(i + 1), a.at(i + 1)));
        f.for_(0, nb, |f, i| f.set(r.at(na + i + 1), b.at(i + 1)));
        f.ret(r);
    });
    p.function("rt_streq", &["a", "b"], |f| {
        let (a, b) = (f.arg("a"), f.arg("b"));
        f.if_(a.fixed_at(0).ne(b.fixed_at(0)), |f| f.ret(0));
        f.for_(0, a.fixed_at(0), |f, i| f.if_(a.at(i + 1).ne(b.at(i + 1)), |f| f.ret(0)));
        f.ret(1);
    });
    p.function("rt_strlt", &["a", "b"], |f| {
        let (a, b) = (f.arg("a"), f.arg("b"));
        let n = f.var(a.fixed_at(0).min(b.fixed_at(0)));
        f.for_(0, n, |f, i| f.if_(a.at(i + 1).ne(b.at(i + 1)), |f| f.ret(a.at(i + 1).lt(b.at(i + 1)))));
        f.ret(a.fixed_at(0).lt(b.fixed_at(0)));
    });
    p.function("rt_itos", &["n"], |f| {
        let n = f.arg("n");
        let digits = f.array(24);
        let negative = f.var(n.lt(0));
        let m = f.var(n);
        f.if_(negative, |f| f.set(m, -m));
        let len = f.var(0);
        f.loop_(|f| {
            f.set(digits.at(len), m % 10 + 48);
            f.set(len, len + 1);
            f.set(m, m / 10);
            f.if_(m.eq(0), |f| f.break_());
        });
        let total = f.var(len + negative);
        let r = f.gc_alloc_data(total + 1);
        f.set(r.at(0), total);
        f.if_(negative, |f| f.set(r.at(1), '-'));
        f.for_(0, len, |f, i| f.set(r.at(total - i), digits.at(i)));
        f.ret(r);
    });
    p.function("rt_recget", &["r", "label"], |f| {
        let (r, label) = (f.arg("r"), f.arg("label"));
        f.for_(0, r.at(0), |f, i| f.if_(r.at(i * 2 + 1).eq(label), |f| f.ret(r.at(i * 2 + 2))));
        f.print("no such field\n");
        f.abort();
    });
    p.function("rt_recext", &["r", "label", "v"], |f| {
        let (r, label, v) = (f.arg("r"), f.arg("label"), f.arg("v"));
        let n = f.var(r.at(0));
        let q = f.gc_alloc(n * 2 + 3);
        f.set(q.at(0), n + 1);
        f.set(q.at(1), label);
        f.set(q.at(2), v);
        f.for_(0, n * 2, |f, i| f.set(q.at(i + 3), r.at(i + 1)));
        f.ret(q);
    });
    let mut names: Vec<(i64, String)> = effect_names.iter().map(|(k, v)| (*k, v.clone())).collect();
    names.sort();
    p.function("rt_find", &["h", "eff"], move |f| {
        let (h, eff) = (f.arg("h"), f.arg("eff"));
        f.while_(h.ne(0), |f| {
            f.if_(h.at(0).eq(eff), |f| f.ret(h));
            f.set(h, h.at(4));
        });
        f.print("unhandled effect: ");
        for (k, name) in &names {
            let msg = format!("{name}\n");
            f.if_(eff.eq(*k), |f| f.print(&msg));
        }
        f.abort();
    });
    // a thunk's call: its number of arguments says which call to make
    p.function("rt_run", &["t"], move |f| {
        let t = f.arg("t");
        for n in 0..=max_args {
            f.if_(t.at(0).eq(n as i64), |f| {
                let args: Vec<Expr> = (0..n).map(|i| t.at(i as i64 + 2)).collect();
                let r = f.call_at(t.at(1), args);
                f.ret(r);
            });
        }
        f.print("bad thunk\n");
        f.abort();
    });
}

#[allow(dead_code)]
fn unused(_: IrVar) {}
