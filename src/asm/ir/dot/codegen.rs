//! Code generation: from checked terms to an IR module.
//!
//! Types are erased, and every value is one cell: an integer, a boolean (1 or
//! 0), unit (0), or the address of a record allocated with `gc_alloc`, which
//! the garbage collector frees once nothing points to it.
//!
//! An object is a record of its fields. Each field name has the same slot in
//! every object, so selecting a field doesn't need to know which object it
//! is: the slots come from coloring a graph of the names, with an edge
//! between names defined in the same object, so names that never meet share
//! a slot.
//!
//! A function is a closure: a record of the address of its code and the
//! values of the variables it captures. A lambda of several parameters,
//! `(x: A, y: B) => t`, is curried, but its body is one IR function that
//! takes the closure and all of them; calling the closure goes through small
//! functions that collect the arguments one at a time. Where a call's
//! function is known (a `def`, or a `val` that's a lambda), and it's given
//! all its arguments, it's a direct call to the whole body, which the
//! optimizer can inline, or turn into a loop when it's a tail call to
//! itself. Other calls are indirect calls to the address in the closure's
//! first cell.

use super::strings;
use super::syntax::*;
use super::typer::{Kind, Note};
use crate::asm::ir::{Function, Module, Value};
use std::collections::{HashMap, HashSet};
use std::rc::Rc;

pub fn generate(
    term: &Term,
    names: &Names,
    notes: &HashMap<usize, Note>,
    implicit: &HashMap<usize, usize>,
    min_width: u32,
) -> Module {
    let mut module = Module::with_min_width(min_width);
    let mut shared = Shared {
        names,
        notes,
        implicit,
        slots: slots(term),
        jobs: vec![],
        taken: BUILTINS.iter().map(|(b, _)| b.to_string()).chain(["main".to_string()]).collect(),
        known: HashMap::new(),
        alias: HashMap::new(),
        runtime: HashSet::new(),
        builtins: HashSet::new(),
        externs: HashSet::new(),
    };
    let f = module.main();
    let mut g = Gen { f, env: HashMap::new(), s: &mut shared };
    g.term(term);
    g.f.ret_void();
    while let Some(job) = shared.jobs.pop() {
        match job {
            Job::Body { lambda, params, body } => {
                let f = module.function(&lambda.name, 1 + params.len());
                let closure = f.param(0);
                let mut env: HashMap<Var, Value> = params.iter().enumerate().map(|(i, &x)| (x, f.param(i + 1))).collect();
                for (i, &c) in lambda.captures.iter().enumerate() {
                    let slot = f.int(i as i64 + 1);
                    let addr = f.index(closure, slot);
                    env.insert(c, f.load(addr));
                }
                let mut g = Gen { f, env, s: &mut shared };
                let r = g.term(&body);
                g.f.ret(r);
            }
            Job::Curried { lambda, i } => curried(module.function(&lambda.curried[i - 1], 2), &lambda, i),
        }
    }
    strings::add(&mut module, &shared.runtime);
    let mut externs: Vec<&String> = shared.externs.iter().collect();
    externs.sort();
    for name in externs {
        module.external(name);
    }
    let mut used: Vec<&String> = shared.builtins.iter().collect();
    used.sort();
    for name in used {
        let &(_, params) = BUILTINS.iter().find(|(b, _)| b == name).expect("checked");
        builtin(name, module.function(name, params));
    }
    module
}

/// The compiler's own functions, which `builtin def` declares, with how
/// many parameters each takes: raw cells, which the standard library's
/// arrays, buffers and strings are made of.
pub(super) const BUILTINS: [(&str, usize); 4] = [("mem_new", 1), ("mem_get", 2), ("mem_set", 3), ("mem_as_string", 1)];

/// Builds the body of the built-in function `name`.
fn builtin(name: &str, f: &mut Function) {
    match name {
        // `n` cells
        "mem_new" => {
            let n = f.param(0);
            let p = f.gc_alloc(n);
            f.ret(p);
        }
        // cell `i` of `p`
        "mem_get" => {
            let (p, i) = (f.param(0), f.param(1));
            let at = f.index(p, i);
            let x = f.load(at);
            f.ret(x);
        }
        // sets cell `i` of `p` to `x`
        "mem_set" => {
            let (p, i, x) = (f.param(0), f.param(1), f.param(2));
            let at = f.index(p, i);
            f.store(at, x);
            let zero = f.int(0);
            f.ret(zero);
        }
        // cells, as a string (their length, then a character in each)
        "mem_as_string" => {
            let p = f.param(0);
            f.ret(p);
        }
        _ => unreachable!("checked"),
    }
}

/// The function that takes argument `i` (from 1) of a curried lambda: it
/// collects the arguments so far in a new closure, or once it has them all,
/// calls the body.
fn curried(f: &mut Function, lambda: &Lambda, i: usize) {
    let (partial, x) = (f.param(0), f.param(1));
    // the first takes the lambda's own closure; later ones a record of the
    // code, that closure, and the arguments before
    let (env, mut args) = if i == 1 {
        (partial, vec![])
    } else {
        let one = f.int(1);
        let at = f.index(partial, one);
        let env = f.load(at);
        let args: Vec<Value> = (2..=i)
            .map(|j| {
                let slot = f.int(j as i64);
                let at = f.index(partial, slot);
                f.load(at)
            })
            .collect();
        (env, args)
    };
    args.push(x);
    if i == lambda.arity {
        let all: Vec<Value> = std::iter::once(env).chain(args).collect();
        let r = f.call(&lambda.name, &all);
        f.ret(r);
        return;
    }
    let size = f.int(2 + i as i64);
    let record = f.gc_alloc(size);
    let code = f.func_addr(&lambda.curried[i]);
    f.store(record, code);
    for (j, v) in std::iter::once(env).chain(args).enumerate() {
        let slot = f.int(j as i64 + 1);
        let at = f.index(record, slot);
        f.store(at, v);
    }
    f.ret(record);
}

/// The slot of each field name.
fn slots(term: &Term) -> HashMap<String, usize> {
    fn objects(t: &Term, out: &mut Vec<Vec<String>>) {
        let mut go = |t: &Term| objects(t, out);
        match &t.kind {
            TermKind::New(_, _, defs) => {
                let mut fields = vec![];
                for d in defs {
                    if let DefKind::Val(_, t) | DefKind::Var(_, t) = &d.kind {
                        fields.push(d.name.clone());
                        objects(t, out);
                    }
                }
                out.push(fields);
            }
            TermKind::Lam(_, _, b) | TermKind::Sel(b, _) | TermKind::Ascribe(b, _) | TermKind::Set(_, b) => go(b),
            TermKind::App(a, b) | TermKind::Let(_, _, a, b) | TermKind::LetVar(_, _, a, b) | TermKind::While(a, b) | TermKind::Assign(a, _, b) => {
                go(a);
                go(b);
            }
            TermKind::If(a, b, c) => {
                go(a);
                go(b);
                go(c);
            }
            TermKind::Prim(_, args) => args.iter().for_each(go),
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
    let mut all = vec![];
    objects(term, &mut all);
    let mut order: Vec<&String> = vec![];
    let mut neighbors: HashMap<&String, HashSet<&String>> = HashMap::new();
    for fields in &all {
        for a in fields {
            if !neighbors.contains_key(a) {
                order.push(a);
            }
            let n = neighbors.entry(a).or_default();
            n.extend(fields.iter().filter(|b| *b != a));
        }
    }
    let mut slots: HashMap<String, usize> = HashMap::new();
    for a in order {
        let used: HashSet<usize> = neighbors[a].iter().filter_map(|b| slots.get(*b).copied()).collect();
        let slot = (0..).find(|s| !used.contains(s)).unwrap();
        slots.insert(a.clone(), slot);
    }
    slots
}

/// The variables a term uses but doesn't bind. Variables are unique, so
/// that's every variable used, less every one bound.
fn free_vars(t: &Term) -> Vec<Var> {
    fn walk(t: &Term, used: &mut HashSet<Var>, bound: &mut HashSet<Var>) {
        let mut go = |t: &Term| walk(t, used, bound);
        match &t.kind {
            TermKind::Var(x) => {
                used.insert(*x);
            }
            TermKind::Lam(x, _, b) => {
                bound.insert(*x);
                walk(b, used, bound);
            }
            TermKind::Let(x, _, a, b) => {
                bound.insert(*x);
                walk(a, used, bound);
                walk(b, used, bound);
            }
            TermKind::New(z, _, defs) => {
                bound.insert(*z);
                for d in defs {
                    if let DefKind::Val(_, t) | DefKind::Var(_, t) = &d.kind {
                        walk(t, used, bound);
                    }
                }
            }
            TermKind::LetVar(x, _, a, b) => {
                bound.insert(*x);
                walk(a, used, bound);
                walk(b, used, bound);
            }
            TermKind::Get(x) => {
                used.insert(*x);
            }
            TermKind::Set(x, b) => {
                used.insert(*x);
                walk(b, used, bound);
            }
            TermKind::Foreign(_, params, _) => used.extend(params),
            TermKind::Sel(b, _) | TermKind::Ascribe(b, _) => go(b),
            TermKind::App(a, b) | TermKind::While(a, b) | TermKind::Assign(a, _, b) => {
                go(a);
                go(b);
            }
            TermKind::If(a, b, c) => {
                go(a);
                go(b);
                go(c);
            }
            TermKind::Prim(_, args) => args.iter().for_each(go),
            TermKind::Int(_) | TermKind::Bool(_) | TermKind::Unit | TermKind::Str(_) | TermKind::TypeArg(_) => {}
        }
    }
    let (mut used, mut bound) = (HashSet::new(), HashSet::new());
    walk(t, &mut used, &mut bound);
    let mut free: Vec<Var> = used.difference(&bound).copied().collect();
    free.sort();
    free
}

fn strip_ascriptions(t: &Term) -> &Term {
    match &t.kind {
        TermKind::Ascribe(t, _) => strip_ascriptions(t),
        _ => t,
    }
}

/// A lambda's code: the function that takes all its parameters, and the
/// ones that take them one at a time.
struct Lambda {
    name: String,
    arity: usize,
    captures: Vec<Var>,
    /// The functions taking each argument, when there's more than one.
    curried: Vec<String>,
}

impl Lambda {
    /// The code a closure of it starts with.
    fn entry(&self) -> &str {
        if self.arity == 1 { &self.name } else { &self.curried[0] }
    }
}

/// A function's code still to generate.
enum Job {
    Body { lambda: Rc<Lambda>, params: Vec<Var>, body: Term },
    Curried { lambda: Rc<Lambda>, i: usize },
}

struct Shared<'a> {
    names: &'a Names,
    notes: &'a HashMap<usize, Note>,
    /// How many type arguments the checker worked out to pass before each
    /// argument, by its position.
    implicit: &'a HashMap<usize, usize>,
    /// The built-in functions called.
    builtins: HashSet<String>,
    /// The external functions called.
    externs: HashSet<String>,
    slots: HashMap<String, usize>,
    jobs: Vec<Job>,
    /// The functions' names so far.
    taken: HashSet<String>,
    /// The lambdas that variables, and objects' fields, are known to be.
    known: HashMap<(Var, Option<String>), Rc<Lambda>>,
    /// Variables bound to the object another variable names.
    alias: HashMap<Var, Var>,
    /// The string functions needed.
    runtime: HashSet<&'static str>,
}

impl Shared<'_> {
    /// Names for a lambda's functions, from the name of what it's bound to.
    fn function_names(&mut self, hint: &str, arity: usize) -> (String, Vec<String>) {
        let base: String = hint.trim_start_matches('_').chars().filter(|c| c.is_ascii_alphanumeric() || *c == '_').take(8).collect();
        let base = if base.is_empty() { "lam".to_string() } else { base };
        let curried = |name: &str| if arity > 1 { (1..=arity).map(|i| format!("{name}c{i}")).collect() } else { vec![] };
        let (name, curried) = std::iter::once(base.clone())
            .chain((1..).map(|n| format!("{base}_{n}")))
            .map(|name| {
                let c: Vec<String> = curried(&name);
                (name, c)
            })
            .find(|(name, c)| !self.taken.contains(name) && c.iter().all(|c| !self.taken.contains(c)))
            .unwrap();
        self.taken.insert(name.clone());
        self.taken.extend(curried.iter().cloned());
        (name, curried)
    }

    fn resolve(&self, mut x: Var) -> Var {
        while let Some(&y) = self.alias.get(&x) {
            if y == x {
                break;
            }
            x = y;
        }
        x
    }

    /// The lambda the head of a call is known to be.
    fn known_head(&self, head: &Term) -> Option<Rc<Lambda>> {
        match &strip_ascriptions(head).kind {
            TermKind::Var(x) => self.known.get(&(self.resolve(*x), None)).cloned(),
            TermKind::Sel(r, m) => match strip_ascriptions(r).kind {
                TermKind::Var(z) => self.known.get(&(self.resolve(z), Some(m.clone()))).cloned(),
                _ => None,
            },
            _ => None,
        }
    }

    fn note(&self, pos: usize) -> Option<Note> {
        self.notes.get(&pos).copied()
    }
}

struct Gen<'f, 's, 'a> {
    f: &'f mut Function,
    env: HashMap<Var, Value>,
    s: &'s mut Shared<'a>,
}

impl Gen<'_, '_, '_> {
    fn term(&mut self, t: &Term) -> Value {
        match &t.kind {
            TermKind::Var(x) => self.env[x],
            TermKind::Int(n) => self.f.int(*n),
            TermKind::Bool(b) => self.f.int(*b as i64),
            TermKind::Unit => self.f.int(0),
            TermKind::Str(s) => strings::literal(self.f, s),
            TermKind::Lam(..) => {
                let lambda = self.lambda(t, "lam");
                self.closure(&lambda)
            }
            TermKind::App(..) => self.call(t),
            TermKind::Sel(recv, a) if self.s.note(t.pos) == Some(Note::StrMember) => {
                let s = self.term(recv);
                match a.as_str() {
                    "length" => self.f.load(s),
                    "charAt" => self.record("_s_charc", &[s]),
                    _ => self.record("_s_sub1", &[s]),
                }
            }
            TermKind::Sel(recv, a) => {
                let obj = self.term(recv);
                let slot = self.s.slots.get(a).copied().unwrap_or(0);
                let slot = self.f.int(slot as i64);
                let addr = self.f.index(obj, slot);
                self.f.load(addr)
            }
            TermKind::New(z, _, defs) => {
                // the lambdas among its fields are known, even inside them
                let lambdas: HashMap<&str, Rc<Lambda>> = defs
                    .iter()
                    .filter_map(|d| match &d.kind {
                        DefKind::Val(_, t) if matches!(strip_ascriptions(t).kind, TermKind::Lam(..)) => {
                            let lambda = self.lambda(strip_ascriptions(t), &d.name);
                            self.s.known.insert((*z, Some(d.name.clone())), lambda.clone());
                            Some((d.name.as_str(), lambda))
                        }
                        _ => None,
                    })
                    .collect();
                let fields: Vec<(usize, &Def)> = defs
                    .iter()
                    .filter(|d| matches!(d.kind, DefKind::Val(..) | DefKind::Var(..)))
                    .map(|d| (self.s.slots[&d.name], d))
                    .collect();
                // an object without fields still gets a cell, so it's
                // different from every other
                let size = fields.iter().map(|(s, _)| s + 1).max().unwrap_or(1);
                let size = self.f.int(size as i64);
                let obj = self.f.gc_alloc(size);
                self.env.insert(*z, obj);
                for (slot, d) in fields {
                    let (DefKind::Val(_, t) | DefKind::Var(_, t)) = &d.kind else { unreachable!() };
                    let v = match lambdas.get(d.name.as_str()) {
                        Some(lambda) => self.closure(lambda),
                        None => self.term(t),
                    };
                    let slot = self.f.int(slot as i64);
                    let addr = self.f.index(obj, slot);
                    self.f.store(addr, v);
                }
                obj
            }
            TermKind::Let(x, _, value, body) => {
                let v = match &strip_ascriptions(value).kind {
                    TermKind::Lam(..) => {
                        let name = self.s.names.name(*x).to_string();
                        let lambda = self.lambda(strip_ascriptions(value), &name);
                        self.s.known.insert((*x, None), lambda.clone());
                        self.closure(&lambda)
                    }
                    TermKind::New(z, ..) => {
                        if z != x {
                            self.s.alias.insert(*x, *z);
                        }
                        self.term(value)
                    }
                    _ => self.term(value),
                };
                self.env.insert(*x, v);
                self.term(body)
            }
            TermKind::If(c, a, b) => {
                let c = self.term(c);
                let (then, els, merge) = (self.f.new_block(0), self.f.new_block(0), self.f.new_block(1));
                self.f.branch(c, then, &[], els, &[]);
                for (block, t) in [(then, a), (els, b)] {
                    self.f.switch_to(block);
                    let v = self.term(t);
                    self.f.jump(merge, &[v]);
                }
                self.f.switch_to(merge);
                self.f.block_param(merge, 0)
            }
            TermKind::Prim(prim, args) => self.prim(prim, args, t.pos),
            TermKind::Ascribe(e, _) => self.term(e),
            // only a type argument's type matters, so it's nothing at run time
            TermKind::TypeArg(_) => self.f.int(0),
            // a var is a cell of its own, which closures that use it share
            TermKind::LetVar(x, _, value, body) => {
                let v = self.term(value);
                let one = self.f.int(1);
                let cell = self.f.gc_alloc(one);
                self.f.store(cell, v);
                self.env.insert(*x, cell);
                self.term(body)
            }
            TermKind::Get(x) => self.f.load(self.env[x]),
            TermKind::Set(x, value) => {
                let v = self.term(value);
                self.f.store(self.env[x], v);
                self.f.int(0)
            }
            TermKind::Assign(recv, a, value) => {
                let obj = self.term(recv);
                let v = self.term(value);
                let slot = self.s.slots.get(a).copied().unwrap_or(0);
                let slot = self.f.int(slot as i64);
                let addr = self.f.index(obj, slot);
                self.f.store(addr, v);
                self.f.int(0)
            }
            TermKind::While(c, body) => {
                let (head, inside, after) = (self.f.new_block(0), self.f.new_block(0), self.f.new_block(0));
                self.f.jump(head, &[]);
                self.f.switch_to(head);
                let c = self.term(c);
                self.f.branch(c, inside, &[], after, &[]);
                self.f.switch_to(inside);
                self.term(body);
                self.f.jump(head, &[]);
                self.f.switch_to(after);
                self.f.int(0)
            }
            TermKind::Foreign(name, params, ForeignKind::Builtin) => {
                self.s.builtins.insert(name.clone());
                let args: Vec<Value> = params.iter().map(|x| self.env[x]).collect();
                self.f.call(name, &args)
            }
            TermKind::Foreign(name, params, ForeignKind::Extern) => {
                self.s.externs.insert(name.clone());
                let args: Vec<Value> = params.iter().map(|x| self.env[x]).collect();
                self.f.call_extern(name, &args)
            }
        }
    }

    /// A record of a function's address and `values`.
    fn record(&mut self, code: &'static str, values: &[Value]) -> Value {
        self.s.runtime.insert(code);
        let size = self.f.int(values.len() as i64 + 1);
        let r = self.f.gc_alloc(size);
        let addr = self.f.func_addr(code);
        self.f.store(r, addr);
        for (i, &v) in values.iter().enumerate() {
            let slot = self.f.int(i as i64 + 1);
            let at = self.f.index(r, slot);
            self.f.store(at, v);
        }
        r
    }

    /// Names the functions for the lambda `t`, and queues their code.
    fn lambda(&mut self, t: &Term, hint: &str) -> Rc<Lambda> {
        let captures = free_vars(t);
        let mut params = vec![];
        let mut body = t;
        while let TermKind::Lam(x, _, b) = &body.kind {
            params.push(*x);
            body = b;
        }
        let (name, curried) = self.s.function_names(hint, params.len());
        let lambda = Rc::new(Lambda { name, arity: params.len(), captures, curried });
        self.s.jobs.push(Job::Body { lambda: lambda.clone(), params, body: body.clone() });
        if lambda.arity > 1 {
            for i in 1..=lambda.arity {
                self.s.jobs.push(Job::Curried { lambda: lambda.clone(), i });
            }
        }
        lambda
    }

    /// A closure of `lambda`, capturing the variables it uses.
    fn closure(&mut self, lambda: &Lambda) -> Value {
        let size = self.f.int(lambda.captures.len() as i64 + 1);
        let closure = self.f.gc_alloc(size);
        let code = self.f.func_addr(lambda.entry());
        self.f.store(closure, code);
        for (i, c) in lambda.captures.iter().enumerate() {
            let slot = self.f.int(i as i64 + 1);
            let addr = self.f.index(closure, slot);
            self.f.store(addr, self.env[c]);
        }
        closure
    }

    fn call_closure(&mut self, closure: Value, arg: Value) -> Value {
        let code = self.f.load(closure);
        self.f.call_indirect(code, &[closure, arg])
    }

    /// `head(a)(b)...`
    fn call(&mut self, t: &Term) -> Value {
        let mut given = vec![];
        let mut head = t;
        while let TermKind::App(fun, arg) = &head.kind {
            given.push(&**arg);
            head = fun;
        }
        given.reverse();
        // the type arguments the checker worked out go before the argument
        // they were found for, and are nothing at run time
        let mut args: Vec<Option<&Term>> = vec![];
        for a in given {
            for _ in 0..self.s.implicit.get(&a.pos).copied().unwrap_or(0) {
                args.push(None);
            }
            args.push(Some(a));
        }
        let mut rest = &args[..];
        let mut v = match &head.kind {
            // a string's methods
            TermKind::Sel(recv, m) if self.s.note(head.pos) == Some(Note::StrMember) => {
                let s = self.term(recv);
                if m == "charAt" {
                    let i = self.arg(rest[0]);
                    rest = &rest[1..];
                    self.s.runtime.insert("_s_char");
                    self.f.call("_s_char", &[s, i])
                } else if rest.len() >= 2 {
                    let (i, j) = (self.arg(rest[0]), self.arg(rest[1]));
                    rest = &rest[2..];
                    self.s.runtime.insert("_s_sub");
                    self.f.call("_s_sub", &[s, i, j])
                } else {
                    let i = self.arg(rest[0]);
                    rest = &rest[1..];
                    self.record("_s_sub2", &[s, i])
                }
            }
            _ => match self.s.known_head(head) {
                // a known function, given all its arguments
                Some(lambda) if args.len() >= lambda.arity => {
                    let closure = self.term(head);
                    let mut values = vec![closure];
                    for &a in &args[..lambda.arity] {
                        values.push(self.arg(a));
                    }
                    rest = &args[lambda.arity..];
                    self.f.call(&lambda.name, &values)
                }
                _ => self.term(head),
            },
        };
        for &a in rest {
            let x = self.arg(a);
            v = self.call_closure(v, x);
        }
        v
    }

    /// An argument's value: 0 for a type argument the checker worked out.
    fn arg(&mut self, a: Option<&Term>) -> Value {
        match a {
            Some(t) => self.term(t),
            None => self.f.int(0),
        }
    }

    /// `v` as a string, when it's a value of kind `kind`.
    fn to_string(&mut self, v: Value, kind: Kind) -> Value {
        match kind {
            Kind::Str => v,
            Kind::Int => {
                self.s.runtime.insert("_s_int");
                self.f.call("_s_int", &[v])
            }
            Kind::Bool => {
                self.s.runtime.insert("_s_bool");
                self.f.call("_s_bool", &[v])
            }
        }
    }

    /// Stops the program with an error, then goes on in a block that never
    /// runs.
    fn fail(&mut self) {
        self.f.abort();
        let after = self.f.new_block(0);
        self.f.jump(after, &[]);
        self.f.switch_to(after);
    }

    fn prim(&mut self, prim: &Prim, args: &[Term], pos: usize) -> Value {
        use Prim::*;
        let unit = self.f.int(0);
        match prim {
            And | Or => {
                let a = self.term(&args[0]);
                let (rhs, merge) = (self.f.new_block(0), self.f.new_block(1));
                if *prim == And {
                    self.f.branch(a, rhs, &[], merge, &[unit]);
                } else {
                    let one = self.f.int(1);
                    self.f.branch(a, merge, &[one], rhs, &[]);
                }
                self.f.switch_to(rhs);
                let b = self.term(&args[1]);
                self.f.jump(merge, &[b]);
                self.f.switch_to(merge);
                self.f.block_param(merge, 0)
            }
            Print | PrintLn => {
                let v = self.term(&args[0]);
                match self.s.note(pos) {
                    Some(Note::PrintBool) => {
                        let (yes, no, after) = (self.f.new_block(0), self.f.new_block(0), self.f.new_block(0));
                        self.f.branch(v, yes, &[], no, &[]);
                        for (block, s) in [(yes, "true"), (no, "false")] {
                            self.f.switch_to(block);
                            self.f.puts(s);
                            self.f.jump(after, &[]);
                        }
                        self.f.switch_to(after);
                    }
                    Some(Note::PrintStr) => {
                        self.s.runtime.insert("_s_print");
                        self.f.call("_s_print", &[v]);
                    }
                    _ => self.f.put_int(v),
                }
                if *prim == PrintLn {
                    self.f.puts("\n");
                }
                unit
            }
            PrintChar => {
                let v = self.term(&args[0]);
                self.f.put_char(v);
                unit
            }
            Puts(s) => {
                self.f.puts(s);
                unit
            }
            Read => self.f.get_int(),
            ReadChar => self.f.get_char(),
            ReadLine => {
                self.s.runtime.insert("_s_read");
                self.f.call("_s_read", &[])
            }
            Error => {
                match &args[0].kind {
                    TermKind::Str(s) => self.f.puts(&format!("error: {s}\n")),
                    _ => {
                        let message = self.term(&args[0]);
                        self.f.puts("error: ");
                        self.s.runtime.insert("_s_print");
                        self.f.call("_s_print", &[message]);
                        self.f.puts("\n");
                    }
                }
                self.fail();
                unit
            }
            Neg | Not => {
                let a = self.term(&args[0]);
                if *prim == Neg { self.f.neg(a) } else { self.f.lnot(a) }
            }
            Add if matches!(self.s.note(pos), Some(Note::Concat(..))) => {
                let Some(Note::Concat(ka, kb)) = self.s.note(pos) else { unreachable!() };
                let a = self.term(&args[0]);
                let a = self.to_string(a, ka);
                let b = self.term(&args[1]);
                let b = self.to_string(b, kb);
                self.s.runtime.insert("_s_cat");
                self.f.call("_s_cat", &[a, b])
            }
            Eq | Ne if self.s.note(pos) == Some(Note::StrEq) => {
                let a = self.term(&args[0]);
                let b = self.term(&args[1]);
                self.s.runtime.insert("_s_eq");
                let same = self.f.call("_s_eq", &[a, b]);
                if *prim == Eq { same } else { self.f.lnot(same) }
            }
            _ => {
                let a = self.term(&args[0]);
                let b = self.term(&args[1]);
                if matches!(prim, Div | Rem) && !self.f.const_value(b).is_some_and(|k| k != 0) {
                    let zero = self.f.int(0);
                    let by_zero = self.f.eq(b, zero);
                    let (stop, after) = (self.f.new_block(0), self.f.new_block(0));
                    self.f.branch(by_zero, stop, &[], after, &[]);
                    self.f.switch_to(stop);
                    self.f.puts("error: division by zero\n");
                    self.fail();
                    self.f.jump(after, &[]);
                    self.f.switch_to(after);
                }
                let f = &mut *self.f;
                match prim {
                    Add => f.add(a, b),
                    Sub => f.sub(a, b),
                    Mul => f.mul(a, b),
                    Div => f.div(a, b),
                    Rem => f.rem(a, b),
                    Eq => f.eq(a, b),
                    Ne => f.ne(a, b),
                    Lt => f.lt(a, b),
                    Le => f.le(a, b),
                    Gt => f.gt(a, b),
                    Ge => f.ge(a, b),
                    _ => unreachable!(),
                }
            }
        }
    }
}
