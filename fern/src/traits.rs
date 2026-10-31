//! Traits: meeting each requirement (`Show<List<Int>>`) with a dictionary,
//! and filling in the placeholders the code left for them.
//!
//! A requirement is met by, in order:
//! 1. a dictionary the function was given (a bound it declared, or one
//!    inferred for its type variables): `Param`;
//! 2. a supertrait's part of one (an `Ord` dictionary has its `Eq`'s):
//!    `Super`;
//! 3. an impl whose head matches the type (`impl<T: Show> Show for
//!    List<T>` for `List<Int>`), with its own requirements met the same way
//!    (`Show<Int>`): `Impl`;
//! 4. if the function is being generalized and the type is one of its type
//!    variables: a new dictionary parameter.
//!
//! Then the core's placeholders become real code: a dictionary is a call
//! of the impl's dictionary function (or a parameter, or a part of one); a
//! method call on a dictionary from an impl calls the impl's method
//! directly; and `==`/`<` on `Int`, `Bool` or `String` are machine
//! comparisons.

use crate::checker::{default_name, Checker, Dict, Res};
use crate::core::{Cmp, Core, Eff, Name, Prim};
use crate::expr::{arith_trait, EQ, ORD};
use crate::types::{Pred, Type, TV};
use bf::asm::fx::HashMap;

impl Checker<'_> {
    /// Meets every requirement in `self.wanted`. `given` are the
    /// dictionaries the function has (and, if `generalize`, gets the new
    /// parameters added): it's what's returned, the function's dictionary
    /// parameters in order.
    pub fn solve(&mut self, given: &mut Vec<(Pred, Name)>, generalize: bool) -> Res<Vec<(Pred, Name)>> {
        let wanted = std::mem::take(&mut self.wanted);
        for w in wanted {
            let dict = self.entail(&w.pred, given, generalize).map_err(|m| (w.pos, m))?;
            self.holes[w.hole] = Some(dict);
        }
        Ok(given.clone())
    }

    fn entail(&mut self, pred: &Pred, given: &mut Vec<(Pred, Name)>, generalize: bool) -> Result<Dict, String> {
        let ty = self.u.zonk(&pred.ty);
        // 1, 2: one it has, or part of one
        for (g, name) in given.iter() {
            let gt = self.u.zonk(&g.ty);
            if gt != ty {
                continue;
            }
            if g.trait_ == pred.trait_ {
                return Ok(Dict::Param(name.clone(), g.trait_.clone()));
            }
            if let Some(path) = self.super_path(&g.trait_, &pred.trait_) {
                return Ok(path.into_iter().fold(Dict::Param(name.clone(), g.trait_.clone()), |d, i| Dict::Super(Box::new(d), i)));
            }
        }
        // (an associated type of a type parameter: the part of that type's
        // dictionary for one of the traits the associated type has to have)
        if let Type::Assoc(of, trait_, name) = &ty {
            let of = self.u.zonk(of);
            for (g, gname) in given.iter() {
                if g.trait_ != *trait_ || self.u.zonk(&g.ty) != of {
                    continue;
                }
                let bounds = self.traits[trait_].assoc_bounds.clone();
                for (j, (a, b)) in bounds.iter().enumerate() {
                    if a != name {
                        continue;
                    }
                    let part = Dict::Assoc(Box::new(Dict::Param(gname.clone(), g.trait_.clone())), j);
                    if *b == pred.trait_ {
                        return Ok(part);
                    }
                    if let Some(path) = self.super_path(b, &pred.trait_) {
                        return Ok(path.into_iter().fold(part, |d, i| Dict::Super(Box::new(d), i)));
                    }
                }
            }
            return Err(format!("{} doesn't implement {} (say so where {} is declared: `type {}: {}`)", self.u.show(&ty), short(&pred.trait_), name, name, short(&pred.trait_)));
        }
        match &ty {
            // 4: a type variable of the function being generalized
            Type::Var(_) if generalize => {
                let name = self.fresh_name("dict");
                given.push((Pred { trait_: pred.trait_.clone(), ty: ty.clone() }, name.clone()));
                Ok(Dict::Param(name, pred.trait_.clone()))
            }
            Type::Var(_) => Err(format!("can't tell which type this needs {} for", short(&pred.trait_))),
            Type::Skolem(_, name) => Err(format!("{name} needs the bound {name}: {}", short(&pred.trait_))),
            // 3: an impl
            _ => {
                for k in 0..self.impls.len() {
                    if self.impls[k].trait_ != pred.trait_ {
                        continue;
                    }
                    let mut subst = HashMap::default();
                    let (vars, head) = (self.impls[k].vars.clone(), self.impls[k].head.clone());
                    if !self.matches(&head, &ty, &vars, &mut subst) {
                        continue;
                    }
                    let context = self.impls[k].context.clone();
                    let mut subs = vec![];
                    for c in context {
                        let p = Pred { trait_: c.trait_, ty: crate::types::substitute(&c.ty, &subst) };
                        subs.push(self.entail(&p, given, generalize)?);
                    }
                    return Ok(Dict::Impl(k, subs));
                }
                Err(format!("{} doesn't implement {}", self.u.show(&ty), short(&pred.trait_)))
            }
        }
    }

    /// Whether `pattern` (an impl's head, with variables `vars`) matches
    /// `t`, binding the variables in `subst` (never `t`'s).
    fn matches(&self, pattern: &Type, t: &Type, vars: &[TV], subst: &mut HashMap<TV, Type>) -> bool {
        let t = self.u.zonk(t);
        match (pattern, &t) {
            (Type::Var(v), _) if vars.contains(v) => match subst.get(v) {
                Some(bound) => *bound == t,
                None => {
                    subst.insert(*v, t.clone());
                    true
                }
            },
            (Type::Con(n, xs), Type::Con(m, ys)) => n == m && xs.len() == ys.len() && xs.iter().zip(ys).all(|(x, y)| self.matches(x, y, vars, subst)),
            (Type::Tuple(xs), Type::Tuple(ys)) => xs.len() == ys.len() && xs.iter().zip(ys).all(|(x, y)| self.matches(x, y, vars, subst)),
            (Type::Fn(ps, r, _), Type::Fn(qs, s, _)) => {
                ps.len() == qs.len() && ps.iter().zip(qs).all(|(x, y)| self.matches(x, y, vars, subst)) && self.matches(r, s, vars, subst)
            }
            _ => *pattern == t,
        }
    }

    /// How to get trait `to`'s dictionary from one of `from`'s: the
    /// supertrait positions, in order, if `to` is a supertrait of `from`.
    fn super_path(&self, from: &str, to: &str) -> Option<Vec<usize>> {
        let t = self.traits.get(from)?;
        for (i, s) in t.supers.iter().enumerate() {
            if s == to {
                return Some(vec![i]);
            }
            if let Some(mut rest) = self.super_path(s, to) {
                rest.insert(0, i);
                return Some(rest);
            }
        }
        None
    }

    fn dict_core(&self, d: &Dict) -> Core {
        match d {
            Dict::Param(n, _) => Core::Local(n.clone()),
            Dict::Impl(k, subs) => Core::CallGlobal(self.impls[*k].dict_fn.clone(), subs.iter().map(|s| self.dict_core(s)).collect(), Eff::Pure),
            Dict::Super(inner, i) => {
                // (a dictionary's supertraits' come after its methods)
                let trait_ = self.dict_trait(inner);
                let n = self.traits[&trait_].methods.len();
                Core::Proj(Box::new(self.dict_core(inner)), n + i)
            }
            Dict::Assoc(inner, j) => {
                // (and its associated types' after those)
                let t = &self.traits[&self.dict_trait(inner)];
                Core::Proj(Box::new(self.dict_core(inner)), t.methods.len() + t.supers.len() + j)
            }
        }
    }

    /// The trait a dictionary is for.
    fn dict_trait(&self, d: &Dict) -> String {
        match d {
            Dict::Param(_, t) => t.clone(),
            Dict::Impl(k, _) => self.impls[*k].trait_.clone(),
            Dict::Super(inner, i) => self.traits[&self.dict_trait(inner)].supers[*i].clone(),
            Dict::Assoc(inner, j) => self.traits[&self.dict_trait(inner)].assoc_bounds[*j].1.clone(),
        }
    }

    /// The core with its placeholders filled in. `dicts` are the function's
    /// dictionary parameters (for `DictArgs`).
    pub fn finalize(&self, c: Core, dicts: &[Name]) -> Core {
        let f = |c: Core| self.finalize(c, dicts);
        let bx = |c: Box<Core>| Box::new(self.finalize(*c, dicts));
        match c {
            Core::DictHole(h) => self.dict_core(self.hole(h)),
            Core::Pending(i) => f(self.resolved[i].clone().expect("resolved before its group is finished")),
            Core::DictArgs => unreachable!("only in a call's arguments"),
            Core::MethodCall(h, trait_, k, args, eff) => {
                let args: Vec<Core> = args.into_iter().map(f).collect();
                let eff = self.eff(eff);
                let d = self.hole(h);
                match d {
                    // an impl's: its method, called directly
                    Dict::Impl(i, subs) if self.impls[*i].trait_ == trait_ => {
                        let mut all: Vec<Core> = subs.iter().map(|s| self.dict_core(s)).collect();
                        match self.impls[*i].methods.get(&k) {
                            Some(m) => {
                                all.extend(args);
                                Core::CallGlobal(m.clone(), all, eff)
                            }
                            None => {
                                let mut a = vec![Core::CallGlobal(self.impls[*i].dict_fn.clone(), all, Eff::Pure)];
                                a.extend(args);
                                Core::CallGlobal(default_name(&trait_, k), a, eff)
                            }
                        }
                    }
                    _ => Core::App(Box::new(Core::Proj(Box::new(self.dict_core(d)), k)), args, eff),
                }
            }
            Core::Arith(p, h, args) => {
                // the machine's arithmetic, for an Int; else the trait's method
                if let Dict::Impl(i, _) = self.hole(h) {
                    if self.impls[*i].head == Type::int() {
                        return Core::Prim(p, args.into_iter().map(f).collect());
                    }
                }
                let (trait_, method) = arith_trait(p);
                let k = self.method_index(trait_, method);
                f(Core::MethodCall(h, trait_.to_string(), k, args, self.declared_eff(trait_, k)))
            }
            Core::Compare(cmp, h, a, b) => {
                let (a, b) = (f(*a), f(*b));
                let d = self.hole(h);
                // the machine's comparison, for the types it has one for
                if let Dict::Impl(i, _) = d {
                    if let Type::Con(n, args) = &self.impls[*i].head {
                        if args.is_empty() && (n == "Int" || n == "Bool") {
                            let p = match cmp {
                                Cmp::Eq => Prim::IntEq,
                                Cmp::Ne => Prim::IntNe,
                                Cmp::Lt => Prim::IntLt,
                                Cmp::Le => Prim::IntLe,
                                Cmp::Gt => Prim::IntGt,
                                Cmp::Ge => Prim::IntGe,
                            };
                            return Core::Prim(p, vec![a, b]);
                        }
                        if args.is_empty() && n == "String" {
                            let not = |c| Core::Prim(Prim::Not, vec![c]);
                            return match cmp {
                                Cmp::Eq => Core::Prim(Prim::StrEq, vec![a, b]),
                                Cmp::Ne => not(Core::Prim(Prim::StrEq, vec![a, b])),
                                Cmp::Lt => Core::Prim(Prim::StrLt, vec![a, b]),
                                Cmp::Gt => Core::Prim(Prim::StrLt, vec![b, a]),
                                Cmp::Le => not(Core::Prim(Prim::StrLt, vec![b, a])),
                                Cmp::Ge => not(Core::Prim(Prim::StrLt, vec![a, b])),
                            };
                        }
                    }
                }
                // else the trait's methods: Eq's eq, and Ord's cmp against 0
                let method = |trait_: &str, k: usize, args: Vec<Core>| match d {
                    Dict::Impl(i, subs) if self.impls[*i].trait_ == trait_ && self.impls[*i].methods.contains_key(&k) => {
                        let mut all: Vec<Core> = subs.iter().map(|s| self.dict_core(s)).collect();
                        all.extend(args);
                        Core::CallGlobal(self.impls[*i].methods[&k].clone(), all, self.declared_eff(trait_, k))
                    }
                    _ => Core::App(Box::new(Core::Proj(Box::new(self.dict_core(d)), k)), args, self.declared_eff(trait_, k)),
                };
                let eq = self.method_index(EQ, "eq");
                let cmp_k = self.method_index(ORD, "cmp");
                match cmp {
                    Cmp::Eq => method(EQ, eq, vec![a, b]),
                    Cmp::Ne => Core::Prim(Prim::Not, vec![method(EQ, eq, vec![a, b])]),
                    _ => {
                        let c = method(ORD, cmp_k, vec![a, b]);
                        let p = match cmp {
                            Cmp::Lt => Prim::IntLt,
                            Cmp::Le => Prim::IntLe,
                            Cmp::Gt => Prim::IntGt,
                            _ => Prim::IntGe,
                        };
                        Core::Prim(p, vec![c, Core::Int(0)])
                    }
                }
            }
            Core::CallGlobal(name, args, eff) => {
                let mut out = vec![];
                for a in args {
                    if matches!(a, Core::DictArgs) {
                        out.extend(dicts.iter().map(|d| Core::Local(d.clone())));
                    } else {
                        out.push(f(a));
                    }
                }
                Core::CallGlobal(name, out, self.eff(eff))
            }
            Core::Lam(id, ps, b, eff) => Core::Lam(id, ps, bx(b), self.eff(eff)),
            Core::App(g, args, eff) => Core::App(bx(g), args.into_iter().map(f).collect(), self.eff(eff)),
            Core::Let(n, v, b) => Core::Let(n, bx(v), bx(b)),
            Core::If(c, t, e) => Core::If(bx(c), bx(t), bx(e)),
            Core::Match(s, arms) => Core::Match(bx(s), arms.into_iter().map(|(p, b)| (p, f(b))).collect()),
            Core::Con(t, args) => Core::Con(t, args.into_iter().map(f).collect()),
            Core::Tuple(xs) => Core::Tuple(xs.into_iter().map(f).collect()),
            Core::Proj(x, i) => Core::Proj(bx(x), i),
            Core::Field(x, i) => Core::Field(bx(x), i),
            Core::SetProj(x, i, v) => Core::SetProj(bx(x), i, bx(v)),
            Core::Record(fs) => Core::Record(fs.into_iter().map(|(l, v)| (l, f(v))).collect()),
            Core::RecGet(r, l) => Core::RecGet(bx(r), l),
            Core::RecExtend(r, fs) => Core::RecExtend(bx(r), fs.into_iter().map(|(l, v)| (l, f(v))).collect()),
            Core::Prim(p, args) => Core::Prim(p, args.into_iter().map(f).collect()),
            Core::Seq(a, b) => Core::Seq(bx(a), bx(b)),
            Core::While(c, b) => Core::While(bx(c), bx(b)),
            Core::Loop(b) => Core::Loop(bx(b)),
            Core::Return(v) => Core::Return(bx(v)),
            Core::NewRef(v) => Core::NewRef(bx(v)),
            Core::GetRef(v) => Core::GetRef(bx(v)),
            Core::SetRef(r, v) => Core::SetRef(bx(r), bx(v)),
            Core::Handle { eff, body, ret: (v, r), ops } => Core::Handle {
                eff,
                body: bx(body),
                ret: (v, bx(r)),
                ops: ops.into_iter().map(|(ps, res, b)| (ps, res, f(b))).collect(),
            },
            Core::Perform { eff, op, args } => Core::Perform { eff, op, args: args.into_iter().map(f).collect() },
            Core::Located(pos, e) => Core::Located(pos, bx(e)),
            c @ (Core::Int(_) | Core::Str(_) | Core::Local(_) | Core::Break | Core::Continue | Core::Panic(_)) => c,
        }
    }

    fn hole(&self, h: usize) -> &Dict {
        self.holes[h].as_ref().expect("every requirement is met by now")
    }

    fn method_index(&self, trait_: &str, name: &str) -> usize {
        self.traits[trait_].methods.iter().position(|m| m.name == name).expect("the standard library's traits")
    }
}

fn short(n: &str) -> &str {
    n.rsplit("::").next().unwrap_or(n)
}
