//! Types, and unification: making two types equal by working out what
//! their type variables must be.
//!
//! - Type variables are numbered, and bound (or not) in the `Unifier`'s
//!   table. Each has a *level*: how many generalizing scopes deep it was
//!   made. Generalizing a definition quantifies the variables deeper than
//!   it, so nothing that escaped into an outer scope gets quantified
//!   (Rémy's levels; see Kiselyov's "Efficient and insightful
//!   generalization").
//! - Rows are lists of labelled types ending in nothing or in a variable:
//!   a record's fields, and a function's effects, both. Unifying two rows
//!   finds each label of one in the other, in any order, and a row ending in
//!   a variable can grow (Leijen, "Extensible records with scoped labels").
//!   Labels may repeat; the first of a name is the one that's seen.

use bf::asm::fx::HashMap;
use std::fmt;

pub type TV = u32;

#[derive(Clone, Debug, PartialEq)]
pub enum Type {
    Var(TV),
    /// A named type: `Int`, `Bool`, `String`, a struct, an enum, or (in an
    /// effect row) an effect, each with its arguments.
    Con(String, Vec<Type>),
    /// Parameters, result, effects (a row).
    Fn(Vec<Type>, Box<Type>, Box<Type>),
    /// `()` is the empty tuple.
    Tuple(Vec<Type>),
    /// A record: a row of fields.
    Record(Box<Type>),
    RowEmpty,
    RowExtend(String, Box<Type>, Box<Type>),
    /// A type parameter written in a signature (`T` in `fn id<T>(x: T)`):
    /// it stands for any type, so it equals only itself.
    Skolem(TV, String),
    /// An associated type, `T::Item`: of trait `trait_` (by full name), for
    /// type `T`. Once `T` is known, it's what `T`'s impl of the trait says
    /// (see `Unifier::zonk`); for a type parameter, it equals only itself.
    Assoc(Box<Type>, String, String),
}

impl Type {
    pub fn con(name: &str) -> Type {
        Type::Con(name.into(), vec![])
    }
    pub fn int() -> Type {
        Type::con("Int")
    }
    pub fn bool() -> Type {
        Type::con("Bool")
    }
    pub fn string() -> Type {
        Type::con("String")
    }
    pub fn unit() -> Type {
        Type::Tuple(vec![])
    }
    pub fn func(params: Vec<Type>, ret: Type, eff: Type) -> Type {
        Type::Fn(params, Box::new(ret), Box::new(eff))
    }
    pub fn extend(label: &str, t: Type, rest: Type) -> Type {
        Type::RowExtend(label.into(), Box::new(t), Box::new(rest))
    }
}

/// `Trait<type>`: a requirement that a type has an impl of a trait.
#[derive(Clone, Debug, PartialEq)]
pub struct Pred {
    pub trait_: String,
    pub ty: Type,
}

/// A type with variables that each use may make different: `∀ vars. preds
/// => ty`. A function's dictionary parameters come in the order of `preds`.
#[derive(Clone, Debug)]
pub struct Scheme {
    pub vars: Vec<TV>,
    pub preds: Vec<Pred>,
    pub ty: Type,
}

/// What an impl says an associated type is: `type name = ty` in `impl
/// trait_ for head`, whose type parameters are `vars`.
#[derive(Clone)]
pub struct AssocImpl {
    pub trait_: String,
    pub name: String,
    pub vars: Vec<TV>,
    pub head: Type,
    pub ty: Type,
}

#[derive(Default, Clone)]
pub struct Unifier {
    binding: Vec<Option<Type>>,
    level: Vec<u32>,
    /// The level of the scope being worked on.
    pub current: u32,
    /// What the impls say the associated types are.
    pub assoc: Vec<AssocImpl>,
    /// Equations with an associated type that can't be decided yet (its
    /// type isn't known): tried again when more is known (see `settle`).
    deferred: Vec<(Type, Type)>,
    settling: bool,
}

/// Whether a type is an impl's head, as far as can be told yet.
enum Match {
    Yes,
    No,
    Unknown,
}

impl Unifier {
    pub fn fresh(&mut self) -> Type {
        Type::Var(self.fresh_var())
    }

    pub fn fresh_var(&mut self) -> TV {
        self.binding.push(None);
        self.level.push(self.current);
        (self.binding.len() - 1) as TV
    }

    pub fn skolem(&mut self, name: &str) -> Type {
        let v = self.fresh_var();
        Type::Skolem(v, name.into())
    }

    /// `t` with every bound variable replaced by what it's bound to.
    pub fn zonk(&self, t: &Type) -> Type {
        match t {
            Type::Var(v) => match &self.binding[*v as usize] {
                Some(b) => self.zonk(b),
                None => t.clone(),
            },
            Type::Con(n, args) => Type::Con(n.clone(), args.iter().map(|a| self.zonk(a)).collect()),
            Type::Fn(ps, r, e) => Type::func(ps.iter().map(|p| self.zonk(p)).collect(), self.zonk(r), self.zonk(e)),
            Type::Tuple(ts) => Type::Tuple(ts.iter().map(|x| self.zonk(x)).collect()),
            Type::Record(r) => Type::Record(Box::new(self.zonk(r))),
            Type::RowExtend(l, t, r) => Type::extend(l, self.zonk(t), self.zonk(r)),
            Type::RowEmpty | Type::Skolem(..) => t.clone(),
            Type::Assoc(of, trait_, name) => {
                let of = self.zonk(of);
                match self.normalize(&of, trait_, name) {
                    Some(t) => self.zonk(&t),
                    None => Type::Assoc(Box::new(of), trait_.clone(), name.clone()),
                }
            }
        }
    }

    /// `t`, with its outer variables followed (and an associated type
    /// whose type is known, what it is).
    fn shallow(&self, t: &Type) -> Type {
        match t {
            Type::Var(v) => match &self.binding[*v as usize] {
                Some(b) => self.shallow(b),
                None => t.clone(),
            },
            Type::Assoc(of, trait_, name) => match self.normalize(&self.zonk(of), trait_, name) {
                Some(t) => self.shallow(&t),
                None => t.clone(),
            },
            _ => t.clone(),
        }
    }

    /// What associated type `name` of `trait_` is for `of`, if an impl says
    /// (and `of` is known enough to tell which impl).
    fn normalize(&self, of: &Type, trait_: &str, name: &str) -> Option<Type> {
        for a in self.assoc.iter().filter(|a| a.trait_ == trait_ && a.name == name) {
            let mut map = HashMap::default();
            if let Match::Yes = matches(&a.head, of, &a.vars, &mut map) {
                return Some(substitute(&a.ty, &map));
            }
        }
        None
    }

    /// Unifies the equations put off (see `deferred`) whose associated
    /// types can be told now, until none can.
    fn settle(&mut self) -> Result<(), String> {
        if self.settling {
            return Ok(());
        }
        self.settling = true;
        let mut result = Ok(());
        loop {
            let pending = std::mem::take(&mut self.deferred);
            let before = pending.len();
            for (a, b) in pending {
                if let Err(e) = self.unify_now(&a, &b) {
                    result = Err(e);
                }
            }
            if result.is_err() || self.deferred.len() >= before {
                break;
            }
        }
        self.settling = false;
        result
    }

    /// The equations still put off: associated types whose types nothing
    /// decided (`T::Item`, for a `T` nothing says).
    pub fn unsettled(&mut self) -> Vec<(Type, Type)> {
        let _ = self.settle();
        std::mem::take(&mut self.deferred).into_iter().map(|(a, b)| (self.zonk(&a), self.zonk(&b))).collect()
    }

    /// Checks that `v` isn't in `t` (or `t` would be infinite), and lowers
    /// the levels of `t`'s variables to `v`'s, since they're now as visible
    /// as it is.
    fn occurs(&mut self, v: TV, t: &Type) -> Result<(), String> {
        match self.shallow(t) {
            Type::Var(w) => {
                if w == v {
                    return Err("a type that would contain itself".into());
                }
                let lv = self.level[v as usize];
                let lw = &mut self.level[w as usize];
                *lw = (*lw).min(lv);
                Ok(())
            }
            Type::Con(_, args) | Type::Tuple(args) => args.iter().try_for_each(|a| self.occurs(v, a)),
            Type::Fn(ps, r, e) => {
                ps.iter().try_for_each(|p| self.occurs(v, p))?;
                self.occurs(v, &r)?;
                self.occurs(v, &e)
            }
            Type::Record(r) => self.occurs(v, &r),
            Type::RowExtend(_, t, r) => {
                self.occurs(v, &t)?;
                self.occurs(v, &r)
            }
            Type::Assoc(of, ..) => self.occurs(v, &of),
            Type::RowEmpty | Type::Skolem(..) => Ok(()),
        }
    }

    fn bind(&mut self, v: TV, t: &Type) -> Result<(), String> {
        if let Type::Var(w) = self.shallow(t) {
            if w == v {
                return Ok(());
            }
        }
        self.occurs(v, t)?;
        self.binding[v as usize] = Some(t.clone());
        Ok(())
    }

    pub fn unify(&mut self, a: &Type, b: &Type) -> Result<(), String> {
        self.unify_now(a, b)?;
        // (what's been put off may be decided now)
        if !self.deferred.is_empty() {
            self.settle()?;
        }
        Ok(())
    }

    fn unify_now(&mut self, a: &Type, b: &Type) -> Result<(), String> {
        let (a, b) = (self.shallow(a), self.shallow(b));
        match (&a, &b) {
            (Type::Var(v), _) => self.bind(*v, &b),
            (_, Type::Var(v)) => self.bind(*v, &a),
            // (an associated type of a type parameter equals only itself; of
            // a type not known yet, it's put off until it is)
            (Type::Assoc(x, t, n), Type::Assoc(y, u, m)) if t == u && n == m && self.zonk(x) == self.zonk(y) => Ok(()),
            (Type::Assoc(of, ..), _) | (_, Type::Assoc(of, ..)) if undecided(&self.zonk(of)) => {
                self.deferred.push((a.clone(), b.clone()));
                Ok(())
            }
            (Type::Con(n, xs), Type::Con(m, ys)) if n == m && xs.len() == ys.len() => {
                xs.iter().zip(ys).try_for_each(|(x, y)| self.unify_now(x, y))
            }
            (Type::Tuple(xs), Type::Tuple(ys)) if xs.len() == ys.len() => xs.iter().zip(ys).try_for_each(|(x, y)| self.unify_now(x, y)),
            (Type::Fn(ps, r, e), Type::Fn(qs, s, f)) if ps.len() == qs.len() => {
                ps.iter().zip(qs).try_for_each(|(p, q)| self.unify_now(p, q))?;
                self.unify_now(r, s)?;
                self.unify_now(e, f)
            }
            (Type::Record(r), Type::Record(s)) => self.unify_now(r, s),
            (Type::RowEmpty, Type::RowEmpty) => Ok(()),
            (Type::RowExtend(l, t, r), _) => {
                let tail = self.row_tail(r);
                let (t2, s2) = self.find_label(&b, l)?;
                // (if r ends in the variable that just grew, the row is infinite)
                if let (Some(x), Some(y)) = (tail, self.row_tail(r)) {
                    if x != y {
                        return Err("a row that would contain itself".into());
                    }
                }
                self.unify_now(t, &t2)?;
                self.unify_now(r, &s2)
            }
            (Type::Skolem(x, _), Type::Skolem(y, _)) if x == y => Ok(()),
            // (a row with a label against one that can't have it)
            (Type::RowEmpty | Type::Skolem(..), Type::RowExtend(l, _, _)) => Err(format!("missing {}", short(l))),
            _ => Err(format!("{} and {} are different types", self.show(&a), self.show(&b))),
        }
    }

    /// The variable a row ends in, if it does.
    fn row_tail(&self, r: &Type) -> Option<TV> {
        match self.shallow(r) {
            Type::Var(v) => Some(v),
            Type::RowExtend(_, _, rest) => self.row_tail(&rest),
            _ => None,
        }
    }

    /// Row `row` as `label: t` then the rest: the first `label` in it,
    /// growing it if it ends in a variable.
    fn find_label(&mut self, row: &Type, label: &str) -> Result<(Type, Type), String> {
        match self.shallow(row) {
            Type::RowExtend(l, t, rest) if l == label => Ok((*t, *rest)),
            Type::RowExtend(l, t, rest) => {
                let (found, rest) = self.find_label(&rest, label)?;
                Ok((found, Type::RowExtend(l, t, Box::new(rest))))
            }
            Type::Var(v) => {
                let (t, rest) = (self.fresh_at(v), self.fresh_at(v));
                self.bind(v, &Type::extend(label, t.clone(), rest.clone()))?;
                Ok((t, rest))
            }
            // (a row that ends, or ends in a skolem, can't grow)
            Type::RowEmpty | Type::Skolem(..) => Err(format!("missing {}", short(label))),
            other => Err(format!("{} isn't a row", self.show(&other))),
        }
    }

    /// A new variable at the level of `v`.
    fn fresh_at(&mut self, v: TV) -> Type {
        let w = self.fresh_var();
        self.level[w as usize] = self.level[v as usize];
        Type::Var(w)
    }

    /// The scheme that quantifies the variables of `t` (and `preds`) deeper
    /// than the current scope, and the type parameters (skolems) `rigid`.
    pub fn generalize(&mut self, t: &Type, preds: Vec<Pred>, rigid: &[TV]) -> Scheme {
        let t = self.zonk(t);
        let preds: Vec<Pred> = preds.iter().map(|p| Pred { trait_: p.trait_.clone(), ty: self.zonk(&p.ty) }).collect();
        let mut vars = vec![];
        let mut map = HashMap::default();
        let ty = self.quantify(&t, &mut vars, &mut map, rigid);
        let preds = preds.iter().map(|p| Pred { trait_: p.trait_.clone(), ty: self.quantify(&p.ty, &mut vars, &mut map, rigid) }).collect();
        Scheme { vars, preds, ty }
    }

    fn quantify(&mut self, t: &Type, vars: &mut Vec<TV>, map: &mut HashMap<TV, TV>, rigid: &[TV]) -> Type {
        match t {
            Type::Var(v) if self.level[*v as usize] > self.current => {
                let q = *map.entry(*v).or_insert_with(|| {
                    vars.push(*v);
                    *v
                });
                Type::Var(q)
            }
            Type::Skolem(v, _) if rigid.contains(v) => {
                map.entry(*v).or_insert_with(|| {
                    vars.push(*v);
                    *v
                });
                Type::Var(*v)
            }
            Type::Con(n, args) => Type::Con(n.clone(), args.iter().map(|a| self.quantify(a, vars, map, rigid)).collect()),
            Type::Fn(ps, r, e) => Type::func(
                ps.iter().map(|p| self.quantify(p, vars, map, rigid)).collect(),
                self.quantify(r, vars, map, rigid),
                self.quantify(e, vars, map, rigid),
            ),
            Type::Tuple(ts) => Type::Tuple(ts.iter().map(|x| self.quantify(x, vars, map, rigid)).collect()),
            Type::Record(r) => Type::Record(Box::new(self.quantify(r, vars, map, rigid))),
            Type::RowExtend(l, t, r) => Type::extend(l, self.quantify(t, vars, map, rigid), self.quantify(r, vars, map, rigid)),
            Type::Assoc(of, trait_, name) => Type::Assoc(Box::new(self.quantify(of, vars, map, rigid)), trait_.clone(), name.clone()),
            _ => t.clone(),
        }
    }

    /// A use of a scheme: its variables replaced by new ones.
    pub fn instantiate(&mut self, s: &Scheme) -> (Type, Vec<Pred>) {
        let map: HashMap<TV, Type> = s.vars.iter().map(|&v| (v, self.fresh())).collect();
        let ty = substitute(&s.ty, &map);
        let preds = s.preds.iter().map(|p| Pred { trait_: p.trait_.clone(), ty: substitute(&p.ty, &map) }).collect();
        (ty, preds)
    }

    /// A type for people: variables as `a`, `b`, ...
    pub fn show(&self, t: &Type) -> String {
        let t = self.zonk(t);
        let names = std::cell::RefCell::new(HashMap::default());
        format!("{}", Shown(&t, &names))
    }
}

/// The type variables (and type parameters) in `t` (after `zonk`).
pub fn vars_in(t: &Type, out: &mut Vec<TV>) {
    match t {
        Type::Var(v) | Type::Skolem(v, _) => out.push(*v),
        Type::Con(_, args) | Type::Tuple(args) => args.iter().for_each(|a| vars_in(a, out)),
        Type::Fn(ps, r, e) => {
            ps.iter().for_each(|p| vars_in(p, out));
            vars_in(r, out);
            vars_in(e, out);
        }
        Type::Record(r) => vars_in(r, out),
        Type::RowExtend(_, t, rest) => {
            vars_in(t, out);
            vars_in(rest, out);
        }
        Type::Assoc(of, ..) => vars_in(of, out),
        Type::RowEmpty => {}
    }
}

/// Whether a type is unknown, so that what an associated type of it is
/// can't be told yet (a type parameter, a skolem, is known: it's itself).
fn undecided(t: &Type) -> bool {
    matches!(t, Type::Var(_)) || matches!(t, Type::Assoc(of, ..) if undecided(of))
}

/// Whether `t` is impl head `head` (whose type parameters are `vars`):
/// `map` says what each parameter is, if it is. Where `t` has a variable
/// and `head` has more, it can't be told yet.
fn matches(head: &Type, t: &Type, vars: &[TV], map: &mut HashMap<TV, Type>) -> Match {
    match (head, t) {
        (Type::Var(v), _) if vars.contains(v) => match map.get(v) {
            Some(seen) if seen == t => Match::Yes,
            Some(_) => Match::No,
            None => {
                map.insert(*v, t.clone());
                Match::Yes
            }
        },
        (_, Type::Var(_)) => Match::Unknown,
        (Type::Con(n, ps), Type::Con(m, ts)) if n == m && ps.len() == ts.len() => all(ps.iter().zip(ts), vars, map),
        (Type::Tuple(ps), Type::Tuple(ts)) if ps.len() == ts.len() => all(ps.iter().zip(ts), vars, map),
        (Type::Fn(ps, r, _), Type::Fn(ts, s, _)) if ps.len() == ts.len() => all(ps.iter().zip(ts).chain([(&**r, &**s)]), vars, map),
        _ if head == t => Match::Yes,
        _ => Match::No,
    }
}

fn all<'a>(pairs: impl Iterator<Item = (&'a Type, &'a Type)>, vars: &[TV], map: &mut HashMap<TV, Type>) -> Match {
    let mut unknown = false;
    for (h, t) in pairs {
        match matches(h, t, vars, map) {
            Match::No => return Match::No,
            Match::Unknown => unknown = true,
            Match::Yes => {}
        }
    }
    if unknown { Match::Unknown } else { Match::Yes }
}

/// `t` with variables replaced as `map` says.
pub fn substitute(t: &Type, map: &HashMap<TV, Type>) -> Type {
    match t {
        Type::Var(v) => map.get(v).cloned().unwrap_or_else(|| t.clone()),
        Type::Con(n, args) => Type::Con(n.clone(), args.iter().map(|a| substitute(a, map)).collect()),
        Type::Fn(ps, r, e) => Type::func(ps.iter().map(|p| substitute(p, map)).collect(), substitute(r, map), substitute(e, map)),
        Type::Tuple(ts) => Type::Tuple(ts.iter().map(|x| substitute(x, map)).collect()),
        Type::Record(r) => Type::Record(Box::new(substitute(r, map))),
        Type::RowExtend(l, t, r) => Type::extend(l, substitute(t, map), substitute(r, map)),
        Type::Assoc(of, trait_, name) => Type::Assoc(Box::new(substitute(of, map)), trait_.clone(), name.clone()),
        _ => t.clone(),
    }
}

/// A type, printed with its variables named in the order they appear.
struct Shown<'a>(&'a Type, &'a std::cell::RefCell<HashMap<TV, String>>);

impl fmt::Display for Shown<'_> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        let name = |v: TV| {
            let mut names = self.1.borrow_mut();
            let n = names.len();
            names.entry(v).or_insert_with(|| ((b'a' + (n % 26) as u8) as char).to_string()).clone()
        };
        match self.0 {
            Type::Var(v) => write!(f, "{}", name(*v)),
            Type::Skolem(_, n) => write!(f, "{n}"),
            Type::Con(n, args) if args.is_empty() => write!(f, "{}", short(n)),
            Type::Con(n, args) => {
                write!(f, "{}<", short(n))?;
                for (i, a) in args.iter().enumerate() {
                    write!(f, "{}{}", if i > 0 { ", " } else { "" }, Shown(a, self.1))?;
                }
                write!(f, ">")
            }
            Type::Tuple(ts) => {
                write!(f, "(")?;
                for (i, t) in ts.iter().enumerate() {
                    write!(f, "{}{}", if i > 0 { ", " } else { "" }, Shown(t, self.1))?;
                }
                write!(f, ")")
            }
            Type::Fn(ps, r, e) => {
                write!(f, "fn(")?;
                for (i, p) in ps.iter().enumerate() {
                    write!(f, "{}{}", if i > 0 { ", " } else { "" }, Shown(p, self.1))?;
                }
                write!(f, ") -> {}", Shown(r, self.1))?;
                if !matches!(**e, Type::Var(_) | Type::RowEmpty) {
                    write!(f, " with {}", Shown(e, self.1))?;
                }
                Ok(())
            }
            Type::Record(r) => write!(f, "{{{}}}", Shown(r, self.1)),
            Type::Assoc(of, _, name) => write!(f, "{}::{name}", Shown(of, self.1)),
            Type::RowEmpty => Ok(()),
            Type::RowExtend(l, t, r) => {
                if let Type::Con(n, _) = &**t {
                    if n == l {
                        // (an effect)
                        write!(f, "{}", Shown(t, self.1))?;
                    } else {
                        write!(f, "{}: {}", short(l), Shown(t, self.1))?;
                    }
                } else {
                    write!(f, "{}: {}", short(l), Shown(t, self.1))?;
                }
                match &**r {
                    Type::RowEmpty => Ok(()),
                    Type::Var(_) => write!(f, ", ..{}", Shown(r, self.1)),
                    _ => write!(f, ", {}", Shown(r, self.1)),
                }
            }
        }
    }
}

/// A full name's last part, for messages.
fn short(n: &str) -> &str {
    n.rsplit("::").next().unwrap_or(n)
}
