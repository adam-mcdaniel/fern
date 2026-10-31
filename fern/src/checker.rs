//! Type checking: inference for the whole program, producing the core
//! program (`core.rs`). This file has the declarations and the order things
//! are checked in; `expr.rs` has expressions and patterns, `traits.rs` the
//! traits (finding impls, and dictionaries).
//!
//! The order:
//! 1. Every struct, enum, effect and trait's declaration, and every impl's
//!    head (`impl<T: Show> Show for List<T>`): what using them needs.
//! 2. Each type's methods' types, from their signatures (written out in
//!    full, so nothing waits on a method's body).
//! 3. The functions, a recursive group at a time (Tarjan's algorithm on
//!    which call which), each group generalized together: so a function's
//!    type is known, and polymorphic, before anything outside its group
//!    uses it. A method call or field whose receiver's type isn't known
//!    where it's written is worked out at the end of its group (`Use`).
//! 4. The methods' bodies, each against its signature.
//! 5. Each impl's methods, against the trait's signatures, and the traits'
//!    default methods. (Functions only use impls through dictionaries, so
//!    they don't need these first.)
//! 6. `main`: it may only have the `Io` effect.

use crate::ast::{self, Expr, ExprKind, FnDef, TypeExpr};
use crate::core::{self, Core, Eff, Name};
use crate::lexer::Pos;
use crate::modules::{Def, ItemKind, Ns, Program};
use crate::types::{Pred, Scheme, Type, Unifier, TV};
use bf::asm::fx::{HashMap, HashSet};

pub type Error = (Pos, String);
pub type Res<T> = Result<T, Error>;

pub struct StructInfo {
    pub vars: Vec<TV>,
    pub fields: Vec<(String, Type)>,
    /// Whether a value of it is just its one field, with no block of its
    /// own: a struct of one field that's never set (see `expr::struct_lit`).
    pub unboxed: bool,
    /// Which of its fields something may set (by name: anything sets a
    /// field of that name); the others never change once it's made.
    pub set: Vec<bool>,
}

pub struct EnumInfo {
    pub vars: Vec<TV>,
    pub variants: Vec<(String, Vec<Type>)>,
}

pub struct OpSig {
    pub name: String,
    /// The operation's own type parameters (`fn fail<A>(..) -> A`).
    pub vars: Vec<TV>,
    pub params: Vec<Type>,
    pub ret: Type,
}

pub struct EffectInfo {
    pub vars: Vec<TV>,
    pub ops: Vec<OpSig>,
}

pub struct MethodSig {
    pub name: String,
    pub vars: Vec<TV>,
    /// The parameters (`self` first), result and effects (a row ending in
    /// `tail`), with `Self` as the trait's `self_var`.
    pub params: Vec<Type>,
    pub ret: Type,
    pub eff: Type,
    pub tail: TV,
    pub has_default: bool,
}

pub struct TraitInfo {
    pub name: String,
    pub item: usize,
    pub self_var: TV,
    /// Its associated types, by name, and the traits they have to have
    /// (each one's dictionary is in the trait's, after the supertraits').
    pub assoc: Vec<String>,
    pub assoc_bounds: Vec<(String, String)>,
    /// The traits it requires (`trait Ord: Eq`), by full name: their
    /// dictionaries come after the methods in its dictionary.
    pub supers: Vec<String>,
    pub methods: Vec<MethodSig>,
}

pub struct ImplInfo {
    pub item: usize,
    pub trait_: String,
    pub vars: Vec<TV>,
    pub head: Type,
    /// What the impl requires of its type parameters (`T: Show`): its
    /// dictionary function's parameters.
    pub context: Vec<Pred>,
    /// The function making its dictionary.
    pub dict_fn: String,
    /// Each method it defines (by the trait's numbering): its function.
    pub methods: HashMap<usize, String>,
}

/// A local variable.
#[derive(Clone)]
pub struct Local {
    pub name: Name,
    pub ty: Type,
    pub mutable: bool,
    /// Where it's declared, if it's one to warn of if it's never used.
    pub at: Option<Pos>,
}

/// A method call or field, `recv.name(args)` or `recv.name`, whose
/// receiver's type wasn't known where it was written: which method or
/// field it is waits for that (see `resolve_uses` in expr.rs).
pub struct Use {
    pub recv: Core,
    pub recv_ty: Type,
    pub name: String,
    /// What's done with it: read, set, or called.
    pub what: UseKind,
    pub result: Type,
    /// The effects where it was written: a method's go there.
    pub here: Type,
    pub module: usize,
    pub pos: Pos,
    /// Its number, in `resolved`.
    pub id: usize,
}

/// What a `Use` does with what it names.
pub enum UseKind {
    /// `recv.name`: reads a field.
    Get,
    /// `recv.name = value`: sets a field, to the value (and its type).
    Set(Core, Type),
    /// `recv.name(args)`: calls a method, with the arguments and their types.
    Call(Vec<(Core, Type)>),
}

/// A trait requirement found in the code, to be met by a dictionary.
pub struct Wanted {
    pub pred: Pred,
    pub hole: usize,
    pub pos: Pos,
}

/// How a requirement is met.
#[derive(Clone, Debug)]
pub enum Dict {
    /// One of the function's dictionary parameters (for this trait).
    Param(Name, String),
    /// An impl's dictionary, made from these for its own requirements.
    Impl(usize, Vec<Dict>),
    /// The dictionary of a trait another's requires: the `i`th of its
    /// supertraits'.
    Super(Box<Dict>, usize),
    /// The dictionary of a trait an associated type has to have: the `j`th
    /// of its trait's (see `TraitInfo::assoc_bounds`).
    Assoc(Box<Dict>, usize),
}

pub struct Checker<'p> {
    pub prog: &'p Program,
    /// The `extern fn`s, by item: parameters, result, number (in
    /// `externs`, named once however many modules declare them), and
    /// whether calling it has the Io effect.
    pub extern_sigs: HashMap<usize, (Vec<Type>, Type, usize, bool)>,
    pub externs: Vec<(String, usize)>,
    pub u: Unifier,
    pub structs: HashMap<String, StructInfo>,
    pub enums: HashMap<String, EnumInfo>,
    pub effects: HashMap<String, EffectInfo>,
    pub traits: HashMap<String, TraitInfo>,
    pub impls: Vec<ImplInfo>,
    /// The functions' types, once their groups are checked.
    pub schemes: HashMap<usize, Scheme>,
    /// The group being checked: each function's type so far.
    pub group: HashMap<usize, Type>,
    pub funcs: Vec<core::Func>,

    // what the function being checked needs
    pub module: usize,
    pub scopes: Vec<HashMap<String, Local>>,
    pub effect: Type,
    pub ret: Option<Type>,
    pub loops: usize,
    pub wanted: Vec<Wanted>,
    pub holes: Vec<Option<Dict>>,
    /// The requirements of the scheme `callee_type` just instantiated, for
    /// `direct_call`.
    pub pending_preds: Vec<Pred>,
    /// Whether the program calls `read_int`.
    pub reads_input: bool,
    /// The type names in scope in the body being checked: its signature's
    /// type parameters, and `Self`.
    pub body_ctx: TyCtx,
    /// Method calls and fields whose receivers' types weren't known yet,
    /// in the group being checked (see `Use`), and what each came to.
    pub uses: Vec<Use>,
    pub resolved: Vec<Option<Core>>,
    counter: usize,
    /// The variables to warn of if they're never used (by where they're
    /// declared, which stays the same if a body's checked again), and
    /// which have been.
    pub declared: Vec<(Pos, String)>,
    pub used: std::cell::RefCell<HashSet<(usize, usize, usize)>>,
    /// The errors in functions' and methods' bodies so far: checking goes
    /// on past one, to find the rest (see `functions`).
    pub errors: Vec<(Pos, String)>,
}

/// Checks the program: its core form, or its errors (as many as can be
/// found: an error in a function's body doesn't stop the others' being
/// checked).
pub fn check(prog: &Program) -> Result<core::Program, Vec<(Pos, String)>> {
    let one = |e: (Pos, String)| vec![e];
    let mut c = Checker {
        prog,
        extern_sigs: HashMap::default(),
        externs: vec![],
        u: Unifier::default(),
        structs: HashMap::default(),
        enums: HashMap::default(),
        effects: HashMap::default(),
        traits: HashMap::default(),
        impls: vec![],
        schemes: HashMap::default(),
        group: HashMap::default(),
        funcs: vec![],
        module: 0,
        scopes: vec![],
        effect: Type::RowEmpty,
        ret: None,
        loops: 0,
        wanted: vec![],
        holes: vec![],
        pending_preds: vec![],
        reads_input: false,
        body_ctx: TyCtx::default(),
        uses: vec![],
        resolved: vec![],
        counter: 0,
        declared: vec![],
        used: Default::default(),
        errors: vec![],
    };
    use bf::asm::log::{phase, DEBUG};
    let p = phase(DEBUG, "declarations, and impls' heads");
    c.declarations().map_err(one)?;
    c.extern_fns().map_err(one)?;
    drop(p);
    let p = phase(DEBUG, "methods' signatures");
    c.method_signatures().map_err(one)?;
    drop(p);
    let p = phase(DEBUG, "functions, a group at a time");
    c.functions().map_err(one)?;
    drop(p);
    let p = phase(DEBUG, "methods' bodies");
    c.method_bodies().map_err(one)?;
    drop(p);
    let p = phase(DEBUG, "impls' methods");
    c.impl_methods().map_err(one)?;
    drop(p);
    if !c.errors.is_empty() {
        let mut errors = std::mem::take(&mut c.errors);
        errors.sort_by_key(|(p, _)| (p.file, p.line, p.col));
        errors.dedup();
        return Err(errors);
    }
    let main = c.main().map_err(one)?;
    // (variables declared and never used: each once)
    let used = c.used.borrow();
    let mut warned = HashSet::default();
    let mut warnings = vec![];
    for (pos, name) in &c.declared {
        if !used.contains(&(pos.file, pos.line, pos.col)) && warned.insert((pos.file, pos.line, pos.col)) {
            warnings.push((*pos, format!("unused variable `{name}` (if it's meant to be, call it `_{name}`)")));
        }
    }
    drop(used);
    Ok(core::Program { funcs: c.funcs, main, reads_input: c.reads_input, externs: c.externs, warnings, files: prog.files.clone() })
}

/// A function's body: a `Block`'s, or an expression's.
fn body_of(f: &FnDef) -> &Expr {
    f.body.as_ref().expect("a function with a body")
}

impl<'p> Checker<'p> {
    pub fn fresh_name(&mut self, base: &str) -> Name {
        self.counter += 1;
        format!("{base}_{}", self.counter)
    }

    /// A new lambda's number.
    pub fn lam_id(&mut self) -> usize {
        self.counter += 1;
        self.counter
    }

    /// What a row of effects means for compiling a call with them: none, the
    /// effect parameters', or operations. (A variable nothing decided can be
    /// anything; it's taken to be a parameter's.)
    pub fn eff(&self, e: Eff) -> Eff {
        let Eff::Row(row) = e else { return e };
        match self.u.zonk(&row) {
            Type::RowEmpty => Eff::Pure,
            Type::Var(_) | Type::Skolem(..) => Eff::Poly,
            _ => Eff::Impure,
        }
    }

    /// What calling a function of type `ty` may do.
    fn own_eff(&self, ty: &Type) -> Eff {
        let Type::Fn(_, _, eff) = ty else { unreachable!("a function's type") };
        self.eff(Eff::Row((**eff).clone()))
    }

    /// What trait method `k`'s signature says calling it may do.
    pub fn declared_eff(&self, trait_: &str, k: usize) -> Eff {
        self.eff(Eff::Row(self.traits[trait_].methods[k].eff.clone()))
    }

    /// Closes off the effects of a group of functions (of `types`) that
    /// nothing else in their types mentions: they're just what the bodies
    /// do, so a pure function's are none at all, not any effects a caller
    /// likes. (A call opens a function's effects again, so this allows
    /// nothing less; but it lets a pure function be compiled as one, wherever
    /// it's called from.)
    fn close_effects(&mut self, types: &[Type]) {
        let mut mentioned = vec![];
        let mut tails = vec![];
        for t in types {
            let Type::Fn(params, ret, eff) = self.u.zonk(t) else { unreachable!("a function's type") };
            for p in params.iter().chain([&*ret]) {
                crate::types::vars_in(p, &mut mentioned);
            }
            let mut row = *eff;
            while let Type::RowExtend(_, _, rest) = row {
                row = *rest;
            }
            if let Type::Var(v) = row {
                tails.push(v);
            }
        }
        for v in tails {
            if !mentioned.contains(&v) && matches!(self.u.zonk(&Type::Var(v)), Type::Var(_)) {
                self.u.unify(&Type::Var(v), &Type::RowEmpty).expect("a variable unifies with anything");
            }
        }
    }

    pub fn lookup(&self, path: &ast::Path, ns: Ns) -> Res<Def> {
        self.prog.lookup(self.module, path, ns).map_err(|e| (path.pos, e))
    }

    fn item_name(&self, i: usize) -> String {
        self.prog.items[i].name.clone()
    }

    // ---- 1. declarations

    fn declarations(&mut self) -> Res<()> {
        // names and type parameters first, so they can refer to each other
        let mut vars_of: HashMap<usize, Vec<(String, TV)>> = HashMap::default();
        for (i, item) in self.prog.items.iter().enumerate() {
            let generics = match &item.kind {
                ItemKind::Struct(s) => &s.generics,
                ItemKind::Enum(e) => &e.generics,
                ItemKind::Effect(e) => &e.generics,
                _ => continue,
            };
            let vars = generics.iter().map(|g| (g.clone(), self.u.fresh_var())).collect();
            vars_of.insert(i, vars);
        }
        // the fields set anywhere in the program, by name (a struct of one
        // field can't be just that field if it's set: there's nothing to set)
        let mut set = HashSet::default();
        for item in &self.prog.items {
            let fns: Vec<&FnDef> = match &item.kind {
                ItemKind::Fn(f) => vec![f],
                ItemKind::Trait(t) => t.methods.iter().collect(),
                ItemKind::Impl(m) => m.methods.iter().collect(),
                _ => vec![],
            };
            for f in fns {
                if let Some(body) = &f.body {
                    fields_set(body, &mut set);
                }
            }
        }
        for i in 0..self.prog.items.len() {
            self.module = self.prog.items[i].module;
            let name = self.item_name(i);
            match &self.prog.items[i].kind {
                ItemKind::Struct(s) => {
                    let vars = &vars_of[&i];
                    let ctx = TyCtx::with(vars);
                    let fields: Vec<(String, Type)> = s.fields.iter().map(|(f, t)| Ok((f.clone(), self.ty(t, &ctx)?))).collect::<Res<_>>()?;
                    let unboxed = fields.len() == 1 && !set.contains(&fields[0].0);
                    let settable = fields.iter().map(|(f, _)| set.contains(f)).collect();
                    self.structs.insert(name, StructInfo { vars: vars.iter().map(|v| v.1).collect(), fields, unboxed, set: settable });
                }
                ItemKind::Enum(e) => {
                    let vars = &vars_of[&i];
                    let ctx = TyCtx::with(vars);
                    let variants = e
                        .variants
                        .iter()
                        .map(|(v, ts)| Ok((v.clone(), ts.iter().map(|t| self.ty(t, &ctx)).collect::<Res<_>>()?)))
                        .collect::<Res<_>>()?;
                    self.enums.insert(name, EnumInfo { vars: vars.iter().map(|v| v.1).collect(), variants });
                }
                ItemKind::Effect(e) => {
                    let vars = &vars_of[&i];
                    let mut ops = vec![];
                    for op in &e.ops {
                        let mut ctx = TyCtx::with(vars);
                        let own: Vec<TV> = op.generics.iter().map(|g| {
                            let v = self.u.fresh_var();
                            ctx.types.insert(g.name.clone(), Type::Var(v));
                            v
                        }).collect();
                        let params = op.params.iter().map(|p| self.param_ty(p, &ctx, op.pos)).collect::<Res<_>>()?;
                        let ret = op.ret.as_ref().map(|t| self.ty(t, &ctx)).transpose()?.unwrap_or_else(Type::unit);
                        ops.push(OpSig { name: op.name.clone(), vars: own, params, ret });
                    }
                    self.effects.insert(name, EffectInfo { vars: vars.iter().map(|v| v.1).collect(), ops });
                }
                _ => {}
            }
        }
        // traits, then impl heads (which name traits)
        for i in 0..self.prog.items.len() {
            if let ItemKind::Trait(t) = &self.prog.items[i].kind {
                self.module = self.prog.items[i].module;
                let info = self.trait_decl(i, t)?;
                self.traits.insert(info.name.clone(), info);
            }
        }
        for i in 0..self.prog.items.len() {
            if let ItemKind::Impl(im) = &self.prog.items[i].kind {
                self.module = self.prog.items[i].module;
                let info = self.impl_head(i, im)?;
                self.impls.push(info);
            }
        }
        self.coherence()
    }

    fn trait_decl(&mut self, item: usize, t: &ast::TraitDef) -> Res<TraitInfo> {
        let name = self.item_name(item);
        let self_var = self.u.fresh_var();
        let mut supers = vec![];
        for s in &t.supers {
            match self.lookup(s, Ns::Type)? {
                Def::Item(j) if matches!(self.prog.items[j].kind, ItemKind::Trait(_)) => supers.push(self.item_name(j)),
                _ => return Err((s.pos, format!("{s} isn't a trait"))),
            }
        }
        let mut methods = vec![];
        for m in &t.methods {
            if !m.has_self {
                return Err((m.pos, format!("{} needs `self` as its first parameter", m.name)));
            }
            let mut ctx = TyCtx { self_ty: Some(Type::Var(self_var)), self_trait: Some(name.clone()), ..TyCtx::default() };
            let vars: Vec<TV> = m.generics.iter().filter(|g| !g.effect).map(|g| {
                let v = self.u.fresh_var();
                ctx.types.insert(g.name.clone(), Type::Var(v));
                v
            }).collect();
            self.add_bounds(&mut ctx, &m.generics)?;
            let params = m.params.iter().map(|p| self.param_ty(p, &ctx, m.pos)).collect::<Res<_>>()?;
            let ret = m.ret.as_ref().map(|t| self.ty(t, &ctx)).transpose()?.unwrap_or_else(Type::unit);
            // (a method's effects are what its signature says: none, unless
            // it says `with`)
            let tail = self.u.fresh_var();
            let eff = match &m.effects {
                Some(e) => self.effect_row(e, &ctx, Type::Var(tail))?,
                None => Type::RowEmpty,
            };
            methods.push(MethodSig { name: m.name.clone(), vars, params, ret, eff, tail, has_default: m.body.is_some() });
        }
        let mut assoc_bounds = vec![];
        for (a, bounds) in &t.assoc {
            for b in bounds {
                assoc_bounds.push((a.clone(), self.trait_name(b)?));
            }
        }
        let assoc = t.assoc.iter().map(|(a, _)| a.clone()).collect();
        Ok(TraitInfo { name, item, self_var, assoc, assoc_bounds, supers, methods })
    }

    fn impl_head(&mut self, item: usize, im: &ast::ImplDef) -> Res<ImplInfo> {
        let trait_ = match self.lookup(&im.trait_, Ns::Type)? {
            Def::Item(j) if matches!(self.prog.items[j].kind, ItemKind::Trait(_)) => self.item_name(j),
            _ => return Err((im.trait_.pos, format!("{} isn't a trait", im.trait_))),
        };
        let mut ctx = TyCtx::default();
        let vars: Vec<TV> = im.generics.iter().map(|g| {
            let v = self.u.fresh_var();
            ctx.types.insert(g.name.clone(), Type::Var(v));
            v
        }).collect();
        let head = self.ty(&im.ty, &ctx)?;
        let mut context = vec![];
        for g in &im.generics {
            for b in &g.bounds {
                context.push(Pred { trait_: self.trait_name(b)?, ty: ctx.types[&g.name].clone() });
            }
        }
        // what it says its trait's associated types are: each of them, once
        let mut actx = TyCtx { self_ty: Some(head.clone()), self_trait: Some(trait_.clone()), ..ctx.clone() };
        self.add_bounds(&mut actx, &im.generics)?;
        let wanted = self.traits[&trait_].assoc.clone();
        for (name, t, at) in &im.assoc {
            if !wanted.contains(name) {
                return Err((*at, format!("{trait_} has no associated type {name}")));
            }
            if im.assoc.iter().filter(|(n, _, _)| n == name).count() > 1 {
                return Err((*at, format!("{name} is said twice")));
            }
            let ty = self.ty(t, &actx)?;
            self.u.assoc.push(crate::types::AssocImpl { trait_: trait_.clone(), name: name.clone(), vars: vars.clone(), head: head.clone(), ty });
        }
        if let Some(missing) = wanted.iter().find(|w| !im.assoc.iter().any(|(n, _, _)| n == *w)) {
            return Err((im.pos, format!("this impl doesn't say what {missing} is (`type {missing} = ...;`)")));
        }
        let n = self.impls.len();
        // (which methods it defines is known now: code using the impl calls
        // them directly, before they're checked)
        let mut methods = HashMap::default();
        for m in &im.methods {
            let Some(idx) = self.traits[&trait_].methods.iter().position(|s| s.name == m.name) else {
                return Err((m.pos, format!("{trait_} has no method {}", m.name)));
            };
            methods.insert(idx, format!("{}::{}", self.prog.items[item].name, m.name));
        }
        Ok(ImplInfo { item, trait_, vars, head, context, dict_fn: format!("dict{n}"), methods })
    }

    /// Where the first function of a group is.
    fn group_pos(&self, items: &[usize]) -> Pos {
        match &self.prog.items[items[0]].kind {
            ItemKind::Fn(f) => f.pos,
            _ => Pos::default(),
        }
    }

    /// Fails if an associated type has been left undecided (`T::Item`, for
    /// a `T` nothing says), at `pos`.
    fn settled(&mut self, pos: Pos) -> Res<()> {
        match self.u.unsettled().into_iter().next() {
            Some((a, b)) => Err((pos, format!("can't tell what {} is, to see if it's {}: say what type it's of", self.u.show(&a), self.u.show(&b)))),
            None => Ok(()),
        }
    }

    /// Adds to `ctx` the traits each of `generics` has to have (for its
    /// associated types).
    fn add_bounds(&self, ctx: &mut TyCtx, generics: &[ast::Generic]) -> Res<()> {
        for g in generics {
            for b in &g.bounds {
                let t = self.trait_name(b)?;
                ctx.bounds.entry(g.name.clone()).or_default().push(t);
            }
        }
        Ok(())
    }

    /// Trait `trait_`'s associated types (it may be the one being declared).
    fn assoc_names(&self, trait_: &str) -> Vec<String> {
        if let Some(t) = self.traits.get(trait_) {
            return t.assoc.clone();
        }
        (0..self.prog.items.len())
            .find_map(|i| match &self.prog.items[i].kind {
                ItemKind::Trait(t) if self.item_name(i) == trait_ => Some(t.assoc.iter().map(|(a, _)| a.clone()).collect()),
                _ => None,
            })
            .unwrap_or_default()
    }

    pub fn trait_name(&self, path: &ast::Path) -> Res<String> {
        match self.lookup(path, Ns::Type)? {
            Def::Item(j) if matches!(self.prog.items[j].kind, ItemKind::Trait(_)) => Ok(self.item_name(j)),
            _ => Err((path.pos, format!("{path} isn't a trait"))),
        }
    }

    /// No two impls of a trait for types that could be the same, and each
    /// impl in the module of its trait or its type (so which impl a type
    /// uses never depends on what's imported).
    fn coherence(&mut self) -> Res<()> {
        for i in 0..self.impls.len() {
            let pos = self.impl_pos(i);
            let module_path = self.prog.modules[self.prog.items[self.impls[i].item].module].path.join("::");
            let home = |name: &str| name.rsplit_once("::").map_or("", |(m, _)| m).to_string();
            let trait_home = home(&self.impls[i].trait_);
            let type_home = match &self.impls[i].head {
                Type::Con(n, _) if !n.contains("::") && ["Int", "Bool", "String"].contains(&n.as_str()) => "std".to_string(),
                Type::Con(n, _) => home(n),
                _ => "std".to_string(),
            };
            if trait_home != module_path && type_home != module_path {
                return Err((pos, format!("an impl has to be in the module of its trait or of its type ({trait_home} or {type_home})")));
            }
            for j in 0..i {
                if self.impls[j].trait_ == self.impls[i].trait_ && self.overlap(i, j) {
                    return Err((pos, format!("two impls of {} for the same type", self.impls[i].trait_)));
                }
            }
        }
        Ok(())
    }

    /// Whether impls `i` and `j` could be for the same type: a trial
    /// unification of their heads, on a copy of the unifier.
    fn overlap(&mut self, i: usize, j: usize) -> bool {
        let a = self.instantiate_impl(i).0;
        let b = self.instantiate_impl(j).0;
        self.u.clone().unify(&a, &b).is_ok()
    }

    pub fn impl_pos(&self, i: usize) -> Pos {
        match &self.prog.items[self.impls[i].item].kind {
            ItemKind::Impl(im) => im.pos,
            _ => Pos::default(),
        }
    }

    /// An impl's head and requirements, with new variables for its type
    /// parameters.
    pub fn instantiate_impl(&mut self, i: usize) -> (Type, Vec<Pred>) {
        let s = Scheme { vars: self.impls[i].vars.clone(), preds: self.impls[i].context.clone(), ty: self.impls[i].head.clone() };
        self.u.instantiate(&s)
    }

    // ---- types written in the source

    pub fn param_ty(&mut self, p: &ast::Param, ctx: &TyCtx, _pos: Pos) -> Res<Type> {
        match &p.ty {
            Some(t) => self.ty(t, ctx),
            None => Ok(self.u.fresh()),
        }
    }

    /// The type a type expression means, with `ctx`'s type parameters.
    pub fn ty(&mut self, t: &TypeExpr, ctx: &TyCtx) -> Res<Type> {
        Ok(match t {
            TypeExpr::Infer => self.u.fresh(),
            TypeExpr::SelfType => ctx.self_ty.clone().ok_or((Pos::default(), "Self outside a trait or impl".to_string()))?,
            TypeExpr::SelfAssoc(name) => {
                let (Some(of), Some(trait_)) = (&ctx.self_ty, &ctx.self_trait) else {
                    return Err((Pos::default(), format!("Self::{name} outside a trait or a trait's impl")));
                };
                if !self.assoc_names(trait_).contains(name) {
                    return Err((Pos::default(), format!("{trait_} has no associated type {name}")));
                }
                Type::Assoc(Box::new(of.clone()), trait_.clone(), name.clone())
            }
            TypeExpr::Tuple(ts) => Type::Tuple(ts.iter().map(|t| self.ty(t, ctx)).collect::<Res<_>>()?),
            TypeExpr::Fn(ps, r, e) => {
                let params = ps.iter().map(|p| self.ty(p, ctx)).collect::<Res<_>>()?;
                let ret = self.ty(r, ctx)?;
                let eff = match e {
                    // (a function type's written effects are all it may do;
                    // calls open the row, see `open`)
                    Some(e) => self.effect_row(e, ctx, Type::RowEmpty)?,
                    None => self.u.fresh(),
                };
                Type::func(params, ret, eff)
            }
            TypeExpr::Record(fields, rest) => {
                let mut row = match rest {
                    Some(r) => ctx.rows.get(r).cloned().unwrap_or_else(|| self.u.fresh()),
                    None => Type::RowEmpty,
                };
                for (f, t) in fields.iter().rev() {
                    row = Type::extend(f, self.ty(t, ctx)?, row);
                }
                Type::Record(Box::new(row))
            }
            TypeExpr::Named(path, args) => {
                if path.segments.len() == 1 && args.is_empty() {
                    if let Some(t) = ctx.types.get(&path.segments[0]) {
                        return Ok(t.clone());
                    }
                }
                // (`T::Item`: an associated type of one of type parameter T's
                // traits)
                if path.segments.len() == 2 && args.is_empty() {
                    if let Some(of) = ctx.types.get(&path.segments[0]) {
                        let name = &path.segments[1];
                        let traits: Vec<String> = ctx.bounds.get(&path.segments[0]).into_iter().flatten().filter(|t| self.assoc_names(t).contains(name)).cloned().collect();
                        return match traits.as_slice() {
                            [trait_] => Ok(Type::Assoc(Box::new(of.clone()), trait_.clone(), name.clone())),
                            [] => Err((path.pos, format!("none of {}'s traits has an associated type {name}", path.segments[0]))),
                            _ => Err((path.pos, format!("more than one of {}'s traits has an associated type {name}", path.segments[0]))),
                        };
                    }
                }
                let args: Vec<Type> = args.iter().map(|a| self.ty(a, ctx)).collect::<Res<_>>()?;
                match self.lookup(path, Ns::Type)? {
                    Def::Builtin("Array") => {
                        if args.len() != 1 {
                            return Err((path.pos, "Array takes 1 type argument".into()));
                        }
                        Type::Con("Array".into(), args)
                    }
                    Def::Builtin(n) if n != "Io" => {
                        if !args.is_empty() {
                            return Err((path.pos, format!("{n} takes no type arguments")));
                        }
                        Type::con(n)
                    }
                    Def::Item(i) => {
                        let name = self.item_name(i);
                        let want = match &self.prog.items[i].kind {
                            ItemKind::Struct(s) => s.generics.len(),
                            ItemKind::Enum(e) => e.generics.len(),
                            _ => return Err((path.pos, format!("{path} isn't a type"))),
                        };
                        if args.len() != want {
                            return Err((path.pos, format!("{path} takes {want} type arguments")));
                        }
                        Type::Con(name, args)
                    }
                    _ => return Err((path.pos, format!("{path} isn't a type"))),
                }
            }
        })
    }

    /// A row of effects: `with A, B<T>, 'e`, ending in `tail` unless it
    /// names one.
    pub fn effect_row(&mut self, e: &ast::EffectExpr, ctx: &TyCtx, tail: Type) -> Res<Type> {
        let mut row = match &e.tail {
            Some(name) => ctx.effects.get(name).cloned().ok_or((Pos::default(), format!("no effect variable '{name}")))?,
            None => tail,
        };
        for (path, args) in e.effects.iter().rev() {
            let args: Vec<Type> = args.iter().map(|a| self.ty(a, ctx)).collect::<Res<_>>()?;
            let name = match self.lookup(path, Ns::Type)? {
                Def::Builtin("Io") => "Io".to_string(),
                Def::Item(i) if matches!(self.prog.items[i].kind, ItemKind::Effect(_)) => self.item_name(i),
                _ => return Err((path.pos, format!("{path} isn't an effect"))),
            };
            row = Type::extend(&name, Type::Con(name.clone(), args), row);
        }
        Ok(row)
    }

    /// Each `extern fn`'s type, as written: every parameter's is, and the
    /// result's is `()` if it isn't. Calling one has the `Io` effect (C can
    /// do anything), unless it says `with {}`: it's pure, which fern takes
    /// its word for. (C can't perform fern's own effects: an operation goes
    /// to a handler, which only fern code has.)
    fn extern_fns(&mut self) -> Res<()> {
        for i in 0..self.prog.items.len() {
            let ItemKind::Extern(f) = &self.prog.items[i].kind else { continue };
            self.module = self.prog.items[i].module;
            let ctx = TyCtx::default();
            let params = f.params.iter().map(|p| self.ty(p.ty.as_ref().unwrap(), &ctx)).collect::<Res<Vec<_>>>()?;
            let ret = match &f.ret {
                Some(t) => self.ty(t, &ctx)?,
                None => Type::unit(),
            };
            let io = match &f.effects {
                None => true,
                Some(e) => {
                    if e.tail.is_some() {
                        return Err((f.pos, format!("extern fn {}'s effects are Io, or none (with {{}})", f.name)));
                    }
                    for (path, _) in &e.effects {
                        if !matches!(self.lookup(path, Ns::Type), Ok(Def::Builtin("Io"))) {
                            return Err((path.pos, format!("C can't perform {path}: an extern fn's effects are Io, or none (with {{}})")));
                        }
                    }
                    !e.effects.is_empty()
                }
            };
            // (a C function, so a C name; and the VM's labels hold 15 characters)
            if f.name.len() > 15 || f.name.starts_with("rt_") {
                return Err((f.pos, format!("an extern fn's name has at most 15 characters, and doesn't start with rt_: {}", f.name)));
            }
            let number = match self.externs.iter().position(|(n, _)| *n == f.name) {
                Some(k) if self.externs[k].1 != params.len() => {
                    return Err((f.pos, format!("extern fn {} is declared elsewhere with {} parameters", f.name, self.externs[k].1)));
                }
                Some(k) => k,
                None => {
                    self.externs.push((f.name.clone(), params.len()));
                    self.externs.len() - 1
                }
            };
            self.extern_sigs.insert(i, (params, ret, number, io));
        }
        Ok(())
    }

    /// Arithmetic on a type nothing decides (a `Num`, `Add`, `Mul`, ...
    /// requirement on a variable none of `types` has, as in
    /// `let f = |a, b| a + b;` never used) is Int's, as Haskell defaults it.
    fn default_numbers(&mut self, types: &[Type]) -> Res<()> {
        let mut seen = vec![];
        for t in types {
            crate::types::vars_in(&self.u.zonk(t), &mut seen);
        }
        let numeric = |t: &str| t == "std::Num" || crate::expr::ARITH.iter().any(|(_, a, _)| *a == t);
        let nums: Vec<(Type, Pos)> = self.wanted.iter().filter(|w| numeric(&w.pred.trait_)).map(|w| (w.pred.ty.clone(), w.pos)).collect();
        for (t, pos) in nums {
            if let Type::Var(v) = self.u.zonk(&t) {
                if !seen.contains(&v) {
                    self.unify(&t, &Type::int(), pos)?;
                }
            }
        }
        Ok(())
    }

    // ---- methods

    /// Each method's type, from its signature, which is written out in
    /// full (as a trait's methods' are): parameters' types, the result's (or
    /// `()`), and its effects (or none). So calls to methods, which type's
    /// method a call is being something worked out as functions are
    /// checked, never wait for a method's body.
    fn method_signatures(&mut self) -> Res<()> {
        for i in self.method_ids() {
            let ItemKind::Fn(f) = &self.prog.items[i].kind else { unreachable!() };
            self.module = self.prog.items[i].module;
            self.u.current += 1;
            let sig = self.method_signature(i, f)?;
            self.u.current -= 1;
            let scheme = self.u.generalize(&sig.ty, sig.bounds.clone(), &sig.rigid);
            self.schemes.insert(i, scheme);
        }
        Ok(())
    }

    fn method_ids(&self) -> Vec<usize> {
        let mut ids: Vec<usize> = self.prog.self_types.keys().copied().collect();
        ids.sort();
        ids
    }

    fn method_signature(&mut self, i: usize, f: &FnDef) -> Res<Signature> {
        if let Some(p) = f.params.iter().find(|p| p.ty.is_none()) {
            return Err((f.pos, format!("{}'s parameter {} needs a type (a method's signature is written out in full)", f.name, p.name)));
        }
        let sig = self.signature(f, self.prog.self_types.get(&i))?;
        let Type::Fn(_, ret, eff) = &sig.ty else { unreachable!() };
        if f.ret.is_none() {
            self.unify(ret, &Type::unit(), f.pos)?;
        }
        if f.effects.is_none() {
            self.unify(eff, &Type::RowEmpty, f.pos)?;
        }
        Ok(sig)
    }

    /// Each method's body, against its signature, on its own (it may only
    /// need what its type parameters' bounds say).
    fn method_bodies(&mut self) -> Res<()> {
        for i in self.method_ids() {
            // (an error in one doesn't stop the others' being checked)
            let level = self.u.current;
            if let Err(e) = self.inherent_method(i) {
                self.errors.push(e);
                self.u.current = level;
            }
        }
        Ok(())
    }

    /// Checks a method's body (one in an `impl Type` block, not a trait's).
    fn inherent_method(&mut self, i: usize) -> Res<()> {
        let ItemKind::Fn(f) = &self.prog.items[i].kind else { unreachable!() };
        self.module = self.prog.items[i].module;
        self.u.current += 1;
        self.wanted.clear();
        self.uses.clear();
        let sig = self.method_signature(i, f)?;
        let (vparams, body) = self.fn_body(f, &sig)?;
        self.resolve_uses()?;
        self.settled(f.pos)?;
        self.default_numbers(&[sig.ty.clone()])?;
        self.u.current -= 1;
        let mut given: Vec<(Pred, Name)> = sig.bounds.iter().map(|p| (p.clone(), self.fresh_name("dict"))).collect();
        self.solve(&mut given, false)?;
        let dicts: Vec<Name> = given.iter().map(|(_, n)| n.clone()).collect();
        let body = self.finalize(body, &dicts);
        let mut ps = dicts;
        ps.extend(vparams);
        let eff = self.own_eff(&sig.ty);
        self.funcs.push(core::Func { name: self.item_name(i), params: ps, body, eff });
        Ok(())
    }

    // ---- 2. functions, a recursive group at a time

    fn functions(&mut self) -> Res<()> {
        // (methods aren't in these: their types are known from their signatures)
        let fns: Vec<usize> = (0..self.prog.items.len()).filter(|&i| matches!(self.prog.items[i].kind, ItemKind::Fn(_)) && !self.prog.self_types.contains_key(&i)).collect();
        let index: HashMap<usize, usize> = fns.iter().enumerate().map(|(k, &i)| (i, k)).collect();
        let mut edges = vec![vec![]; fns.len()];
        for (k, &i) in fns.iter().enumerate() {
            let ItemKind::Fn(f) = &self.prog.items[i].kind else { unreachable!() };
            let mut refs = HashSet::default();
            calls_in(body_of(f), &mut refs);
            for path in refs {
                if let Ok(Def::Item(j)) = self.prog.lookup(self.prog.items[i].module, &path, Ns::Value) {
                    if let Some(&kj) = index.get(&j) {
                        edges[k].push(kj);
                    }
                }
            }
        }
        for group in tarjan(&edges) {
            let items: Vec<usize> = group.iter().map(|&k| fns[k]).collect();
            let level = self.u.current;
            if let Err(e) = self.fn_group(&items) {
                // (on to the rest, with the group's functions taken to have
                // the types their signatures give them, anything where they
                // don't say: so what calls them doesn't fail because they did)
                self.errors.push(e);
                self.u.current = level;
                for &i in &items {
                    self.group.remove(&i);
                    if !self.schemes.contains_key(&i) {
                        let ItemKind::Fn(f) = &self.prog.items[i].kind else { unreachable!() };
                        self.module = self.prog.items[i].module;
                        self.u.current += 1;
                        let sig = self.signature(f, None);
                        self.u.current = level;
                        if let Ok(sig) = sig {
                            let scheme = self.u.generalize(&sig.ty, vec![], &sig.rigid);
                            self.schemes.insert(i, scheme);
                        }
                    }
                }
            }
        }
        Ok(())
    }

    /// Checks a recursive group of functions, and generalizes them together.
    fn fn_group(&mut self, items: &[usize]) -> Res<()> {
        let start = std::time::Instant::now();
        let r = self.fn_group_inner(items);
        if bf::asm::log::enabled(bf::asm::log::TRACE) {
            let names: Vec<&str> = items.iter().map(|&i| self.prog.items[i].name.as_str()).collect();
            bf::log!(bf::asm::log::TRACE, "{}: {}", names.join(", "), bf::asm::log::show(start.elapsed()));
        }
        r
    }

    fn fn_group_inner(&mut self, items: &[usize]) -> Res<()> {
        self.u.current += 1;
        self.wanted.clear();
        self.uses.clear();
        let mut sigs = vec![];
        for &i in items {
            let ItemKind::Fn(f) = &self.prog.items[i].kind else { unreachable!() };
            self.module = self.prog.items[i].module;
            let sig = self.signature(f, self.prog.self_types.get(&i))?;
            self.group.insert(i, sig.ty.clone());
            sigs.push(sig);
        }
        let mut bodies = vec![];
        for (&i, sig) in items.iter().zip(&sigs) {
            let ItemKind::Fn(f) = &self.prog.items[i].kind else { unreachable!() };
            self.module = self.prog.items[i].module;
            let (params, body) = self.fn_body(f, sig)?;
            bodies.push((params, body));
        }
        self.resolve_uses()?;
        self.settled(self.group_pos(items))?;
        let types: Vec<Type> = sigs.iter().map(|s| s.ty.clone()).collect();
        self.default_numbers(&types)?;
        self.close_effects(&types);
        self.u.current -= 1;
        // the group's requirements: those its signatures declare, then the
        // rest it needs of its type variables (all of them share these)
        let mut given: Vec<(Pred, Name)> = vec![];
        let mut rigid = vec![];
        for sig in &sigs {
            for p in &sig.bounds {
                given.push((p.clone(), self.fresh_name("dict")));
            }
            rigid.extend(sig.rigid.iter().copied());
        }
        let params = self.solve(&mut given, true)?;
        // a requirement on a type the functions' types don't have can never
        // be decided by a caller (like `Show` of the elements of `Nil` in
        // `Nil.show()`): the code has to say what that type is
        let mut seen = vec![];
        for sig in &sigs {
            crate::types::vars_in(&self.u.zonk(&sig.ty), &mut seen);
        }
        for (p, _) in &params {
            let mut vars = vec![];
            crate::types::vars_in(&self.u.zonk(&p.ty), &mut vars);
            if vars.iter().any(|v| !seen.contains(v)) {
                let ItemKind::Fn(f) = &self.prog.items[items[0]].kind else { unreachable!() };
                let what = self.u.show(&p.ty);
                let trait_ = p.trait_.rsplit("::").next().unwrap_or(&p.trait_);
                return Err((f.pos, format!("{} needs {trait_}<{what}>, but nothing says what type {what} is: annotate it", f.name)));
            }
        }
        let preds: Vec<Pred> = params.iter().map(|(p, _)| p.clone()).collect();
        let dict_names: Vec<Name> = params.iter().map(|(_, n)| n.clone()).collect();
        for ((&i, sig), (vparams, body)) in items.iter().zip(&sigs).zip(bodies) {
            let scheme = self.u.generalize(&sig.ty, preds.clone(), &rigid);
            self.schemes.insert(i, scheme);
            self.group.remove(&i);
            let body = self.finalize(body, &dict_names);
            let mut ps = dict_names.clone();
            ps.extend(vparams);
            let eff = self.own_eff(&sig.ty);
            self.funcs.push(core::Func { name: self.item_name(i), params: ps, body, eff });
        }
        Ok(())
    }

    /// A function's type as its signature says: written types where they're
    /// written (type parameters as skolems), new variables where they aren't.
    fn signature(&mut self, f: &FnDef, self_ty: Option<&TypeExpr>) -> Res<Signature> {
        let mut ctx = TyCtx::default();
        let mut rigid = vec![];
        for g in &f.generics {
            let t = self.u.skolem(&g.name);
            if let Type::Skolem(v, _) = &t {
                rigid.push(*v);
            }
            if g.effect {
                ctx.effects.insert(g.name.clone(), t);
            } else {
                ctx.types.insert(g.name.clone(), t);
            }
        }
        let mut bounds = vec![];
        for g in &f.generics {
            for b in &g.bounds {
                bounds.push(Pred { trait_: self.trait_name(b)?, ty: ctx.types[&g.name].clone() });
            }
        }
        self.add_bounds(&mut ctx, &f.generics)?;
        // (a method's `Self`, and its `self`'s type: its impl's type)
        if let Some(t) = self_ty {
            ctx.self_ty = Some(self.ty(t, &ctx)?);
        }
        let params: Vec<Type> = f.params.iter().map(|p| self.param_ty(p, &ctx, f.pos)).collect::<Res<_>>()?;
        let ret = match &f.ret {
            Some(t) => self.ty(t, &ctx)?,
            None => self.u.fresh(),
        };
        // written effects are all it may have (the row ends in a skolem,
        // which nothing can be added to); unwritten, they're worked out
        let eff = match &f.effects {
            Some(e) => {
                let tail = self.u.skolem("e");
                if let Type::Skolem(v, _) = &tail {
                    rigid.push(*v);
                }
                self.effect_row(e, &ctx, tail)?
            }
            None => self.u.fresh(),
        };
        Ok(Signature { ty: Type::func(params, ret, eff), bounds, rigid, ctx })
    }

    /// Checks a function's body against its type: its parameters' names and
    /// its core body.
    fn fn_body(&mut self, f: &FnDef, sig: &Signature) -> Res<(Vec<Name>, Core)> {
        let Type::Fn(params, ret, eff) = &sig.ty else { unreachable!() };
        self.scopes = vec![HashMap::default()];
        let mut names = vec![];
        let mut wrap: Vec<(Name, Name)> = vec![];
        for (p, t) in f.params.iter().zip(params) {
            let name = self.fresh_name(&p.name);
            if p.mutable {
                // (a `mut` parameter: a cell made from the argument)
                let cell = self.fresh_name(&p.name);
                wrap.push((cell.clone(), name.clone()));
                self.scopes[0].insert(p.name.clone(), Local { name: cell, ty: t.clone(), mutable: true, at: None });
            } else {
                self.scopes[0].insert(p.name.clone(), Local { name: name.clone(), ty: t.clone(), mutable: false, at: None });
            }
            names.push(name);
        }
        self.effect = (**eff).clone();
        self.ret = Some((**ret).clone());
        self.loops = 0;
        self.body_ctx = sig.ctx.clone();
        let body = body_of(f);
        let (mut core, t) = self.infer(body)?;
        self.unify(&t, ret, body.pos)?;
        for (cell, arg) in wrap.into_iter().rev() {
            core = Core::Let(cell, Box::new(Core::NewRef(Box::new(Core::Local(arg)))), Box::new(core));
        }
        Ok((names, core))
    }

    pub fn unify(&mut self, a: &Type, b: &Type, pos: Pos) -> Res<()> {
        self.u.unify(a, b).map_err(|e| (pos, e))
    }

    // ---- 3. impls' methods, and traits' default methods

    fn impl_methods(&mut self) -> Res<()> {
        for k in 0..self.impls.len() {
            let level = self.u.current;
            if let Err(e) = self.check_impl(k) {
                self.errors.push(e);
                self.u.current = level;
            }
        }
        let mut traits: Vec<String> = self.traits.keys().cloned().collect();
        traits.sort();
        for t in traits {
            self.default_methods(&t)?;
        }
        Ok(())
    }

    /// Checks an impl's methods, and makes its dictionary function.
    fn check_impl(&mut self, k: usize) -> Res<()> {
        let item = self.impls[k].item;
        let ItemKind::Impl(im) = &self.prog.items[item].kind else { unreachable!() };
        self.module = self.prog.items[item].module;
        let trait_name = self.impls[k].trait_.clone();
        // the impl's type parameters as skolems, while checking it
        let skolems: HashMap<TV, Type> = im.generics.iter().zip(self.impls[k].vars.clone()).map(|(g, v)| (v, self.u.skolem(&g.name))).collect();
        let mut names = TyCtx::default();
        for (g, v) in im.generics.iter().zip(&self.impls[k].vars) {
            names.types.insert(g.name.clone(), skolems[v].clone());
        }
        self.add_bounds(&mut names, &im.generics)?;
        let head = crate::types::substitute(&self.impls[k].head, &skolems);
        let context: Vec<Pred> = self.impls[k].context.iter().map(|p| Pred { trait_: p.trait_.clone(), ty: crate::types::substitute(&p.ty, &skolems) }).collect();
        let ctx_names: Vec<Name> = context.iter().map(|_| self.fresh_name("ctx")).collect();
        let n_methods = self.traits[&trait_name].methods.len();
        for m in &im.methods {
            let idx = self.traits[&trait_name].methods.iter().position(|s| s.name == m.name).unwrap();
            let fname = self.impls[k].methods[&idx].clone();
            self.method_body(&trait_name, idx, m, &head, &names, &context, &ctx_names, &fname)?;
        }
        for idx in 0..n_methods {
            if !self.impls[k].methods.contains_key(&idx) && !self.traits[&trait_name].methods[idx].has_default {
                let name = self.traits[&trait_name].methods[idx].name.clone();
                return Err((im.pos, format!("the impl of {trait_name} needs {name}")));
            }
        }
        self.dict_fn(k, &head, &context, &ctx_names)
    }

    /// Checks one method of an impl (or, with `Self` a skolem, a trait's
    /// default method), and adds its function: parameters `ctx_names` (the
    /// dictionaries it's given), then its own.
    #[allow(clippy::too_many_arguments)]
    fn method_body(&mut self, trait_name: &str, idx: usize, m: &FnDef, self_ty: &Type, names: &TyCtx, context: &[Pred], ctx_names: &[Name], fname: &str) -> Res<()> {
        self.u.current += 1;
        self.wanted.clear();
        self.uses.clear();
        let sig = &self.traits[trait_name].methods[idx];
        let mut map: HashMap<TV, Type> = HashMap::default();
        map.insert(self.traits[trait_name].self_var, self_ty.clone());
        let own: Vec<TV> = sig.vars.clone();
        let tail = sig.tail;
        let (params, ret, eff) = (sig.params.clone(), sig.ret.clone(), sig.eff.clone());
        for (k, v) in own.iter().enumerate() {
            let name = m.generics.get(k).map_or("T".to_string(), |g| g.name.clone());
            map.insert(*v, self.u.skolem(&name));
        }
        // (no effects but the signature's: its row ends in a skolem)
        map.insert(tail, self.u.skolem("e"));
        let ctx = TyCtx { self_ty: Some(self_ty.clone()), self_trait: Some(trait_name.to_string()), ..names.clone() };
        let params: Vec<Type> = params.iter().map(|p| crate::types::substitute(p, &map)).collect();
        if m.params.len() != params.len() {
            return Err((m.pos, format!("{} takes {} parameters", m.name, params.len())));
        }
        for (p, t) in m.params.iter().zip(&params) {
            if let Some(written) = &p.ty {
                let w = self.ty(written, &ctx)?;
                self.unify(&w, t, m.pos)?;
            }
        }
        let ty = Type::func(params, crate::types::substitute(&ret, &map), crate::types::substitute(&eff, &map));
        let sig = Signature { ty, bounds: vec![], rigid: vec![], ctx };
        let (vparams, body) = self.fn_body(m, &sig)?;
        self.resolve_uses()?;
        self.settled(m.pos)?;
        self.default_numbers(&[sig.ty.clone()])?;
        self.u.current -= 1;
        let mut given: Vec<(Pred, Name)> = context.iter().cloned().zip(ctx_names.iter().cloned()).collect();
        self.solve(&mut given, false)?;
        let body = self.finalize(body, &[]);
        let mut ps = ctx_names.to_vec();
        ps.extend(vparams);
        let eff = self.own_eff(&sig.ty);
        self.funcs.push(core::Func { name: fname.to_string(), params: ps, body, eff });
        Ok(())
    }

    /// The function making impl `k`'s dictionary: its methods (as closures),
    /// then its supertraits' dictionaries.
    fn dict_fn(&mut self, k: usize, head: &Type, context: &[Pred], ctx_names: &[Name]) -> Res<()> {
        let trait_name = self.impls[k].trait_.clone();
        let pos = self.impl_pos(k);
        let mut fields = vec![];
        let n = self.traits[&trait_name].methods.len();
        for idx in 0..n {
            let arity = self.traits[&trait_name].methods[idx].params.len();
            // (what the method may do: what its signature says)
            let eff = self.declared_eff(&trait_name, idx);
            let params: Vec<Name> = (0..arity).map(|_| self.fresh_name("a")).collect();
            let mut args: Vec<Core> = ctx_names.iter().map(|c| Core::Local(c.clone())).collect();
            let call = match self.impls[k].methods.get(&idx) {
                Some(f) => {
                    args.extend(params.iter().map(|p| Core::Local(p.clone())));
                    Core::CallGlobal(f.clone(), args, eff.clone())
                }
                None => {
                    // a default method: given this very dictionary (made again
                    // when it's called, rather than referring to itself)
                    let dict = Core::CallGlobal(self.impls[k].dict_fn.clone(), args, Eff::Pure);
                    let mut all = vec![dict];
                    all.extend(params.iter().map(|p| Core::Local(p.clone())));
                    Core::CallGlobal(default_name(&trait_name, idx), all, eff.clone())
                }
            };
            let id = self.lam_id();
            fields.push(Core::Lam(id, params, Box::new(call), eff));
        }
        let supers = self.traits[&trait_name].supers.clone();
        let mut given: Vec<(Pred, Name)> = context.iter().cloned().zip(ctx_names.iter().cloned()).collect();
        for s in supers {
            self.wanted.clear();
            let hole = self.new_hole(Pred { trait_: s, ty: head.clone() }, pos);
            self.solve(&mut given, false)?;
            fields.push(self.finalize(Core::DictHole(hole), &[]));
        }
        // (and those its associated types have to have: of what it says they are)
        let bounds = self.traits[&trait_name].assoc_bounds.clone();
        for (a, b) in bounds {
            self.wanted.clear();
            let of = Type::Assoc(Box::new(head.clone()), trait_name.clone(), a.clone());
            let hole = self.new_hole(Pred { trait_: b, ty: of }, pos);
            self.solve(&mut given, false).map_err(|(p, m)| (p, format!("this impl's {a}: {m}")))?;
            fields.push(self.finalize(Core::DictHole(hole), &[]));
        }
        let name = self.impls[k].dict_fn.clone();
        self.funcs.push(core::Func { name, params: ctx_names.to_vec(), body: Core::Tuple(fields), eff: Eff::Pure });
        Ok(())
    }

    /// A trait's default methods, as functions taking the dictionary of the
    /// type they're for.
    fn default_methods(&mut self, trait_name: &str) -> Res<()> {
        let item = self.traits[trait_name].item;
        let ItemKind::Trait(t) = &self.prog.items[item].kind else { unreachable!() };
        self.module = self.prog.items[item].module;
        for (idx, m) in t.methods.iter().enumerate() {
            if m.body.is_none() {
                continue;
            }
            let self_ty = self.u.skolem("Self");
            let dict = self.fresh_name("self_dict");
            let pred = Pred { trait_: trait_name.to_string(), ty: self_ty.clone() };
            self.method_body(trait_name, idx, m, &self_ty, &TyCtx::default(), &[pred], &[dict], &default_name(trait_name, idx))?;
        }
        Ok(())
    }

    // ---- 4. main

    fn main(&mut self) -> Res<String> {
        let root = self.prog.modules.iter().position(|m| m.path.is_empty() && m.parent.is_none()).unwrap();
        let Some(i) = (0..self.prog.items.len()).find(|&i| self.prog.items[i].module == root && matches!(&self.prog.items[i].kind, ItemKind::Fn(f) if f.name == "main"))
        else {
            return Err((Pos::default(), "there's no main function".into()));
        };
        let ItemKind::Fn(f) = &self.prog.items[i].kind else { unreachable!() };
        let scheme = self.schemes[&i].clone();
        if !f.params.is_empty() {
            return Err((f.pos, "main takes no parameters".into()));
        }
        // (a requirement left on a type nothing decided, like `Show` for
        // the elements of `Nil` in `Nil.show()`)
        if let Some(p) = scheme.preds.first() {
            let what = self.u.show(&p.ty);
            return Err((f.pos, format!("main needs {}<{what}>, but nothing says what type {what} is: annotate it", p.trait_.rsplit("::").next().unwrap_or(&p.trait_))));
        }
        let Type::Fn(_, _, eff) = &scheme.ty else { unreachable!() };
        // whatever effects it has left must be Io's
        let mut row = self.u.zonk(eff);
        loop {
            match row {
                Type::RowExtend(l, _, rest) => {
                    if l != "Io" {
                        return Err((f.pos, format!("main doesn't handle the effect {l}")));
                    }
                    row = *rest;
                }
                _ => break,
            }
        }
        Ok(self.item_name(i))
    }
}

/// The function of trait `t`'s default method `idx`.
pub fn default_name(t: &str, idx: usize) -> String {
    format!("{t}::default{idx}")
}

/// What a function's signature says.
pub struct Signature {
    pub ty: Type,
    /// The names its type parameters (and `Self`) have, for its body.
    pub ctx: TyCtx,
    /// The requirements its type parameters' bounds make.
    pub bounds: Vec<Pred>,
    /// Its type parameters' skolems (generalized once it's checked).
    pub rigid: Vec<TV>,
}

/// The type parameters in scope for a type expression.
#[derive(Default, Clone)]
pub struct TyCtx {
    pub types: HashMap<String, Type>,
    pub effects: HashMap<String, Type>,
    pub rows: HashMap<String, Type>,
    pub self_ty: Option<Type>,
    /// The trait being defined or implemented (whose associated types
    /// `Self::Item` names), by full name.
    pub self_trait: Option<String>,
    /// Each type parameter's traits (whose associated types `T::Item`
    /// names), by full name.
    pub bounds: HashMap<String, Vec<String>>,
}

impl TyCtx {
    fn with(vars: &[(String, TV)]) -> TyCtx {
        TyCtx { types: vars.iter().map(|(n, v)| (n.clone(), Type::Var(*v))).collect(), ..TyCtx::default() }
    }
}

/// The paths an expression refers to as values (an over-estimate of what it
/// calls: local variables of the same name are included).
fn calls_in(e: &Expr, out: &mut HashSet<PathKey>) {
    if let ExprKind::Path(p) = &e.kind {
        out.insert(PathKey(p.clone()));
    }
    for c in subexpressions(e) {
        calls_in(c, out);
    }
}

/// The names of the fields an expression sets (`r.f = ..`), whoever's they are.
fn fields_set(e: &Expr, out: &mut HashSet<String>) {
    if let ExprKind::SetField(_, f, _) = &e.kind {
        out.insert(f.clone());
    }
    for c in subexpressions(e) {
        fields_set(c, out);
    }
}

/// The expressions directly inside an expression.
fn subexpressions(e: &Expr) -> Vec<&Expr> {
    use ExprKind::*;
    match &e.kind {
        Int(_) | Str(_) | Bool(_) | Unit | Path(_) | Break | Continue | Return(None) => vec![],
        Call(f, args) | Method(f, _, args) => std::iter::once(&**f).chain(args).collect(),
        Field(r, _) | Unary(_, r) | Loop(r) | Return(Some(r)) | Lambda(_, r) | Assign(_, r) => vec![r],
        Binary(_, a, b) | While(a, b) | SetField(a, _, b) => vec![a, b],
        Block(stmts, tail) => stmts
            .iter()
            .map(|s| match s {
                ast::Stmt::Let { value, .. } => value,
                ast::Stmt::Expr(e) => e,
            })
            .chain(tail.as_deref())
            .collect(),
        If(c, t, e) => [&**c, &**t].into_iter().chain(e.as_deref()).collect(),
        Match(s, arms) => std::iter::once(&**s).chain(arms.iter().map(|(_, b)| b)).collect(),
        Tuple(es) | List(es) => es.iter().collect(),
        Record(fs, base) => fs.iter().map(|(_, v)| v).chain(base.as_deref()).collect(),
        StructLit(_, fs) => fs.iter().map(|(_, v)| v).collect(),
        Handle(b, arms) => std::iter::once(&**b).chain(arms.iter().map(|a| &a.body)).collect(),
    }
}

/// A path, compared by its parts (for a set of them).
#[derive(Clone)]
struct PathKey(ast::Path);

impl std::ops::Deref for PathKey {
    type Target = ast::Path;
    fn deref(&self) -> &ast::Path {
        &self.0
    }
}

impl PartialEq for PathKey {
    fn eq(&self, other: &Self) -> bool {
        self.0.segments == other.0.segments
    }
}
impl Eq for PathKey {}
impl std::hash::Hash for PathKey {
    fn hash<H: std::hash::Hasher>(&self, h: &mut H) {
        self.0.segments.hash(h)
    }
}

/// The strongly connected components of a graph, each before any that
/// depend on it (Tarjan's algorithm).
fn tarjan(edges: &[Vec<usize>]) -> Vec<Vec<usize>> {
    struct T<'a> {
        edges: &'a [Vec<usize>],
        index: Vec<Option<usize>>,
        low: Vec<usize>,
        on_stack: Vec<bool>,
        stack: Vec<usize>,
        next: usize,
        out: Vec<Vec<usize>>,
    }
    fn visit(t: &mut T, v: usize) {
        t.index[v] = Some(t.next);
        t.low[v] = t.next;
        t.next += 1;
        t.stack.push(v);
        t.on_stack[v] = true;
        for &w in &t.edges[v] {
            match t.index[w] {
                None => {
                    visit(t, w);
                    t.low[v] = t.low[v].min(t.low[w]);
                }
                Some(i) if t.on_stack[w] => t.low[v] = t.low[v].min(i),
                _ => {}
            }
        }
        if Some(t.low[v]) == t.index[v] {
            let mut group = vec![];
            loop {
                let w = t.stack.pop().unwrap();
                t.on_stack[w] = false;
                group.push(w);
                if w == v {
                    break;
                }
            }
            t.out.push(group);
        }
    }
    let n = edges.len();
    let mut t = T { edges, index: vec![None; n], low: vec![0; n], on_stack: vec![false; n], stack: vec![], next: 0, out: vec![] };
    for v in 0..n {
        if t.index[v].is_none() {
            visit(&mut t, v);
        }
    }
    t.out
}
