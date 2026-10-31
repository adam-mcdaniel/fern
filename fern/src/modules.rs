//! The module system, all at compile time: loading `mod` files, collecting
//! every item into one list with its full name (`geometry::shapes::area`),
//! working out `use`s, and answering "what does this path mean, from this
//! module?" for the type checker.
//!
//! As in Rust: types and values have separate namespaces; a module sees
//! its own items, what it `use`s, and through paths, other modules' `pub`
//! items (and the private ones of the modules it's inside); paths start
//! from the module, or `crate::`, `self::`, `super::` or `std::`. Items beat
//! explicit `use`s, which beat `*` imports. The standard library's public
//! items are imported into every module (its prelude).

use crate::ast::*;
use crate::lexer::{self, Pos};
use crate::parser;
use bf::asm::fx::HashMap;
use std::path::{Path as FsPath, PathBuf};

/// Something a name can mean.
#[derive(Clone, Copy, Debug, PartialEq)]
pub enum Def {
    Module(usize),
    /// An item: a function, struct, enum, trait or effect (by number).
    Item(usize),
    /// An enum's variant.
    Variant(usize, usize),
    /// An effect's operation.
    Op(usize, usize),
    /// A trait's method.
    Method(usize, usize),
    /// Built into the language (`Int`, `print`, ...).
    Builtin(&'static str),
}

#[derive(Clone, Copy, PartialEq, PartialOrd)]
enum Priority {
    Glob,
    Use,
    Item,
}

#[derive(Clone, Copy)]
struct Binding {
    def: Def,
    public: bool,
    priority: Priority,
}

pub struct ModuleInfo {
    pub path: Vec<String>,
    pub parent: Option<usize>,
    types: HashMap<String, Binding>,
    values: HashMap<String, Binding>,
}

pub enum ItemKind {
    Fn(FnDef),
    Struct(StructDef),
    Enum(EnumDef),
    Trait(TraitDef),
    Impl(ImplDef),
    Effect(EffectDef),
    Extern(FnDef),
}

/// An item, wherever it was written, with the module it's in (whose names
/// its code sees) and its full name.
pub struct Item {
    pub module: usize,
    pub name: String,
    pub kind: ItemKind,
}

pub struct Program {
    pub modules: Vec<ModuleInfo>,
    pub items: Vec<Item>,
    /// The files, by number (`Pos::file`), for error messages.
    pub files: Vec<String>,
    pub std: usize,
    /// Each type's methods (by the type's full name, as `Type::Con` has
    /// it): their functions, by name.
    pub methods: HashMap<String, HashMap<String, usize>>,
    /// What `Self` is in each method's function: its impl's type.
    pub self_types: HashMap<usize, TypeExpr>,
}

/// The name of the methods table of tuples of `n` parts (see `add_methods`).
pub fn tuple_key(n: usize) -> String {
    format!("({})", ",".repeat(n.saturating_sub(1)))
}

/// The name of the methods table of records with exactly these fields.
pub fn record_key<'a>(labels: impl Iterator<Item = &'a str>) -> String {
    let mut labels: Vec<&str> = labels.collect();
    labels.sort();
    format!("{{{}}}", labels.join(","))
}

/// The types and values built into the language.
pub const BUILTIN_TYPES: &[&str] = &["Int", "Bool", "String", "Array", "Io"];
pub const BUILTIN_VALUES: &[&str] =
    &["print", "println", "read_int", "int_to_string", "string_length", "char_at", "char_to_string", "panic", "int_eq", "int_lt", "string_eq", "string_lt", "array", "array_get", "array_set", "array_length"];

#[derive(Clone, Copy, PartialEq)]
pub enum Ns {
    Type,
    Value,
}

type Error = (Pos, String);

struct Pending {
    module: usize,
    public: bool,
    using: Use,
}

/// Loads the program whose root is the file `root`, with the standard
/// library from `std_src`; or the error, with the files read so far (by
/// number, as `Pos::file` has them).
pub fn load(root: &str, std_src: &str) -> Result<Program, (Error, Vec<String>)> {
    let mut l = Loader {
        program: Program { modules: vec![], items: vec![], files: vec![], std: 0, methods: HashMap::default(), self_types: HashMap::default() },
        pending: vec![],
        impls: vec![],
    };
    match l.load(root, std_src) {
        Ok(()) => Ok(l.program),
        Err(e) => Err((e, l.program.files)),
    }
}

impl Loader {
    fn load(&mut self, root: &str, std_src: &str) -> Result<(), Error> {
        self.program.files.push("<std>".into());
        let mut std_items = parse_file(std_src, 0)?;
        // (and Eq, Ord and Show for tuples of every size: see derive.rs)
        std_items.extend(parse_file(&crate::derive::tuple_impls(), 0)?);
        let std = self.new_module(vec!["std".into()], None);
        self.program.std = std;
        self.add_items(std, std_items, None)?;
        let src = std::fs::read_to_string(root).map_err(|e| (Pos::default(), format!("{root}: {e}")))?;
        self.program.files.push(root.into());
        let items = parse_file(&src, 1)?;
        let main = self.new_module(vec![], None);
        let dir = FsPath::new(root).parent().map(|p| p.to_path_buf()).unwrap_or_default();
        self.add_items(main, items, Some(dir))?;
        self.resolve_uses()?;
        self.add_methods()?;
        Ok(())
    }
}

fn parse_file(src: &str, file: usize) -> Result<Vec<crate::ast::Item>, Error> {
    parser::parse(lexer::lex(src, file)?)
}

struct Loader {
    program: Program,
    pending: Vec<Pending>,
    /// Methods, by the module they're in, until the names they use are known.
    impls: Vec<(usize, MethodsDef)>,
}

impl Loader {
    fn new_module(&mut self, path: Vec<String>, parent: Option<usize>) -> usize {
        self.program.modules.push(ModuleInfo { path, parent, types: HashMap::default(), values: HashMap::default() });
        self.program.modules.len() - 1
    }

    fn bind(&mut self, module: usize, ns: Ns, name: &str, def: Def, public: bool, pos: Pos) -> Result<(), Error> {
        let m = &mut self.program.modules[module];
        let table = if ns == Ns::Type { &mut m.types } else { &mut m.values };
        if let Some(b) = table.get(name) {
            if b.priority == Priority::Item && b.def != def {
                return Err((pos, format!("{name} is defined twice in this module")));
            }
        }
        table.insert(name.to_string(), Binding { def, public, priority: Priority::Item });
        Ok(())
    }

    fn full_name(&self, module: usize, name: &str) -> String {
        let mut path = self.program.modules[module].path.clone();
        path.push(name.to_string());
        path.join("::")
    }

    /// Adds a module's items. `dir` is where its `mod name;` files are
    /// (None in the standard library, which has none).
    fn add_items(&mut self, module: usize, items: Vec<crate::ast::Item>, dir: Option<PathBuf>) -> Result<(), Error> {
        for item in items {
            match item {
                crate::ast::Item::Mod { name, public, body, pos } => {
                    let mut path = self.program.modules[module].path.clone();
                    path.push(name.clone());
                    let sub = self.new_module(path, Some(module));
                    self.bind(module, Ns::Type, &name, Def::Module(sub), public, pos)?;
                    let (items, subdir) = match body {
                        Some(items) => (items, dir.as_ref().map(|d| d.join(&name))),
                        None => {
                            let Some(dir) = &dir else { return Err((pos, "the standard library can't load files".into())) };
                            let flat = dir.join(format!("{name}.fern"));
                            let nested = dir.join(&name).join("mod.fern");
                            let file = if flat.exists() { flat } else if nested.exists() { nested } else {
                                return Err((pos, format!("no file for module {name}: expected {}", flat.display())));
                            };
                            let src = std::fs::read_to_string(&file).map_err(|e| (pos, format!("{}: {e}", file.display())))?;
                            let id = self.program.files.len();
                            self.program.files.push(file.display().to_string());
                            (parse_file(&src, id)?, Some(dir.join(&name)))
                        }
                    };
                    self.add_items(sub, items, subdir)?;
                }
                crate::ast::Item::Use { public, uses } => {
                    for using in uses {
                        self.pending.push(Pending { module, public, using });
                    }
                }
                crate::ast::Item::Fn(f) => {
                    let id = self.push(module, &f.name.clone(), ItemKind::Fn(f));
                    let ItemKind::Fn(f) = &self.program.items[id].kind else { unreachable!() };
                    let (name, public, pos) = (f.name.clone(), f.public, f.pos);
                    self.bind(module, Ns::Value, &name, Def::Item(id), public, pos)?;
                }
                crate::ast::Item::Methods(m) => self.impls.push((module, m)),
                crate::ast::Item::Extern(f) => {
                    let (name, public, pos) = (f.name.clone(), f.public, f.pos);
                    let id = self.push(module, &name, ItemKind::Extern(f));
                    self.bind(module, Ns::Value, &name, Def::Item(id), public, pos)?;
                }
                crate::ast::Item::Struct(s) => {
                    let (name, public, pos) = (s.name.clone(), s.public, s.pos);
                    let derived = crate::derive::struct_impls(&s)?;
                    let id = self.push(module, &name, ItemKind::Struct(s));
                    self.bind(module, Ns::Type, &name, Def::Item(id), public, pos)?;
                    self.add_impls(module, derived);
                }
                crate::ast::Item::Enum(e) => {
                    let (name, public, pos) = (e.name.clone(), e.public, e.pos);
                    let variants: Vec<String> = e.variants.iter().map(|(v, _)| v.clone()).collect();
                    let derived = crate::derive::enum_impls(&e)?;
                    let id = self.push(module, &name, ItemKind::Enum(e));
                    self.add_impls(module, derived);
                    self.bind(module, Ns::Type, &name, Def::Item(id), public, pos)?;
                    // (the variants are also names in the module, as in Haskell)
                    for (i, v) in variants.iter().enumerate() {
                        self.bind(module, Ns::Value, v, Def::Variant(id, i), public, pos)?;
                    }
                }
                crate::ast::Item::Trait(t) => {
                    let (name, public, pos) = (t.name.clone(), t.public, t.pos);
                    let id = self.push(module, &name, ItemKind::Trait(t));
                    self.bind(module, Ns::Type, &name, Def::Item(id), public, pos)?;
                }
                crate::ast::Item::Effect(e) => {
                    let (name, public, pos) = (e.name.clone(), e.public, e.pos);
                    let ops: Vec<String> = e.ops.iter().map(|o| o.name.clone()).collect();
                    let id = self.push(module, &name, ItemKind::Effect(e));
                    self.bind(module, Ns::Type, &name, Def::Item(id), public, pos)?;
                    // (and its operations, which are called like functions)
                    for (i, op) in ops.iter().enumerate() {
                        self.bind(module, Ns::Value, op, Def::Op(id, i), public, pos)?;
                    }
                }
                crate::ast::Item::Impl(i) => {
                    let name = format!("impl{}", self.program.items.len());
                    self.push(module, &name, ItemKind::Impl(i));
                }
            }
        }
        Ok(())
    }

    fn add_impls(&mut self, module: usize, impls: Vec<ImplDef>) {
        for i in impls {
            let name = format!("impl{}", self.program.items.len());
            self.push(module, &name, ItemKind::Impl(i));
        }
    }

    fn push(&mut self, module: usize, name: &str, kind: ItemKind) -> usize {
        let name = self.full_name(module, name);
        self.program.items.push(Item { module, name, kind });
        self.program.items.len() - 1
    }

    /// Each method, as a function (named for its type: `std::Map::insert`),
    /// in its type's table. A type's methods are in the module that defines
    /// it (a built-in type's, in the standard library).
    fn add_methods(&mut self) -> Result<(), Error> {
        for (module, m) in std::mem::take(&mut self.impls) {
            // (the table its methods go in, and the name they're under: a
            // named type's own; a tuple's, one for each size; a record's, one
            // for each set of fields)
            let (type_name, short) = match &m.ty {
                TypeExpr::Named(path, _) => {
                    let (type_name, owner) = match self.program.lookup(module, path, Ns::Type).map_err(|e| (path.pos, e))? {
                        Def::Item(i) if matches!(self.program.items[i].kind, ItemKind::Struct(_) | ItemKind::Enum(_)) => {
                            (self.program.items[i].name.clone(), self.program.items[i].module)
                        }
                        Def::Builtin(b) if b != "Io" => (b.to_string(), self.program.std),
                        _ => return Err((path.pos, format!("{path} isn't a struct, an enum or a built-in type, so it has no methods"))),
                    };
                    if owner != module {
                        return Err((m.pos, format!("{path}'s methods have to be in the module that defines it")));
                    }
                    (type_name, path.last().to_string())
                }
                TypeExpr::Tuple(ts) if ts.len() >= 2 => (tuple_key(ts.len()), format!("Tuple{}", ts.len())),
                TypeExpr::Record(fields, None) => {
                    let mut labels: Vec<&str> = fields.iter().map(|(l, _)| l.as_str()).collect();
                    labels.sort();
                    (record_key(labels.iter().copied()), format!("Record_{}", labels.join("_")))
                }
                TypeExpr::Record(_, Some(_)) => return Err((m.pos, "a record's methods are for records with exactly those fields: without `..`".into())),
                _ => return Err((m.pos, "only a struct, an enum, a built-in type, a tuple or a record has methods".into())),
            };
            for f in m.methods {
                if self.program.methods.get(&type_name).is_some_and(|t| t.contains_key(&f.name)) {
                    return Err((f.pos, format!("{short} already has a method {}", f.name)));
                }
                let method = f.name.clone();
                let mut generics = m.generics.clone();
                generics.extend(f.generics.iter().cloned());
                let func = FnDef { name: format!("{short}::{method}"), generics, ..f };
                let id = self.push(module, &format!("{short}::{method}"), ItemKind::Fn(func));
                self.program.self_types.insert(id, m.ty.clone());
                self.program.methods.entry(type_name.clone()).or_default().insert(method, id);
            }
        }
        Ok(())
    }

    /// Works out the `use`s, over and over, since one can bring in a name
    /// another uses, until nothing changes; then the prelude.
    fn resolve_uses(&mut self) -> Result<(), Error> {
        let pending = std::mem::take(&mut self.pending);
        let mut done = vec![false; pending.len()];
        loop {
            let mut progress = false;
            for (i, p) in pending.iter().enumerate() {
                if done[i] {
                    continue;
                }
                if self.try_use(p)? {
                    done[i] = true;
                    progress = true;
                }
            }
            if !progress {
                break;
            }
        }
        if let Some(i) = done.iter().position(|d| !d) {
            let u = &pending[i].using;
            return Err((u.path.pos, format!("can't find {}", u.path)));
        }
        // the prelude: everything public in std, in every module but std
        let std = self.program.std;
        for m in 0..self.program.modules.len() {
            if m != std {
                self.glob(m, Def::Module(std), false);
            }
        }
        Ok(())
    }

    /// Brings in one `use`, if what it names can be found yet.
    fn try_use(&mut self, p: &Pending) -> Result<bool, Error> {
        let path = &p.using.path;
        if p.using.glob {
            let Ok(def) = self.program.lookup(p.module, path, Ns::Type) else { return Ok(false) };
            self.glob(p.module, def, p.public);
            return Ok(true);
        }
        let types = self.program.lookup(p.module, path, Ns::Type).ok();
        let values = self.program.lookup(p.module, path, Ns::Value).ok();
        if types.is_none() && values.is_none() {
            return Ok(false);
        }
        let name = p.using.alias.clone().unwrap_or_else(|| path.last().to_string());
        let m = &mut self.program.modules[p.module];
        for (def, table) in [(types, &mut m.types), (values, &mut m.values)] {
            if let Some(def) = def {
                if table.get(&name).is_none_or(|b| b.priority < Priority::Use) {
                    table.insert(name.clone(), Binding { def, public: p.public, priority: Priority::Use });
                }
            }
        }
        Ok(true)
    }

    /// `use m::*`: the public names of a module (or an enum's variants, or
    /// an effect's operations), where nothing more definite has the name.
    fn glob(&mut self, into: usize, from: Def, public: bool) {
        let mut adds: Vec<(Ns, String, Def)> = vec![];
        match from {
            Def::Module(m) => {
                let src = &self.program.modules[m];
                for (ns, table) in [(Ns::Type, &src.types), (Ns::Value, &src.values)] {
                    for (name, b) in table {
                        if b.public {
                            adds.push((ns, name.clone(), b.def));
                        }
                    }
                }
            }
            Def::Item(i) => match &self.program.items[i].kind {
                ItemKind::Enum(e) => adds.extend(e.variants.iter().enumerate().map(|(k, (v, _))| (Ns::Value, v.clone(), Def::Variant(i, k)))),
                ItemKind::Effect(e) => adds.extend(e.ops.iter().enumerate().map(|(k, o)| (Ns::Value, o.name.clone(), Def::Op(i, k)))),
                _ => {}
            },
            _ => {}
        }
        let m = &mut self.program.modules[into];
        for (ns, name, def) in adds {
            let table = if ns == Ns::Type { &mut m.types } else { &mut m.values };
            if table.get(&name).is_none() {
                table.insert(name, Binding { def, public, priority: Priority::Glob });
            }
        }
    }
}

impl Program {
    /// Whether module `inner` is `outer` or inside it (and so sees its
    /// private items).
    fn within(&self, inner: usize, outer: usize) -> bool {
        let mut m = Some(inner);
        while let Some(x) = m {
            if x == outer {
                return true;
            }
            m = self.modules[x].parent;
        }
        false
    }

    fn in_module(&self, from: usize, module: usize, name: &str, ns: Ns) -> Option<Def> {
        let m = &self.modules[module];
        let table = if ns == Ns::Type { &m.types } else { &m.values };
        let b = table.get(name)?;
        (b.public || self.within(from, module)).then_some(b.def)
    }

    /// What `path` means from module `from`, in namespace `ns` (for its last
    /// part; the parts before it are modules, or an enum, effect or trait).
    pub fn lookup(&self, from: usize, path: &Path, ns: Ns) -> Result<Def, String> {
        let segs = &path.segments;
        let first_ns = if segs.len() == 1 { ns } else { Ns::Type };
        let mut def = match segs[0].as_str() {
            "crate" if segs.len() > 1 => Def::Module(self.root_of(from)),
            "self" if segs.len() > 1 => Def::Module(from),
            "super" if segs.len() > 1 => Def::Module(self.modules[from].parent.ok_or("there's no module above this one")?),
            first => self
                .in_module(from, from, first, first_ns)
                .or_else(|| (first == "std").then_some(Def::Module(self.std)))
                .or_else(|| builtin(first, first_ns))
                .ok_or_else(|| format!("can't find {first}"))?,
        };
        for (i, seg) in segs.iter().enumerate().skip(1) {
            let last = i == segs.len() - 1;
            let seg_ns = if last { ns } else { Ns::Type };
            def = match def {
                Def::Module(m) => self.in_module(from, m, seg, seg_ns).ok_or_else(|| format!("can't find {seg} in {}", segs[..i].join("::")))?,
                Def::Item(it) if last => self.member(from, it, seg).ok_or_else(|| format!("{} has no {seg}", segs[..i].join("::")))?,
                // (a built-in type's method: `String::from_chars`)
                Def::Builtin(b) if last => self.method(from, b, seg).ok_or_else(|| format!("{b} has no {seg}"))?,
                _ => return Err(format!("{} isn't a module", segs[..i].join("::"))),
            };
        }
        Ok(def)
    }

    /// An enum's variant, an effect's operation, a trait's method, or a
    /// struct or enum's method, by name.
    fn member(&self, from: usize, item: usize, name: &str) -> Option<Def> {
        match &self.items[item].kind {
            ItemKind::Enum(e) => e.variants.iter().position(|(v, _)| v == name).map(|k| Def::Variant(item, k)).or_else(|| self.method(from, &self.items[item].name, name)),
            ItemKind::Struct(_) => self.method(from, &self.items[item].name, name),
            ItemKind::Effect(e) => e.ops.iter().position(|o| o.name == name).map(|k| Def::Op(item, k)),
            ItemKind::Trait(t) => t.methods.iter().position(|m| m.name == name).map(|k| Def::Method(item, k)),
            _ => None,
        }
    }

    /// Type `type_name`'s method `name`, if it has one that module `from`
    /// can see.
    pub fn method(&self, from: usize, type_name: &str, name: &str) -> Option<Def> {
        let id = *self.methods.get(type_name)?.get(name)?;
        self.can_see(from, id).then_some(Def::Item(id))
    }

    /// Whether module `from` can use item `id`: it's public, or `from` is
    /// its module or inside it.
    pub fn can_see(&self, from: usize, id: usize) -> bool {
        let public = matches!(&self.items[id].kind, ItemKind::Fn(f) if f.public);
        let home = self.items[id].module;
        let mut m = Some(from);
        while let Some(x) = m {
            if x == home {
                return true;
            }
            m = self.modules[x].parent;
        }
        public
    }

    fn root_of(&self, mut m: usize) -> usize {
        while let Some(p) = self.modules[m].parent {
            m = p;
        }
        m
    }
}

fn builtin(name: &str, ns: Ns) -> Option<Def> {
    let names = if ns == Ns::Type { BUILTIN_TYPES } else { BUILTIN_VALUES };
    names.iter().find(|&&n| n == name).map(|&n| Def::Builtin(n))
}
