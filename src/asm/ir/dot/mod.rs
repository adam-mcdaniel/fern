//! A language with the core of Scala's type system, Dependent Object Types
//! (Amin, Rompf et al., "The Essence of Dependent Object Types"), compiled to
//! the IR.
//!
//! Its values are objects, functions, integers, booleans, strings and unit.
//! Objects have fields and type members; a type member can be abstract, with
//! only bounds, so a type can be hidden behind an interface, and the types of
//! a value's members can depend on the value itself:
//!
//! ```text
//! type Counter = { c =>
//!   type T                          // abstract: users can't see it's Int
//!   def start(): c.T
//!   def next(n: c.T): c.T
//!   def show(n: c.T): String
//! }
//! val counter: Counter = new {
//!   type T = Int
//!   def start(): T = 0
//!   def next(n: T): T = n + 1
//!   def show(n: T): String = "count " + n
//! }
//! println(counter.show(counter.next(counter.start())))
//! ```
//!
//! The types are DOT's: `Top` and `Bot`, records of fields and type members,
//! a path's type member `p.A`, intersections `S & T`, dependent functions
//! `(x: S) => T`, and recursive types `{ z => ... }`; plus `Int`, `Bool`,
//! `Unit` and `String`. Generic code takes types as objects with a type
//! member, the way DOT encodes polymorphism.
//!
//! Types are inferred where they can be: a `val`'s, a function's result
//! (recursive functions included), the parameters of a lambda passed where a
//! function type is expected, and the type of an `if` whose branches differ
//! (their join). An object's values are computed in order, and the checker
//! makes sure none is used before it's computed.
//!
//! Programs run with a garbage collector, and stop with a message when they
//! go wrong: `error(message)`, dividing by zero, a string index out of range,
//! or running out of memory or stack.
//!
//! Modules, generics, signatures and functors aren't extra features: DOT's
//! objects already are modules, and its type members already are type
//! parameters, so they're conveniences the parser writes in DOT (see
//! [`parser`]). Mutable fields and variables, `while`, and calling code in
//! other languages go beyond DOT. A [`Compiler`] loads the modules programs
//! import, from the standard library (written in DOT, in `std/`), from
//! directories, or given as source.
//!
//! # Calling out
//!
//! `extern def name(x: Int, s: String): Int` declares a function outside
//! the program, which it calls the way the VM calls one: through a label
//! the program doesn't define. In the C backend (`bf::compile`), that's a
//! C function linked with the program:
//!
//! ```c
//! void name(int64_t **tape, int64_t **ptr, int64_t *acc);
//! ```
//!
//! A call puts its arguments (at most 9) in cells next to each other and
//! points the pointer at the first, so the function finds them at
//! `(*ptr)[0]`, `(*ptr)[1]`, ...; its result is what it leaves in `*acc`,
//! and it must leave the pointer where it was. Each value is one cell: an
//! integer as it is, a boolean as 1 or 0, `Unit` as 0, and anything else
//! as the address of its record (a string's is its length, then a cell per
//! character: [`C_HEADER`] reads them, and fills buffers from `std.c`,
//! which read as strings). `C_HEADER`'s `DOT_EXTERN(ret, name, (type,
//! param)...)` writes such a function around a plain C one, taking its
//! arguments as the declaration's types say (a `String` as a C string).
//! The interpreters take host functions in Rust instead, which get the
//! same; the CPU in `hw/` can't call out.
//!
//! `builtin def` declares one of the compiler's own functions, which the
//! standard library is built on: `mem_new(n)` allocates `n` cells,
//! `mem_get(p, i)` reads cell `i` of them, `mem_set(p, i, x)` writes it,
//! and `mem_as_string(p)` reads cells as a string.
//!
//! [`parse`](parser) reads the source and resolves names, [`typer`] checks it,
//! and [`codegen`] turns it into an IR module, which the IR optimizes and
//! lowers like any other.

mod codegen;
mod parser;
mod strings;
pub mod syntax;
mod typer;

#[cfg(test)]
mod tests;

use crate::asm::ir::Module;
use std::collections::HashMap;
use std::fmt;
use std::path::PathBuf;

/// Positions are byte offsets into a source, with the source's number above
/// this bit.
const FILE_SHIFT: u32 = 40;

/// A program's source, or a module's.
#[derive(Clone, Debug)]
pub struct Source {
    pub name: String,
    pub text: String,
}

/// An error in a program, in a file, at a line and column (both from 1).
#[derive(Clone, Debug, PartialEq)]
pub struct Error {
    pub message: String,
    /// The position: a byte offset, with the file's number above it.
    pub pos: usize,
    /// "main" for the program itself, or a module's file.
    pub file: String,
    pub line: usize,
    pub col: usize,
}

impl Error {
    fn at(pos: usize, message: &str) -> Error {
        Error { message: message.to_string(), pos, file: String::new(), line: 0, col: 0 }
    }

    /// This error, with its file, line and column found in `sources`.
    fn locate(mut self, sources: &[Source]) -> Error {
        let file = self.pos >> FILE_SHIFT;
        let offset = self.pos & ((1 << FILE_SHIFT) - 1);
        let Some(source) = sources.get(file) else { return self };
        let before = &source.text[..offset.min(source.text.len())];
        self.file = source.name.clone();
        self.line = before.matches('\n').count() + 1;
        self.col = before.len() - before.rfind('\n').map_or(0, |i| i + 1) + 1;
        self
    }
}

impl fmt::Display for Error {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        if self.file.is_empty() || self.file == "main" {
            write!(f, "{}:{}: {}", self.line, self.col, self.message)
        } else {
            write!(f, "{}:{}:{}: {}", self.file, self.line, self.col, self.message)
        }
    }
}

impl std::error::Error for Error {}

/// The standard library's modules.
const STD: [(&str, &str); 7] = [
    ("std.c", include_str!("std/c.dot")),
    ("std.option", include_str!("std/option.dot")),
    ("std.list", include_str!("std/list.dot")),
    ("std.array", include_str!("std/array.dot")),
    ("std.ref", include_str!("std/ref.dot")),
    ("std.map", include_str!("std/map.dot")),
    ("std.text", include_str!("std/text.dot")),
];

/// The header for C functions that DOT programs call: how to read their
/// arguments and DOT's strings, and fill buffers from `std.c`.
pub const C_HEADER: &str = include_str!("dot.h");

/// Compiles programs: finds the modules they import.
#[derive(Clone)]
pub struct Compiler {
    modules: HashMap<String, String>,
    dirs: Vec<PathBuf>,
}

impl Default for Compiler {
    fn default() -> Self {
        Self::new()
    }
}

impl Compiler {
    /// A compiler with the standard library.
    pub fn new() -> Self {
        let mut c = Compiler { modules: HashMap::new(), dirs: vec![] };
        for (name, src) in STD {
            c.modules.insert(name.to_string(), src.to_string());
        }
        c
    }

    /// Makes `import name` find this source.
    pub fn module(&mut self, name: &str, source: &str) -> &mut Self {
        self.modules.insert(name.to_string(), source.to_string());
        self
    }

    /// Makes `import a.b` look for `a/b.dot` in this directory too.
    pub fn dir(&mut self, dir: impl Into<PathBuf>) -> &mut Self {
        self.dirs.push(dir.into());
        self
    }

    fn load(&self, name: &str) -> Option<String> {
        if let Some(src) = self.modules.get(name) {
            return Some(src.clone());
        }
        let file = format!("{}.dot", name.replace('.', "/"));
        self.dirs.iter().find_map(|d| std::fs::read_to_string(d.join(&file)).ok())
    }

    /// Parses and type checks a program.
    pub fn check(&self, src: &str) -> Result<Checked, Error> {
        let loader = |name: &str| self.load(name);
        let (term, mut names, sources) = parser::parse(src, &loader).map_err(|(e, sources)| e.locate(&sources))?;
        self.check_foreign(&term).map_err(|e| e.locate(&sources))?;
        let mut typer = typer::Typer::new(&mut names);
        let ty = typer.infer(&term).map_err(|e| e.locate(&sources))?;
        let notes = std::mem::take(&mut typer.notes);
        let implicit = std::mem::take(&mut typer.implicit);
        Ok(Checked { term, names, ty, notes, implicit })
    }

    /// Compiles a program to an IR module for cells of 16 bits and up.
    pub fn compile(&self, src: &str) -> Result<Module, Error> {
        Ok(self.check(src)?.compile(16))
    }

    /// Checks that every `builtin def` is one of the compiler's, taking as
    /// many parameters, and that every `extern def`'s name can be an
    /// external function's.
    fn check_foreign(&self, t: &syntax::Term) -> Result<(), Error> {
        let mut found = vec![];
        each_term(t, &mut |t| {
            if let syntax::TermKind::Foreign(name, params, kind) = &t.kind {
                found.push((name.clone(), params.len(), *kind, t.pos));
            }
        });
        for (name, n, kind, pos) in found {
            match kind {
                syntax::ForeignKind::Builtin => match codegen::BUILTINS.iter().find(|(b, _)| *b == name) {
                    None => return Err(Error::at(pos, &format!("there's no built-in function called `{name}`"))),
                    Some((_, want)) if *want != n => {
                        return Err(Error::at(pos, &format!("the built-in function `{name}` takes {want} parameters, not {n}")));
                    }
                    _ => {}
                },
                syntax::ForeignKind::Extern => {
                    super::verify::external_name(&name).map_err(|e| Error::at(pos, &format!("`{name}` can't be an external function: {e}")))?
                }
            }
        }
        Ok(())
    }
}

/// Calls `f` on every term in `t`.
pub(super) fn each_term(t: &syntax::Term, f: &mut dyn FnMut(&syntax::Term)) {
    use syntax::{DefKind, TermKind::*};
    f(t);
    match &t.kind {
        Lam(_, _, b) | Sel(b, _) | Ascribe(b, _) | Set(_, b) => each_term(b, f),
        App(a, b) | Let(_, _, a, b) | LetVar(_, _, a, b) | While(a, b) | Assign(a, _, b) => {
            each_term(a, f);
            each_term(b, f);
        }
        If(a, b, c) => {
            each_term(a, f);
            each_term(b, f);
            each_term(c, f);
        }
        Prim(_, args) => args.iter().for_each(|a| each_term(a, f)),
        New(_, _, defs) => {
            for d in defs {
                if let DefKind::Val(_, t) | DefKind::Var(_, t) = &d.kind {
                    each_term(t, f);
                }
            }
        }
        Var(_) | Int(_) | Bool(_) | Unit | Str(_) | TypeArg(_) | Get(_) | Foreign(..) => {}
    }
}

/// A program that's been parsed and checked.
pub struct Checked {
    term: syntax::Term,
    names: syntax::Names,
    ty: syntax::Type,
    notes: HashMap<usize, typer::Note>,
    implicit: HashMap<usize, usize>,
}

impl Checked {
    /// The program's type, as the source would write it.
    pub fn type_string(&self) -> String {
        self.names.show(&self.ty)
    }

    /// The program, as an IR module for CPUs with cells of at least
    /// `min_width` bits.
    pub fn compile(&self, min_width: u32) -> Module {
        codegen::generate(&self.term, &self.names, &self.notes, &self.implicit, min_width)
    }
}

/// Parses and type checks a program, with the standard library.
pub fn check(src: &str) -> Result<Checked, Error> {
    Compiler::new().check(src)
}

/// Compiles a program to an IR module for cells of 16 bits and up, with the
/// standard library.
pub fn compile(src: &str) -> Result<Module, Error> {
    Compiler::new().compile(src)
}
