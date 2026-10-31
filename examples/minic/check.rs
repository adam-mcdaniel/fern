//! Finding the mistakes before generating code: variables used before
//! they're declared, calls to functions that don't exist or with the wrong
//! number of arguments, `break` outside a loop. Doing it here keeps code
//! generation simple: it can assume the program makes sense.

use crate::ast::*;
use std::collections::{HashMap, HashSet};

pub fn check(module: &Module) -> Result<(), String> {
    let funcs = &module.funcs;
    // the structs: their names, and that each field has one place
    let mut structs = HashSet::new();
    for s in &module.structs {
        if !structs.insert(s.name.as_str()) {
            return Err(format!("there are two structs called {}", s.name));
        }
        if s.fields.is_empty() {
            return Err(format!("{} has no fields", s.name));
        }
    }
    let fields = field_offsets(&module.structs)?;
    // every function's number of parameters, first, so a function can call
    // ones defined after it
    let mut arity: HashMap<&str, usize> = HashMap::from([("read", 0), ("array", 1)]);
    for f in funcs {
        if arity.insert(&f.name, f.params.len()).is_some() {
            return Err(format!("there are two functions called {}", f.name));
        }
    }
    match arity.get("main") {
        Some(0) => {}
        Some(_) => return Err("main takes no parameters".into()),
        None => return Err("there's no main function".into()),
    }
    for f in funcs {
        let mut c = Checker { arity: &arity, structs: &structs, fields: &fields, scopes: vec![f.params.iter().cloned().collect()], loops: 0 };
        c.block(&f.body).map_err(|e| format!("in {}: {e}", f.name))?;
    }
    Ok(())
}

struct Checker<'a> {
    arity: &'a HashMap<&'a str, usize>,
    structs: &'a HashSet<&'a str>,
    fields: &'a HashMap<String, i64>,
    /// The variables declared in each block that's open, innermost last.
    scopes: Vec<HashSet<String>>,
    loops: usize,
}

impl Checker<'_> {
    fn block(&mut self, stmts: &[Stmt]) -> Result<(), String> {
        self.scopes.push(HashSet::new());
        for s in stmts {
            self.stmt(s)?;
        }
        self.scopes.pop();
        Ok(())
    }

    fn is_struct(&self, name: &str) -> Result<(), String> {
        if self.structs.contains(name) { Ok(()) } else { Err(format!("there's no struct called {name}")) }
    }

    fn is_field(&self, name: &str) -> Result<(), String> {
        if self.fields.contains_key(name) { Ok(()) } else { Err(format!("no struct has a field called {name}")) }
    }

    fn declared(&self, name: &str) -> Result<(), String> {
        if self.scopes.iter().any(|s| s.contains(name)) { Ok(()) } else { Err(format!("{name} isn't declared")) }
    }

    fn stmt(&mut self, s: &Stmt) -> Result<(), String> {
        match s {
            Stmt::Let(name, e) => {
                // (the value first: `let x = x + 1;` means the x from outside)
                self.expr(e)?;
                self.scopes.last_mut().unwrap().insert(name.clone());
            }
            Stmt::LetArray(name, n) => {
                if *n <= 0 {
                    return Err(format!("{name} needs at least one cell"));
                }
                self.scopes.last_mut().unwrap().insert(name.clone());
            }
            Stmt::LetStruct(name, s) => {
                self.is_struct(s)?;
                self.scopes.last_mut().unwrap().insert(name.clone());
            }
            Stmt::Assign(target, e) => {
                match target {
                    Target::Var(name) => self.declared(name)?,
                    Target::Index(a, i) => {
                        self.expr(a)?;
                        self.expr(i)?;
                    }
                    Target::Deref(p) => self.expr(p)?,
                    Target::Field(p, field) => {
                        self.is_field(field)?;
                        self.expr(p)?;
                    }
                }
                self.expr(e)?;
            }
            Stmt::If(c, then, otherwise) => {
                self.expr(c)?;
                self.block(then)?;
                self.block(otherwise)?;
            }
            Stmt::While(c, body) => {
                self.expr(c)?;
                self.loops += 1;
                self.block(body)?;
                self.loops -= 1;
            }
            Stmt::Return(e) => {
                if let Some(e) = e {
                    self.expr(e)?;
                }
            }
            Stmt::Break | Stmt::Continue => {
                if self.loops == 0 {
                    return Err("break or continue outside a loop".into());
                }
            }
            Stmt::Print(args) => {
                for a in args {
                    if let PrintArg::Expr(e) = a {
                        self.expr(e)?;
                    }
                }
            }
            Stmt::Expr(e) => self.expr(e)?,
        }
        Ok(())
    }

    fn expr(&mut self, e: &Expr) -> Result<(), String> {
        match e {
            Expr::Int(_) => Ok(()),
            Expr::Var(name) => self.declared(name),
            Expr::Index(a, b) | Expr::Binary(_, a, b) => {
                self.expr(a)?;
                self.expr(b)
            }
            Expr::Neg(a) | Expr::Not(a) | Expr::Deref(a) => self.expr(a),
            Expr::AddrOf(a) => match &**a {
                Expr::Var(_) | Expr::Index(..) | Expr::Field(..) => self.expr(a),
                _ => Err("& only takes the address of a variable, a[i] or p.x".into()),
            },
            Expr::Field(p, field) => {
                self.is_field(field)?;
                self.expr(p)
            }
            Expr::New(s) | Expr::SizeOf(s) => self.is_struct(s),
            Expr::Call(name, args) => {
                match self.arity.get(name.as_str()) {
                    None => return Err(format!("there's no function called {name}")),
                    Some(&n) if n != args.len() => return Err(format!("{name} takes {n} arguments, not {}", args.len())),
                    _ => {}
                }
                args.iter().try_for_each(|a| self.expr(a))
            }
        }
    }
}
