//! The tree into a `bf::ir::Program`: the only part of the compiler that
//! knows about the IR.
//!
//! The whole idea: walk the tree, and for each thing in it, call the
//! `Program`/`Func` method that does it. A statement becomes calls on `f`;
//! an expression becomes an `ir::Expr`. The optimizer then cleans up
//! everything this does naively (all the extra variables, for instance).
//!
//! Two things need care, and both come from `ir::Expr` being a formula
//! that's worked out where it's *used*, not where it's made:
//!
//! - Order. In `a[0] + f(a)`, if `f` changes `a[0]`, the left side has to be
//!   read before the call. So a value that's needed after a call is copied
//!   into a variable first (`f.var(x)`), which fixes it at that point.
//! - Loop conditions. `while_` takes a formula, but a condition that calls a
//!   function has to make the call every time round, so `while` is a
//!   `loop_` that works out the condition at its top and `break`s.
//!
//! Structs need nothing from the IR: a struct is a block of cells, and a
//! field is an offset into it, from a table (`Layout`) the compiler keeps.
//! `p.x` is `p.at(offset of x)`, and `new Point` is `f.alloc(size of Point)`.

use crate::ast::{self, field_offsets, Op, PrintArg, Stmt, Target};
use bf::ir::{Expr, Func, Program, Var};
use std::collections::HashMap;

/// Where the structs' fields are, and how big each struct is, in cells.
struct Layout {
    offsets: HashMap<String, i64>,
    sizes: HashMap<String, i64>,
}

/// What code generation needs to know at each point: the variables in
/// scope, by name, and the structs' layout. A `Var` is a handle (it's
/// `Copy`), so copying the whole map for each block is cheap, and it's
/// what scoping is: a block sees everything outside it, and what it
/// declares goes away at its end. Assigning changes the variable, not the
/// map, so it's seen outside the block too.
#[derive(Clone)]
struct Env<'a> {
    vars: HashMap<String, Var>,
    layout: &'a Layout,
}

pub fn generate(module: &ast::Module) -> Program {
    let layout = Layout {
        offsets: field_offsets(&module.structs).expect("checked"),
        sizes: module.structs.iter().map(|s| (s.name.clone(), s.fields.len() as i64)).collect(),
    };
    let mut p = Program::new();
    for func in &module.funcs {
        if func.name == "main" {
            p.main(|f| block(f, &Env { vars: HashMap::new(), layout: &layout }, &func.body));
        } else {
            let params: Vec<&str> = func.params.iter().map(|s| s.as_str()).collect();
            p.function(&func.name, &params, |f| {
                let vars = func.params.iter().map(|n| (n.clone(), f.arg(n))).collect();
                block(f, &Env { vars, layout: &layout }, &func.body);
            });
        }
    }
    p
}

/// A block, in a scope of its own.
fn block(f: &mut Func, outside: &Env, stmts: &[Stmt]) {
    let mut env = outside.clone();
    for s in stmts {
        stmt(f, &mut env, s);
    }
}

fn stmt(f: &mut Func, env: &mut Env, s: &Stmt) {
    match s {
        Stmt::Let(name, e) => {
            let value = expr(f, env, e);
            let v = f.var(value);
            env.vars.insert(name.clone(), v);
        }
        Stmt::LetArray(name, n) => {
            // (a variable holding the array's address, like any pointer)
            let a = f.array(*n as u64);
            env.vars.insert(name.clone(), a);
        }
        Stmt::LetStruct(name, s) => {
            let a = f.array(env.layout.sizes[s] as u64);
            env.vars.insert(name.clone(), a);
        }
        Stmt::Assign(Target::Var(name), e) => {
            let value = expr(f, env, e);
            f.set(env.vars[name], value);
        }
        Stmt::Assign(Target::Index(a, i), e) => {
            // (each part fixed before the next one's calls, if it has any)
            let a = operand(f, env, a, i.has_call() || e.has_call());
            let i = operand(f, env, i, e.has_call());
            let value = expr(f, env, e);
            f.set(a.at(i), value);
        }
        Stmt::Assign(Target::Deref(p), e) => {
            let p = operand(f, env, p, e.has_call());
            let value = expr(f, env, e);
            f.set(p.at(0), value);
        }
        Stmt::Assign(Target::Field(p, field), e) => {
            let p = operand(f, env, p, e.has_call());
            let value = expr(f, env, e);
            f.set(p.at(env.layout.offsets[field]), value);
        }
        Stmt::If(c, then, otherwise) => {
            let c = expr(f, env, c);
            // (both closures only read `env`, so they can both borrow it)
            let env: &Env = env;
            f.if_else(c, |f| block(f, env, then), |f| block(f, env, otherwise));
        }
        Stmt::While(c, body) => {
            let env: &Env = env;
            f.loop_(|f| {
                let c = expr(f, env, c);
                f.if_(!c, |f| f.break_());
                block(f, env, body);
            });
        }
        Stmt::Return(e) => {
            let value = match e {
                Some(e) => expr(f, env, e),
                None => 0.into(),
            };
            f.ret(value);
        }
        Stmt::Break => f.break_(),
        Stmt::Continue => f.continue_(),
        Stmt::Print(args) => {
            for a in args {
                match a {
                    PrintArg::Str(s) => f.print(s),
                    PrintArg::Expr(e) => {
                        let value = expr(f, env, e);
                        f.print_int(value);
                    }
                }
            }
        }
        Stmt::Expr(e) => {
            // (for what it does: the calls in it are made, the value isn't used)
            expr(f, env, e);
        }
    }
}

/// `e`'s value, fixed in a variable if `later_calls`: if something worked
/// out after it calls a function (see the top of the file).
fn operand(f: &mut Func, env: &Env, e: &ast::Expr, later_calls: bool) -> Expr {
    let value = expr(f, env, e);
    if later_calls { f.var(value).into() } else { value }
}

fn expr(f: &mut Func, env: &Env, e: &ast::Expr) -> Expr {
    match e {
        ast::Expr::Int(n) => (*n).into(),
        ast::Expr::Var(name) => env.vars[name].into(),
        ast::Expr::Index(a, i) => {
            let a = operand(f, env, a, i.has_call());
            let i = expr(f, env, i);
            a.at(i)
        }
        ast::Expr::Neg(a) => -expr(f, env, a),
        ast::Expr::Not(a) => !expr(f, env, a),
        // a pointer is just an address: `*p` is the cell at it, and `p[i]`
        // (above) the cell i cells on
        ast::Expr::Deref(p) => expr(f, env, p).at(0),
        // a struct is an address, and a field an offset from it
        ast::Expr::Field(p, field) => expr(f, env, p).at(env.layout.offsets[field]),
        ast::Expr::New(s) => f.alloc(env.layout.sizes[s]).into(),
        ast::Expr::SizeOf(s) => env.layout.sizes[s].into(),
        ast::Expr::AddrOf(target) => match &**target {
            ast::Expr::Var(name) => f.addr(env.vars[name]),
            ast::Expr::Field(p, field) => expr(f, env, p).index(env.layout.offsets[field]),
            ast::Expr::Index(a, i) => {
                let a = operand(f, env, a, i.has_call());
                let i = expr(f, env, i);
                a.index(i)
            }
            _ => unreachable!("the checker allows only these"),
        },
        ast::Expr::Call(name, args) => match name.as_str() {
            "read" => f.read_int().into(),
            "array" => {
                let n = expr(f, env, &args[0]);
                f.alloc(n).into()
            }
            _ => {
                // (every argument fixed in a variable, in order, so a later
                // argument's calls can't change an earlier one: the
                // optimizer removes the variables that didn't need to be)
                let values: Vec<Expr> = args
                    .iter()
                    .map(|a| {
                        let v = expr(f, env, a);
                        f.var(v).into()
                    })
                    .collect();
                f.call(name, values).into()
            }
        },
        ast::Expr::Binary(Op::And, a, b) => {
            // `a && b`: b only if a is true
            let result = f.var(0);
            let a = expr(f, env, a);
            f.if_(a, |f| {
                let b = expr(f, env, b);
                f.set(result, b.ne(0));
            });
            result.into()
        }
        ast::Expr::Binary(Op::Or, a, b) => {
            // `a || b`: b only if a is false
            let result = f.var(1);
            let a = expr(f, env, a);
            f.if_(!a, |f| {
                let b = expr(f, env, b);
                f.set(result, b.ne(0));
            });
            result.into()
        }
        ast::Expr::Binary(op, a, b) => {
            let a = operand(f, env, a, b.has_call());
            let b = expr(f, env, b);
            match op {
                Op::Add => a + b,
                Op::Sub => a - b,
                Op::Mul => a * b,
                Op::Div => a / b,
                Op::Rem => a % b,
                Op::Eq => a.eq(b),
                Op::Ne => a.ne(b),
                Op::Lt => a.lt(b),
                Op::Le => a.le(b),
                Op::Gt => a.gt(b),
                Op::Ge => a.ge(b),
                Op::And | Op::Or => unreachable!(),
            }
        }
    }
}
