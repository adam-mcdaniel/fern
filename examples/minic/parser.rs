//! Tokens into the tree, by recursive descent: a function for each kind of
//! thing, calling the others. Binary operators by precedence climbing.

use crate::ast::*;
use crate::lexer::{Tok, Token};

pub fn parse(tokens: Vec<Token>) -> Result<Module, String> {
    let mut p = Parser { tokens, pos: 0 };
    let mut module = Module { structs: vec![], funcs: vec![] };
    while p.peek() != &Tok::Eof {
        if p.eat("struct") {
            module.structs.push(p.struct_rest()?);
        } else {
            module.funcs.push(p.function()?);
        }
    }
    Ok(module)
}

struct Parser {
    tokens: Vec<Token>,
    pos: usize,
}

impl Parser {
    fn peek(&self) -> &Tok {
        &self.tokens[self.pos].tok
    }

    fn next(&mut self) -> Tok {
        let t = self.tokens[self.pos].tok.clone();
        if t != Tok::Eof {
            self.pos += 1;
        }
        t
    }

    fn error<T>(&self, what: &str) -> Result<T, String> {
        Err(format!("{}: expected {what}, found {:?}", self.tokens[self.pos].line, self.peek()))
    }

    /// Whether the next token is the symbol or keyword `s` (and if so, skips it).
    fn eat(&mut self, s: &str) -> bool {
        let here = match self.peek() {
            Tok::Sym(x) => *x == s,
            Tok::Ident(x) => x == s,
            _ => false,
        };
        if here {
            self.next();
        }
        here
    }

    fn expect(&mut self, s: &str) -> Result<(), String> {
        if self.eat(s) { Ok(()) } else { self.error(&format!("'{s}'")) }
    }

    fn ident(&mut self) -> Result<String, String> {
        match self.peek().clone() {
            Tok::Ident(name) => {
                self.next();
                Ok(name)
            }
            _ => self.error("a name"),
        }
    }

    /// After `struct`: `Name { a, b, c }`
    fn struct_rest(&mut self) -> Result<Struct, String> {
        let name = self.ident()?;
        self.expect("{")?;
        let mut fields = vec![];
        while !self.eat("}") {
            fields.push(self.ident()?);
            if !self.eat(",") {
                self.expect("}")?;
                break;
            }
        }
        Ok(Struct { name, fields })
    }

    /// `fn name(a, b) { ... }`
    fn function(&mut self) -> Result<Function, String> {
        self.expect("fn")?;
        let name = self.ident()?;
        self.expect("(")?;
        let mut params = vec![];
        if !self.eat(")") {
            loop {
                params.push(self.ident()?);
                if self.eat(")") {
                    break;
                }
                self.expect(",")?;
            }
        }
        let body = self.block()?;
        Ok(Function { name, params, body })
    }

    /// `{ statements }`
    fn block(&mut self) -> Result<Vec<Stmt>, String> {
        self.expect("{")?;
        let mut stmts = vec![];
        while !self.eat("}") {
            stmts.push(self.stmt()?);
        }
        Ok(stmts)
    }

    fn stmt(&mut self) -> Result<Stmt, String> {
        if self.eat("let") {
            let name = self.ident()?;
            if self.eat(":") {
                let s = self.ident()?;
                self.expect(";")?;
                return Ok(Stmt::LetStruct(name, s));
            }
            if self.eat("[") {
                let Tok::Int(n) = self.next() else { return self.error("the array's size, a number") };
                self.expect("]")?;
                self.expect(";")?;
                return Ok(Stmt::LetArray(name, n));
            }
            self.expect("=")?;
            let e = self.expr(0)?;
            self.expect(";")?;
            return Ok(Stmt::Let(name, e));
        }
        if self.eat("if") {
            return self.if_rest();
        }
        if self.eat("while") {
            let cond = self.expr(0)?;
            return Ok(Stmt::While(cond, self.block()?));
        }
        if self.eat("return") {
            let e = if self.eat(";") { None } else { Some(self.expr(0)?) };
            if e.is_some() {
                self.expect(";")?;
            }
            return Ok(Stmt::Return(e));
        }
        if self.eat("break") {
            self.expect(";")?;
            return Ok(Stmt::Break);
        }
        if self.eat("continue") {
            self.expect(";")?;
            return Ok(Stmt::Continue);
        }
        if self.eat("print") {
            self.expect("(")?;
            let mut args = vec![];
            loop {
                if let Tok::Str(s) = self.peek().clone() {
                    self.next();
                    args.push(PrintArg::Str(s));
                } else {
                    args.push(PrintArg::Expr(self.expr(0)?));
                }
                if self.eat(")") {
                    break;
                }
                self.expect(",")?;
            }
            self.expect(";")?;
            return Ok(Stmt::Print(args));
        }
        // an assignment, or an expression for what it does
        let e = self.expr(0)?;
        if self.eat("=") {
            let value = self.expr(0)?;
            self.expect(";")?;
            let target = match e {
                Expr::Var(name) => Target::Var(name),
                Expr::Index(a, i) => Target::Index(*a, *i),
                Expr::Deref(p) => Target::Deref(*p),
                Expr::Field(p, name) => Target::Field(*p, name),
                _ => return Err(format!("{}: only a variable, a[i] or *p can be assigned to", self.tokens[self.pos].line)),
            };
            return Ok(Stmt::Assign(target, value));
        }
        self.expect(";")?;
        Ok(Stmt::Expr(e))
    }

    /// After `if`: the condition, the block and any `else`.
    fn if_rest(&mut self) -> Result<Stmt, String> {
        let cond = self.expr(0)?;
        let then = self.block()?;
        let otherwise = if self.eat("else") {
            if self.eat("if") { vec![self.if_rest()?] } else { self.block()? }
        } else {
            vec![]
        };
        Ok(Stmt::If(cond, then, otherwise))
    }

    /// An expression whose binary operators all bind at least as tightly
    /// as `min` (so `1 + 2 * 3` groups the `*` first).
    fn expr(&mut self, min: u8) -> Result<Expr, String> {
        let mut left = self.unary()?;
        loop {
            let Tok::Sym(s) = self.peek() else { break };
            let (op, prec) = match *s {
                "||" => (Op::Or, 1),
                "&&" => (Op::And, 2),
                "==" => (Op::Eq, 3),
                "!=" => (Op::Ne, 3),
                "<" => (Op::Lt, 4),
                "<=" => (Op::Le, 4),
                ">" => (Op::Gt, 4),
                ">=" => (Op::Ge, 4),
                "+" => (Op::Add, 5),
                "-" => (Op::Sub, 5),
                "*" => (Op::Mul, 6),
                "/" => (Op::Div, 6),
                "%" => (Op::Rem, 6),
                _ => break,
            };
            if prec < min {
                break;
            }
            self.next();
            let right = self.expr(prec + 1)?;
            left = Expr::Binary(op, Box::new(left), Box::new(right));
        }
        Ok(left)
    }

    fn unary(&mut self) -> Result<Expr, String> {
        if self.eat("-") {
            return Ok(Expr::Neg(Box::new(self.unary()?)));
        }
        if self.eat("!") {
            return Ok(Expr::Not(Box::new(self.unary()?)));
        }
        if self.eat("&") {
            return Ok(Expr::AddrOf(Box::new(self.unary()?)));
        }
        if self.eat("*") {
            return Ok(Expr::Deref(Box::new(self.unary()?)));
        }
        let mut e = self.primary()?;
        loop {
            if self.eat("[") {
                let i = self.expr(0)?;
                self.expect("]")?;
                e = Expr::Index(Box::new(e), Box::new(i));
            } else if self.eat(".") {
                e = Expr::Field(Box::new(e), self.ident()?);
            } else {
                return Ok(e);
            }
        }
    }

    fn primary(&mut self) -> Result<Expr, String> {
        match self.peek().clone() {
            Tok::Int(n) => {
                self.next();
                Ok(Expr::Int(n))
            }
            Tok::Ident(name) if name == "new" => {
                self.next();
                Ok(Expr::New(self.ident()?))
            }
            Tok::Ident(name) if name == "sizeof" => {
                self.next();
                self.expect("(")?;
                let s = self.ident()?;
                self.expect(")")?;
                Ok(Expr::SizeOf(s))
            }
            Tok::Ident(name) => {
                self.next();
                if !self.eat("(") {
                    return Ok(Expr::Var(name));
                }
                let mut args = vec![];
                if !self.eat(")") {
                    loop {
                        args.push(self.expr(0)?);
                        if self.eat(")") {
                            break;
                        }
                        self.expect(",")?;
                    }
                }
                Ok(Expr::Call(name, args))
            }
            Tok::Sym("(") => {
                self.next();
                let e = self.expr(0)?;
                self.expect(")")?;
                Ok(e)
            }
            _ => self.error("an expression"),
        }
    }
}
