use logos::Logos;

pub mod cpu;
pub mod asm;
pub mod interp;

pub const PRELUDE: &str = r#"
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>

static int64_t **stack = NULL;
static int64_t *tape=NULL, *ptr=NULL, acc=0;
static void (*f)() = NULL;
"#;

#[derive(Logos, Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
#[logos(skip r"[ \t\n\f]+")]
pub enum Op {
    #[token("*")]

    Deref, // *
    #[token("&")]
    Refer, // &
    #[token("?")]
    Where, // ?
    
    #[regex(">+", |lex| lex.slice().chars().filter(|c| *c == '>').count() as i64)]
    #[regex("<+", |lex| -(lex.slice().chars().filter(|c| *c == '<').count() as i64))]
    Move(i64),

    #[regex("[0-9]+", |lex| lex.slice().parse::<u64>().ok())]
    #[regex("0x[0-9a-fA-F]+", |lex| u64::from_str_radix(&lex.slice()[2..], 16).ok())]
    #[regex("0o[0-7]+", |lex| u64::from_str_radix(&lex.slice()[2..], 8).ok())]
    Set(u64),

    #[regex("@[_a-zA-Z][_a-zA-Z0-9]*", |lex| {
        let mut arr = [0u8; 16];
        for (i, ch) in lex.slice().chars().enumerate() {
            if i == 0 { continue }
            arr[i-1] = ch as u8;
        }
        arr[15] = 0;
        arr
    })]
    Label([u8; 16]),
    #[token("$")]
    Load,
    #[token("=")]
    Store,
    
    #[token("!")]
    Call,
    
    #[token(",")]
    Read,
    #[token(".")]
    Write,
    
    #[token("+")]
    Add,
    #[token("-")]
    Neg,
    #[token("#")]
    Positive,
    
    #[token("[")]
    While,
    #[token("]")]
    EndWhile,
    
    #[token(":")]
    Func,
    #[token(";")]
    EndFunc,
}

pub fn parse(code: &str) -> Result<Vec<Op>, ()> {
    Op::lexer(code).collect::<Result<Vec<Op>, ()>>()
}

pub fn compile(ops: &[Op]) -> String {
    use Op::*;
    let mut buf = String::new();
    let mut label = String::new();
    let mut global_defs = String::new();
    let mut main = String::new();
    let mut labels = vec![];
    for op in ops {
        match op {
            Deref => {
                buf += &format!("*stack = ptr; stack += 1; ptr = (int64_t*)*ptr;")
            }
            Refer => {
                buf += &format!("stack -= 1; ptr = (int64_t*)*stack;")
            }
            Where => {
                buf += &format!("acc = (int64_t)ptr;")
            }
            Move(n) => {
                buf += &format!("ptr += {n};")
            }
            Set(n) => {
                buf += &format!("acc = {n};")
            }
            Label(s) => {
                label.clear();
                for ch in s {
                    if *ch != 0 {
                        label.push(*ch as char);
                    } else {
                        break;
                    }
                }
                labels.push(label.clone());
                buf += &format!("acc = (int64_t){label};",)
            }
            Add => {
                buf += &format!("acc += *ptr;")
            }
            Neg => {
                buf += &format!("acc = -acc;")
            }
            Positive => {
                buf += &format!("acc = acc > 0;")
            }
            Load => {
                buf += &format!("acc = *ptr;")
            }
            Store => {
                buf += &format!("*ptr = acc;");
            }
            Call => {
                buf += &format!("((void (*)(int64_t**, int64_t**, int64_t*))acc)(&tape, &ptr, &acc);")
            }
            Read => {
                buf += &format!("acc = getchar();")
            }
            Write => {
                buf += &format!("putchar(acc);")
            }

            While => {
                buf += &format!("while (acc) {{")
            }

            EndWhile => {
                buf += &format!("}}")
            }

            Func => {
                main += &buf;
                buf = format!("void {label}(int64_t **t, int64_t **p, int64_t *a) {{");
            }

            EndFunc => {
                global_defs += &buf;
                global_defs.push('}');
                buf.clear();
            }
        }
    }

    main += &buf;
    

    let result = format!("{PRELUDE} {} {global_defs} int main() {{stack=malloc(1024 * sizeof(int64_t)); tape=malloc(100000 * sizeof(int64_t)); ptr=tape; {main} return 0;}}", labels.into_iter().map(|name| format!("void {name}(int64_t **tape, int64_t **ptr, int64_t *acc);")).collect::<String>());
    return result;
}