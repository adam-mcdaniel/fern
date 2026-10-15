use logos::Logos;

pub mod cpu;
pub mod asm;
pub mod interp;
pub mod backends;

#[derive(Logos, Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
#[logos(skip r"[ \t\n\f]+")]
pub enum Op {
    #[token("*")]
    Deref, // *
    #[token("&")]
    Refer, // &
    #[token("?")]
    Where, // ?

    #[regex(">+", |lex| lex.slice().len() as i64)]
    #[regex("<+", |lex| -(lex.slice().len() as i64))]
    #[regex(r">\{[0-9]+\}", |lex| lex.slice()[2..lex.slice().len() - 1].parse::<i64>().ok())]
    #[regex(r"<\{[0-9]+\}", |lex| lex.slice()[2..lex.slice().len() - 1].parse::<i64>().ok().map(|n| -n))]
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

pub trait Target {
    fn compile(&mut self, ops: &[Op]) -> String;
}

