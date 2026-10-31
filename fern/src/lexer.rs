//! Source text into tokens, each with where it is in its file.

use std::fmt;

#[derive(Clone, Debug, PartialEq)]
pub enum Tok {
    Int(i64),
    /// `1.25`: a rational number, as a numerator over a power of ten
    Decimal(i64, i64),
    Str(String),
    Ident(String),
    /// `'e`: an effect variable
    Tick(String),
    Sym(&'static str),
    Eof,
}

impl fmt::Display for Tok {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            Tok::Int(n) => write!(f, "{n}"),
            Tok::Decimal(n, d) => write!(f, "{n}/{d}"),
            Tok::Str(s) => write!(f, "{s:?}"),
            Tok::Ident(s) => write!(f, "{s}"),
            Tok::Tick(s) => write!(f, "'{s}"),
            Tok::Sym(s) => write!(f, "{s}"),
            Tok::Eof => write!(f, "the end of the file"),
        }
    }
}

/// Where something is: a file (by number, see `modules`), a line, and a
/// column (from 1; 0 if it's not known), in characters.
#[derive(Clone, Copy, Debug, Default, PartialEq)]
pub struct Pos {
    pub file: usize,
    pub line: usize,
    pub col: usize,
}

#[derive(Clone, Debug)]
pub struct Token {
    pub tok: Tok,
    pub pos: Pos,
}

// (longest first, so `::` isn't read as two `:`s)
const SYMBOLS: &[&str] = &[
    "::", "->", "=>", "..=", "..", "==", "!=", "<=", ">=", "&&", "||", "++", "<<", ">>", "(", ")", "{", "}", "[", "]", "<", ">", ",", ";", ":", ".",
    "=", "+", "-", "*", "/", "%", "!", "|", "&", "^", "#",
];

pub fn lex(src: &str, file: usize) -> Result<Vec<Token>, (Pos, String)> {
    let chars: Vec<char> = src.chars().collect();
    let mut i = 0;
    let mut pos = Pos { file, line: 1, col: 1 };
    let mut out = vec![];
    // (where the line starts, for the column each token starts in)
    let mut line_start = 0;
    while i < chars.len() {
        let c = chars[i];
        pos.col = i - line_start + 1;
        if c == '\n' {
            pos.line += 1;
            i += 1;
            line_start = i;
        } else if c.is_whitespace() {
            i += 1;
        } else if c == '/' && chars.get(i + 1) == Some(&'/') {
            while i < chars.len() && chars[i] != '\n' {
                i += 1;
            }
        } else if c == '0' && chars.get(i + 1) == Some(&'x') {
            // 0xff
            let start = i + 2;
            i += 2;
            while i < chars.len() && (chars[i].is_ascii_hexdigit() || chars[i] == '_') {
                i += 1;
            }
            let text: String = chars[start..i].iter().filter(|&&c| c != '_').collect();
            let n = i64::from_str_radix(&text, 16).map_err(|_| (pos, format!("0x{text} isn't a number that fits")))?;
            out.push(Token { tok: Tok::Int(n), pos });
        } else if c.is_ascii_digit() {
            let start = i;
            while i < chars.len() && (chars[i].is_ascii_digit() || chars[i] == '_') {
                i += 1;
            }
            // (a decimal point only with a digit after it: `2.pow(3)` is a method call)
            let frac_start = i + 1;
            let decimal = i + 1 < chars.len() && chars[i] == '.' && chars[i + 1].is_ascii_digit();
            if decimal {
                i += 1;
                while i < chars.len() && (chars[i].is_ascii_digit() || chars[i] == '_') {
                    i += 1;
                }
            }
            let whole: String = chars[start..if decimal { frac_start - 1 } else { i }].iter().filter(|&&c| c != '_').collect();
            if decimal {
                let frac: String = chars[frac_start..i].iter().filter(|&&c| c != '_').collect();
                let text = format!("{whole}.{frac}");
                let num = format!("{whole}{frac}").parse::<i64>().map_err(|_| (pos, format!("{text} has too many digits")))?;
                let den = 10i64.checked_pow(frac.len() as u32).ok_or_else(|| (pos, format!("{text} has too many digits")))?;
                out.push(Token { tok: Tok::Decimal(num, den), pos });
            } else {
                let n = whole.parse().map_err(|_| (pos, format!("{whole} is too big")))?;
                out.push(Token { tok: Tok::Int(n), pos });
            }
        } else if c.is_alphabetic() || c == '_' {
            let start = i;
            while i < chars.len() && (chars[i].is_alphanumeric() || chars[i] == '_') {
                i += 1;
            }
            out.push(Token { tok: Tok::Ident(chars[start..i].iter().collect()), pos });
        } else if c == '\'' && chars.get(i + 1).is_some_and(|c| c.is_alphabetic()) {
            let start = i + 1;
            i += 1;
            while i < chars.len() && (chars[i].is_alphanumeric() || chars[i] == '_') {
                i += 1;
            }
            out.push(Token { tok: Tok::Tick(chars[start..i].iter().collect()), pos });
        } else if c == '"' {
            i += 1;
            let mut s = String::new();
            loop {
                match chars.get(i) {
                    None | Some('\n') => return Err((pos, "a string that isn't closed".into())),
                    Some('"') => break,
                    Some('\\') => {
                        s.push(match chars.get(i + 1) {
                            Some('n') => '\n',
                            Some('t') => '\t',
                            Some('0') => '\0',
                            Some(&c) => c,
                            None => '\\',
                        });
                        i += 2;
                    }
                    Some(&c) => {
                        s.push(c);
                        i += 1;
                    }
                }
            }
            i += 1;
            out.push(Token { tok: Tok::Str(s), pos });
        } else {
            // (as many characters as the longest symbol has)
            let rest: String = chars[i..chars.len().min(i + 3)].iter().collect();
            let Some(sym) = SYMBOLS.iter().find(|s| rest.starts_with(**s)) else {
                return Err((pos, format!("unexpected {c:?}")));
            };
            i += sym.len();
            out.push(Token { tok: Tok::Sym(sym), pos });
        }
    }
    pos.col = i - line_start + 1;
    out.push(Token { tok: Tok::Eof, pos });
    Ok(out)
}
