//! Text into tokens: numbers, names, strings and symbols, each with its line
//! for error messages. `//` starts a comment.

#[derive(Clone, Debug, PartialEq)]
pub enum Tok {
    Int(i64),
    Ident(String),
    Str(String),
    Sym(&'static str),
    Eof,
}

pub struct Token {
    pub tok: Tok,
    pub line: usize,
}

// (longest first, so `<=` isn't read as `<` then `=`)
const SYMBOLS: [&str; 26] = ["==", "!=", "<=", ">=", "&&", "||", "(", ")", "{", "}", "[", "]", ",", ";", "=", "+", "-", "*", "/", "%", "<", ">", "!", "&", ".", ":"];

pub fn lex(src: &str) -> Result<Vec<Token>, String> {
    let chars: Vec<char> = src.chars().collect();
    let (mut i, mut line) = (0, 1);
    let mut out = vec![];
    while i < chars.len() {
        let c = chars[i];
        if c == '\n' {
            line += 1;
            i += 1;
        } else if c.is_whitespace() {
            i += 1;
        } else if c == '/' && chars.get(i + 1) == Some(&'/') {
            while i < chars.len() && chars[i] != '\n' {
                i += 1;
            }
        } else if c.is_ascii_digit() {
            let start = i;
            while i < chars.len() && chars[i].is_ascii_digit() {
                i += 1;
            }
            let text: String = chars[start..i].iter().collect();
            let n = text.parse().map_err(|_| format!("{line}: {text} is too big"))?;
            out.push(Token { tok: Tok::Int(n), line });
        } else if c.is_alphabetic() || c == '_' {
            let start = i;
            while i < chars.len() && (chars[i].is_alphanumeric() || chars[i] == '_') {
                i += 1;
            }
            out.push(Token { tok: Tok::Ident(chars[start..i].iter().collect()), line });
        } else if c == '"' {
            i += 1;
            let mut s = String::new();
            loop {
                match chars.get(i) {
                    None | Some('\n') => return Err(format!("{line}: a string that isn't closed")),
                    Some('"') => break,
                    Some('\\') => {
                        s.push(match chars.get(i + 1) {
                            Some('n') => '\n',
                            Some('t') => '\t',
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
            out.push(Token { tok: Tok::Str(s), line });
        } else {
            let rest: String = chars[i..chars.len().min(i + 2)].iter().collect();
            let Some(sym) = SYMBOLS.iter().find(|s| rest.starts_with(**s)) else {
                return Err(format!("{line}: unexpected {c:?}"));
            };
            i += sym.len();
            out.push(Token { tok: Tok::Sym(sym), line });
        }
    }
    out.push(Token { tok: Tok::Eof, line });
    Ok(out)
}
