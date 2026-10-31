//! The compiler never panics, whatever it's given: an error message is the
//! worst a program gets. Checked on the samples changed at random (bits cut
//! out, symbols and keywords put in, lines repeated and dropped), which
//! makes programs broken in every way the compiler has to say something
//! about.

use std::panic;

struct Rng(u64);

impl Rng {
    fn next(&mut self) -> u64 {
        self.0 ^= self.0 << 13;
        self.0 ^= self.0 >> 7;
        self.0 ^= self.0 << 17;
        self.0
    }

    fn below(&mut self, n: usize) -> usize {
        (self.next() % n.max(1) as u64) as usize
    }
}

const BITS: &[&str] = &[
    "(", ")", "{", "}", "[", "]", "<", ">", ";", ":", ",", ".", "=", "+", "-", "*", "/", "%", "!", "&", "|", "^", "#", "'", "\"", "fn", "let", "mut", "match", "if", "else", "while", "->",
    "=>", "::", "handle", "with", "impl", "struct", "enum", "trait", "0", "x", "Int", "Self",
];

/// `src`, changed one to three times.
fn mutate(src: &str, rng: &mut Rng) -> String {
    let mut src: Vec<char> = src.chars().collect();
    for _ in 0..1 + rng.below(3) {
        if src.is_empty() {
            break;
        }
        let at = rng.below(src.len());
        match rng.below(4) {
            0 => {
                let end = (at + 1 + rng.below(8)).min(src.len());
                src.drain(at..end);
            }
            1 => {
                let bit = BITS[rng.below(BITS.len())];
                src.splice(at..at, bit.chars());
            }
            k => {
                let text: String = src.iter().collect();
                let mut lines: Vec<&str> = text.split('\n').collect();
                let line = rng.below(lines.len());
                if k == 2 {
                    let copy = lines[rng.below(lines.len())];
                    lines.insert(line, copy);
                } else {
                    lines.remove(line);
                }
                src = lines.join("\n").chars().collect();
            }
        }
    }
    src.into_iter().collect()
}

#[test]
fn broken_programs_get_errors_not_panics() {
    let samples = concat!(env!("CARGO_MANIFEST_DIR"), "/samples");
    let mut sources: Vec<String> = std::fs::read_dir(samples).unwrap().filter_map(|e| e.ok()).map(|e| e.path()).filter(|p| p.extension().is_some_and(|x| x == "fern")).map(|p| std::fs::read_to_string(p).unwrap()).collect();
    sources.sort();
    let count: usize = std::env::var("MUTANTS").ok().and_then(|n| n.parse().ok()).unwrap_or(1000);
    let dir = std::env::temp_dir().join(format!("fern-mutants-{}", std::process::id()));
    std::fs::create_dir_all(&dir).unwrap();
    let mut rng = Rng(0x9e3779b97f4a7c15);
    // (the panics are what's being looked for: not their messages)
    panic::set_hook(Box::new(|_| {}));
    let mut panics = vec![];
    for i in 0..count {
        let src = mutate(&sources[rng.below(sources.len())], &mut rng);
        let path = dir.join(format!("m{i}.fern"));
        std::fs::write(&path, &src).unwrap();
        let p = path.display().to_string();
        if panic::catch_unwind(|| {
            let _ = fern::compile(&p);
        })
        .is_err()
        {
            panics.push(p);
        } else {
            let _ = std::fs::remove_file(&path);
        }
    }
    let _ = panic::take_hook();
    if panics.is_empty() {
        let _ = std::fs::remove_dir_all(&dir);
    }
    assert!(panics.is_empty(), "the compiler panicked on {} of {count} programs (kept): {panics:?}", panics.len());
}
