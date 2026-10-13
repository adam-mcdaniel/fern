//! Turns a VM program into LLVM IR, the way `bf::compile` turns one into C,
//! so that LLVM can optimize what the compilers here produce, and compile it
//! to native code.
//!
//! The tape is a global array, and the accumulator, the tape pointer and
//! the pointer stack's top are globals too, which every function shares, as
//! the VM's do. Inside a function they're kept in locals that LLVM can put
//! in registers, and written back to the globals around calls and at the
//! end. A call is a call through the function pointer in the accumulator;
//! once LLVM sees which function that is, it's a direct call.
//!
//! As in the C backend, every function gets pointers to the tape's start,
//! the tape pointer and the accumulator, so a label the program doesn't
//! define is a C function `void name(int64_t **tape, int64_t **ptr,
//! int64_t *acc)` to link with: a module's external functions.

use crate::Op;
use std::fmt::Write;

/// The program as an LLVM IR file, for a tape of `cells` cells.
pub fn emit(ops: &[Op], cells: u64) -> String {
    // the labels the program defines; the rest are external
    let mut defined = std::collections::HashSet::new();
    for w in ops.windows(2) {
        if let (Op::Label(name), Op::Func) = (&w[0], &w[1]) {
            defined.insert(label(name));
        }
    }
    let mut external = std::collections::BTreeSet::new();
    let mut funcs: Vec<String> = vec![];
    let mut main = Body::new("main");
    let mut current: Option<Body> = None;
    let mut pending_label: Option<String> = None;
    for op in ops {
        if let Op::Label(name) = op {
            pending_label = Some(label(name));
            continue;
        }
        if let Op::Func = op {
            current = Some(Body::new(&pending_label.take().expect("a function has a label")));
            continue;
        }
        let body = current.as_mut().unwrap_or(&mut main);
        // a label not starting a function puts its address in acc
        if let Some(name) = pending_label.take() {
            if defined.contains(&name) {
                body.set_acc(&format!("ptrtoint ptr @vm_{name} to i64"));
            } else {
                body.set_acc(&format!("ptrtoint ptr @{name} to i64"));
                external.insert(name);
            }
        }
        match op {
            Op::EndFunc => {
                funcs.push(current.take().expect("matched by the parser").finish(false));
            }
            op => body.op(op),
        }
    }
    let mut out = String::new();
    out += "; generated from VM ops\n\n";
    out += "declare i32 @putchar(i32)\ndeclare i32 @getchar()\n\n";
    let _ = writeln!(out, "@tape = global [{cells} x i64] zeroinitializer");
    out += "@acc = global i64 0\n@ptr = global ptr @tape\n@tapebase = global ptr @tape\n";
    out += "@stack = global [4096 x ptr] zeroinitializer\n@top = global i64 0\n\n";
    for name in external {
        let _ = writeln!(out, "declare void @{name}(ptr, ptr, ptr)");
    }
    for f in funcs {
        out += &f;
    }
    out += &main.finish(true);
    out
}

fn label(name: &[u8; 16]) -> String {
    name.iter().take_while(|&&c| c != 0).map(|&c| c as char).collect()
}

/// A function's code, being built.
struct Body {
    name: String,
    text: String,
    fresh: usize,
    /// The labels of the loops being built: their head and their exit.
    loops: Vec<(String, String)>,
}

impl Body {
    fn new(name: &str) -> Body {
        let mut b = Body { name: name.to_string(), text: String::new(), fresh: 0, loops: vec![] };
        b.text += "entry:\n";
        b.line("%acc = alloca i64");
        b.line("%ptr = alloca ptr");
        b.line("%top = alloca i64");
        b.load_globals();
        b
    }

    fn tmp(&mut self) -> String {
        self.fresh += 1;
        format!("%t{}", self.fresh)
    }

    fn line(&mut self, s: &str) {
        self.text += "  ";
        self.text += s;
        self.text += "\n";
    }

    fn load_globals(&mut self) {
        for (g, ty) in [("acc", "i64"), ("ptr", "ptr"), ("top", "i64")] {
            let t = self.tmp();
            self.line(&format!("{t} = load {ty}, ptr @{g}"));
            self.line(&format!("store {ty} {t}, ptr %{g}"));
        }
    }

    fn store_globals(&mut self) {
        for (g, ty) in [("acc", "i64"), ("ptr", "ptr"), ("top", "i64")] {
            let t = self.tmp();
            self.line(&format!("{t} = load {ty}, ptr %{g}"));
            self.line(&format!("store {ty} {t}, ptr @{g}"));
        }
    }

    fn acc(&mut self) -> String {
        let t = self.tmp();
        self.line(&format!("{t} = load i64, ptr %acc"));
        t
    }

    fn set_acc(&mut self, value: &str) {
        let t = self.tmp();
        self.line(&format!("{t} = {value}"));
        self.line(&format!("store i64 {t}, ptr %acc"));
    }

    fn ptr(&mut self) -> String {
        let t = self.tmp();
        self.line(&format!("{t} = load ptr, ptr %ptr"));
        t
    }

    fn op(&mut self, op: &Op) {
        match op {
            Op::Deref => {
                let (p, top) = (self.ptr(), self.tmp());
                self.line(&format!("{top} = load i64, ptr %top"));
                let slot = self.tmp();
                self.line(&format!("{slot} = getelementptr ptr, ptr @stack, i64 {top}"));
                self.line(&format!("store ptr {p}, ptr {slot}"));
                let next = self.tmp();
                self.line(&format!("{next} = add i64 {top}, 1"));
                self.line(&format!("store i64 {next}, ptr %top"));
                let (v, q) = (self.tmp(), self.tmp());
                self.line(&format!("{v} = load i64, ptr {p}"));
                self.line(&format!("{q} = inttoptr i64 {v} to ptr"));
                self.line(&format!("store ptr {q}, ptr %ptr"));
            }
            Op::Refer => {
                let (top, prev, slot, p) = (self.tmp(), self.tmp(), self.tmp(), self.tmp());
                self.line(&format!("{top} = load i64, ptr %top"));
                self.line(&format!("{prev} = sub i64 {top}, 1"));
                self.line(&format!("store i64 {prev}, ptr %top"));
                self.line(&format!("{slot} = getelementptr ptr, ptr @stack, i64 {prev}"));
                self.line(&format!("{p} = load ptr, ptr {slot}"));
                self.line(&format!("store ptr {p}, ptr %ptr"));
            }
            Op::Where => {
                let p = self.ptr();
                self.set_acc(&format!("ptrtoint ptr {p} to i64"));
            }
            Op::Move(n) => {
                let (p, q) = (self.ptr(), self.tmp());
                self.line(&format!("{q} = getelementptr i64, ptr {p}, i64 {n}"));
                self.line(&format!("store ptr {q}, ptr %ptr"));
            }
            Op::Set(n) => self.set_acc(&format!("add i64 0, {}", *n as i64)),
            Op::Label(_) | Op::Func | Op::EndFunc => unreachable!("handled by emit"),
            Op::Load => {
                let p = self.ptr();
                self.set_acc(&format!("load i64, ptr {p}"));
            }
            Op::Store => {
                let (p, a) = (self.ptr(), self.acc());
                self.line(&format!("store i64 {a}, ptr {p}"));
            }
            Op::Add => {
                let (p, a, x) = (self.ptr(), self.acc(), self.tmp());
                self.line(&format!("{x} = load i64, ptr {p}"));
                self.set_acc(&format!("add i64 {a}, {x}"));
            }
            Op::Neg => {
                let a = self.acc();
                self.set_acc(&format!("sub i64 0, {a}"));
            }
            Op::Positive => {
                let (a, c) = (self.acc(), self.tmp());
                self.line(&format!("{c} = icmp sgt i64 {a}, 0"));
                self.set_acc(&format!("zext i1 {c} to i64"));
            }
            Op::Call => {
                let a = self.acc();
                self.store_globals();
                let f = self.tmp();
                self.line(&format!("{f} = inttoptr i64 {a} to ptr"));
                self.line(&format!("call void {f}(ptr @tapebase, ptr @ptr, ptr @acc)"));
                self.load_globals();
            }
            Op::Read => {
                let c = self.tmp();
                self.line(&format!("{c} = call i32 @getchar()"));
                self.set_acc(&format!("sext i32 {c} to i64"));
            }
            Op::Write => {
                let (a, c) = (self.acc(), self.tmp());
                self.line(&format!("{c} = trunc i64 {a} to i32"));
                self.line(&format!("call i32 @putchar(i32 {c})"));
            }
            // `[` skips past its `]` if acc is 0, and `]` goes back to just
            // after its `[` unless acc is 0: a while loop
            Op::While => {
                self.fresh += 1;
                let (head, body, exit) = (format!("h{}", self.fresh), format!("w{}", self.fresh), format!("x{}", self.fresh));
                self.line(&format!("br label %{head}"));
                let _ = writeln!(self.text, "{head}:");
                let (a, c) = (self.acc(), self.tmp());
                self.line(&format!("{c} = icmp ne i64 {a}, 0"));
                self.line(&format!("br i1 {c}, label %{body}, label %{exit}"));
                let _ = writeln!(self.text, "{body}:");
                self.loops.push((head, exit));
            }
            Op::EndWhile => {
                let (head, exit) = self.loops.pop().expect("matched by the parser");
                self.line(&format!("br label %{head}"));
                let _ = writeln!(self.text, "{exit}:");
            }
        }
    }

    fn finish(mut self, main: bool) -> String {
        if main {
            self.line("ret i32 0");
            return format!("define i32 @main() {{\n{}}}\n", self.text);
        }
        self.store_globals();
        self.line("ret void");
        format!("define internal void @vm_{}(ptr %tape.arg, ptr %ptr.arg, ptr %acc.arg) {{\n{}}}\n\n", self.name, self.text)
    }
}
