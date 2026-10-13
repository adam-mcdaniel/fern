//! A backend that turns a module into LLVM IR, for LLVM to optimize and
//! compile to native code, in place of the VM.
//!
//! Every value is an `i64`, as a 64-bit cell is, and means the same as it
//! does in the interpreter on 64-bit cells: the operations whose LLVM
//! instructions are undefined somewhere (dividing by 0, shifting too far)
//! are guarded to give what [`fold`](super::fold) says. Addresses are
//! native addresses, held as integers; `index` moves them by whole cells.
//! Block parameters become phi nodes, and every edge that passes arguments
//! gets a block of its own, so each phi's incoming edges are distinct.
//!
//! `gc_alloc` calls a garbage collector, [`RUNTIME`], which is C: compile it
//! with the module (`clang module.ll runtime.c`). `heap_alloc` uses `calloc`,
//! I/O uses the C library, and `abort` calls `exit`.

/// The C runtime that native code from [`emit`] needs: the garbage
/// collector behind `gc_alloc`.
pub const RUNTIME: &str = include_str!("llvm_runtime.c");

/// clang's flags for compiling what [`emit`] (or `asm::llvm::emit`, or the C
/// backend) makes: `-O3`, with link-time optimization across the program,
/// its runtime and whatever C it calls, code for the machine it's built
/// on, more inlining, and LLVM's optional passes that help this kind of
/// code (jump threading through dispatch loops, hoisting and sinking common
/// code, versioning loops for LICM). `-fwrapv` is for the C backend's code,
/// whose arithmetic has to wrap around as the VM's does.
pub const OPTIMIZE: &[&str] = &[
    "-O3",
    "-flto",
    #[cfg(target_arch = "aarch64")]
    "-mcpu=native",
    #[cfg(not(target_arch = "aarch64"))]
    "-march=native",
    "-fwrapv",
    "-fomit-frame-pointer",
    "-fno-stack-protector",
    "-fno-semantic-interposition",
    "-fno-plt",
    "-mllvm",
    "-inline-threshold=4000",
    "-mllvm",
    "-enable-gvn-hoist",
    "-mllvm",
    "-enable-gvn-sink",
    "-mllvm",
    "-enable-loop-versioning-licm",
    "-mllvm",
    "-enable-dfa-jump-thread",
    "-mllvm",
    "-enable-unroll-and-jam",
];

use super::{cfg, sched, BinOp, Block, Function, Module, Node, Target, Terminator, UnOp, Value};
use std::collections::HashMap;
use std::fmt::Write;

/// The module, as an LLVM IR file with a `main` that runs it.
pub fn emit(module: &Module) -> Result<String, String> {
    super::verify(module)?;
    let mut strings: Vec<String> = vec![];
    let mut body = String::new();
    for f in &module.funcs {
        Emitter { f, out: String::new(), strings: &mut strings, fresh: 0, edges: vec![], entry_phis: false }.function(&mut body)?;
    }
    let mut out = String::new();
    out += "; generated from the IR\n\n";
    out += "declare i32 @putchar(i32)\ndeclare i32 @getchar()\ndeclare i32 @printf(ptr, ...)\n";
    out += "declare ptr @calloc(i64, i64)\ndeclare void @exit(i32)\n";
    out += "declare i64 @llvm.smax.i64(i64, i64)\ndeclare i64 @llvm.smin.i64(i64, i64)\n";
    out += "declare i64 @rt_alloc(i64)\ndeclare void @rt_init(ptr, ptr, i64)\n";
    // external functions are C's, called as the VM calls them
    out += "declare ptr @llvm.stacksave.p0()\ndeclare void @llvm.stackrestore.p0(ptr)\n";
    for name in module.externals() {
        let _ = writeln!(out, "declare void @{name}(ptr, ptr, ptr)");
    }
    out += "\n";
    let globals = module.globals.max(1);
    let _ = writeln!(out, "@globals = global [{globals} x i64] zeroinitializer");
    // what an external function gets as the tape: there's none, so the
    // global cells
    out += "@tape = global ptr @globals\n";
    out += "@fmt.d = private constant [5 x i8] c\"%lld\\00\"\n@fmt.u = private constant [5 x i8] c\"%llu\\00\"\n";
    out += "@fmt.s = private constant [3 x i8] c\"%s\\00\"\n";
    for (i, s) in strings.iter().enumerate() {
        let _ = writeln!(out, "@str.{i} = private constant [{} x i8] c\"{}\\00\"", s.len() + 1, escape(s));
    }
    out += "\n";
    out += GETINT;
    out += &body;
    // the collector's roots are the stack below main, and the globals
    let _ = write!(
        out,
        "\ndefine i32 @main() {{\n  %bottom = alloca i64\n  call void @rt_init(ptr %bottom, ptr @globals, i64 {globals})\n  call i64 @f_main()\n  ret i32 0\n}}\n"
    );
    Ok(out)
}

/// Reads a number the way `asm::getint` does: skips characters 1 to 32,
/// takes a `-`, then digits, consuming the character after them.
const GETINT: &str = r#"define private i64 @rt_getint() {
entry:
  br label %skip
skip:
  %c0 = call i32 @getchar()
  %c = sext i32 %c0 to i64
  %ws1 = icmp sge i64 %c, 1
  %ws2 = icmp sle i64 %c, 32
  %ws = and i1 %ws1, %ws2
  br i1 %ws, label %skip, label %sign
sign:
  %neg = icmp eq i64 %c, 45
  br i1 %neg, label %after_sign, label %digits
after_sign:
  %c1_ = call i32 @getchar()
  %c1 = sext i32 %c1_ to i64
  br label %digits
digits:
  %first = phi i64 [ %c, %sign ], [ %c1, %after_sign ]
  br label %loop
loop:
  %d = phi i64 [ %first, %digits ], [ %next, %body ]
  %n = phi i64 [ 0, %digits ], [ %n2, %body ]
  %isd1 = icmp sge i64 %d, 48
  %isd2 = icmp sle i64 %d, 57
  %isd = and i1 %isd1, %isd2
  br i1 %isd, label %body, label %done
body:
  %m = mul i64 %n, 10
  %dv = sub i64 %d, 48
  %n2 = add i64 %m, %dv
  %next_ = call i32 @getchar()
  %next = sext i32 %next_ to i64
  br label %loop
done:
  %minus = sub i64 0, %n
  %r = select i1 %neg, i64 %minus, i64 %n
  ret i64 %r
}
"#;

fn escape(s: &str) -> String {
    s.bytes().map(|b| if b.is_ascii_graphic() && b != b'"' && b != b'\\' || b == b' ' { (b as char).to_string() } else { format!("\\{b:02X}") }).collect()
}

struct Emitter<'a> {
    f: &'a Function,
    out: String,
    strings: &'a mut Vec<String>,
    fresh: usize,
    /// The edge blocks to add after the function's blocks: their label, the
    /// block they lead to.
    edges: Vec<(String, Block)>,
    /// Whether the entry block is jumped back to, so its parameters are phis
    /// rather than the function's arguments.
    entry_phis: bool,
}

impl Emitter<'_> {
    fn tmp(&mut self) -> String {
        self.fresh += 1;
        format!("%t{}", self.fresh)
    }

    /// A value as an operand.
    fn val(&self, v: Value) -> String {
        match self.f.values[v.index()].node {
            Node::Const(k) => k.to_string(),
            Node::Param(b, i) if b == self.f.entry() && !self.entry_phis => format!("%a{i}"),
            _ => format!("%v{}", v.index()),
        }
    }

    fn line(&mut self, s: &str) {
        self.out += "  ";
        self.out += s;
        self.out += "\n";
    }

    fn function(mut self, body: &mut String) -> Result<(), String> {
        let f = self.f;
        let params: Vec<String> = (0..f.param_count()).map(|i| format!("i64 %a{i}")).collect();
        let _ = writeln!(self.out, "define internal i64 @f_{}({}) {{", f.name(), params.join(", "));
        let blocks = cfg::reverse_postorder(f);
        self.entry_phis = blocks
            .iter()
            .any(|&b| f.blocks[b.index()].term.iter().flat_map(|t| t.targets()).any(|t| t.block == f.entry()));
        let needed = sched::needed(f, &blocks);
        let outside = sched::used_outside(f, &blocks, &needed);
        let pinned = f.pinned();
        // allocas go at the start, since each one is the same cells for the
        // whole call
        self.out += "start:\n";
        for &b in &blocks {
            for &e in &f.blocks[b.index()].effects {
                if let Node::Alloca(cells) = f.values[e.index()].node {
                    let t = self.tmp();
                    self.line(&format!("{t} = alloca i64, i64 {}", cells.max(1)));
                    self.line(&format!("%v{} = ptrtoint ptr {t} to i64", e.index()));
                }
            }
        }
        self.line(&format!("br label %b{}", f.entry().index()));
        // the phis each block needs: (param value, (incoming value, from));
        // the entry's start with the function's arguments
        let mut phis: HashMap<Block, Vec<Vec<(String, String)>>> = HashMap::new();
        if self.entry_phis {
            phis.insert(f.entry(), (0..f.param_count()).map(|i| vec![(format!("%a{i}"), "start".to_string())]).collect());
        }
        let mut edge_count = 0;
        let mut terms: HashMap<Block, String> = HashMap::new();
        for &b in &blocks {
            let Some(term) = &f.blocks[b.index()].term else { return Err(format!("{b} has no terminator")) };
            let mut target = |t: &Target, me: &mut Self| -> String {
                if t.args.is_empty() {
                    return format!("%b{}", t.block.index());
                }
                edge_count += 1;
                let label = format!("e{edge_count}");
                let entry = phis.entry(t.block).or_insert_with(|| vec![vec![]; t.args.len()]);
                for (i, &a) in t.args.iter().enumerate() {
                    entry[i].push((me.val(a), label.clone()));
                }
                me.edges.push((label.clone(), t.block));
                format!("%{label}")
            };
            let text = match term {
                Terminator::Jump(t) => format!("br label {}", target(t, &mut self)),
                Terminator::Branch(c, t, e) => {
                    let (lt, le) = (target(t, &mut self), target(e, &mut self));
                    format!("!branch {} {lt} {le}", self.val(*c))
                }
                Terminator::Return(Some(v)) => format!("ret i64 {}", self.val(*v)),
                Terminator::Return(None) => "ret i64 0".to_string(),
            };
            terms.insert(b, text);
        }
        // the entry's parameters are the function's, and the entry is
        // reached from `start`
        for &b in &blocks {
            let _ = writeln!(self.out, "b{}:", b.index());
            if let Some(list) = phis.get(&b) {
                for (i, incoming) in list.iter().enumerate() {
                    let p = f.blocks[b.index()].params[i];
                    let parts: Vec<String> = incoming.iter().map(|(v, from)| format!("[ {v}, %{from} ]")).collect();
                    self.line(&format!("%v{} = phi i64 {}", p.index(), parts.join(", ")));
                }
            }
            let mut stopped = false;
            for v in sched::schedule(f, b, &needed, &outside, &pinned[b.index()]) {
                if self.node(v)? {
                    stopped = true;
                    break;
                }
            }
            if stopped {
                continue;
            }
            let text = terms[&b].clone();
            if let Some(rest) = text.strip_prefix("!branch ") {
                let mut parts = rest.split(' ');
                let (c, t, e) = (parts.next().unwrap(), parts.next().unwrap(), parts.next().unwrap());
                let flag = self.tmp();
                self.line(&format!("{flag} = icmp ne i64 {c}, 0"));
                self.line(&format!("br i1 {flag}, label {t}, label {e}"));
            } else {
                self.line(&text);
            }
        }
        for (label, to) in std::mem::take(&mut self.edges) {
            let _ = writeln!(self.out, "{label}:");
            self.line(&format!("br label %b{}", to.index()));
        }
        self.out += "}\n\n";
        body.push_str(&self.out);
        Ok(())
    }

    /// Emits a node; true if it ends the block (an abort).
    fn node(&mut self, v: Value) -> Result<bool, String> {
        let d = format!("%v{}", v.index());
        let node = self.f.values[v.index()].node.clone();
        match node {
            Node::Const(_) | Node::Param(..) => {}
            Node::Unary(op, a) => {
                let a = self.val(a);
                match op {
                    UnOp::Neg => self.line(&format!("{d} = sub i64 0, {a}")),
                    UnOp::Not => self.line(&format!("{d} = xor i64 {a}, -1")),
                    UnOp::LNot => {
                        let t = self.tmp();
                        self.line(&format!("{t} = icmp eq i64 {a}, 0"));
                        self.line(&format!("{d} = zext i1 {t} to i64"));
                    }
                    UnOp::Abs => {
                        let (t, n) = (self.tmp(), self.tmp());
                        self.line(&format!("{t} = icmp slt i64 {a}, 0"));
                        self.line(&format!("{n} = sub i64 0, {a}"));
                        self.line(&format!("{d} = select i1 {t}, i64 {n}, i64 {a}"));
                    }
                }
            }
            Node::Binary(op, a, b) => self.binary(&d, op, a, b),
            Node::FuncAddr(name) => self.line(&format!("{d} = ptrtoint ptr @f_{name} to i64")),
            Node::GlobalAddr(i) => {
                let t = self.tmp();
                self.line(&format!("{t} = getelementptr i64, ptr @globals, i64 {i}"));
                self.line(&format!("{d} = ptrtoint ptr {t} to i64"));
            }
            Node::Load(a) => {
                let p = self.tmp();
                let a = self.val(a);
                self.line(&format!("{p} = inttoptr i64 {a} to ptr"));
                self.line(&format!("{d} = load i64, ptr {p}"));
            }
            Node::Store(a, x) => {
                let p = self.tmp();
                let (a, x) = (self.val(a), self.val(x));
                self.line(&format!("{p} = inttoptr i64 {a} to ptr"));
                self.line(&format!("store i64 {x}, ptr {p}"));
            }
            Node::Call(name, args) => {
                let args: Vec<String> = args.iter().map(|&a| format!("i64 {}", self.val(a))).collect();
                self.line(&format!("{d} = call i64 @f_{name}({})", args.join(", ")));
            }
            // as the VM calls one: `void name(ptr tape, ptr ptr, ptr acc)`,
            // with the arguments in cells next to each other and the
            // pointer at the first, and acc holding the function's address;
            // its result is what it leaves in acc
            Node::CallExtern(name, args) => {
                let values: Vec<String> = args.iter().map(|&a| self.val(a)).collect();
                let (saved, cells, at, acc) = (self.tmp(), self.tmp(), self.tmp(), self.tmp());
                self.line(&format!("{saved} = call ptr @llvm.stacksave.p0()"));
                self.line(&format!("{cells} = alloca [{} x i64]", values.len().max(1)));
                for (i, x) in values.iter().enumerate() {
                    let slot = self.tmp();
                    self.line(&format!("{slot} = getelementptr i64, ptr {cells}, i64 {i}"));
                    self.line(&format!("store i64 {x}, ptr {slot}"));
                }
                self.line(&format!("{at} = alloca ptr"));
                self.line(&format!("store ptr {cells}, ptr {at}"));
                self.line(&format!("{acc} = alloca i64"));
                self.line(&format!("store i64 ptrtoint (ptr @{name} to i64), ptr {acc}"));
                self.line(&format!("call void @{name}(ptr @tape, ptr {at}, ptr {acc})"));
                self.line(&format!("{d} = load i64, ptr {acc}"));
                self.line(&format!("call void @llvm.stackrestore.p0(ptr {saved})"));
            }
            Node::CallIndirect(g, args) => {
                let p = self.tmp();
                let g = self.val(g);
                self.line(&format!("{p} = inttoptr i64 {g} to ptr"));
                let args: Vec<String> = args.iter().map(|&a| format!("i64 {}", self.val(a))).collect();
                self.line(&format!("{d} = call i64 {p}({})", args.join(", ")));
            }
            Node::GetChar => {
                let t = self.tmp();
                self.line(&format!("{t} = call i32 @getchar()"));
                self.line(&format!("{d} = sext i32 {t} to i64"));
            }
            Node::GetInt => self.line(&format!("{d} = call i64 @rt_getint()")),
            Node::PutChar(x) => {
                let t = self.tmp();
                let x = self.val(x);
                self.line(&format!("{t} = trunc i64 {x} to i32"));
                self.line(&format!("call i32 @putchar(i32 {t})"));
            }
            Node::PutInt(x) => {
                let x = self.val(x);
                self.line(&format!("call i32 (ptr, ...) @printf(ptr @fmt.d, i64 {x})"));
            }
            Node::PutUInt(x) => {
                let x = self.val(x);
                self.line(&format!("call i32 (ptr, ...) @printf(ptr @fmt.u, i64 {x})"));
            }
            Node::Puts(s) => {
                let i = match self.strings.iter().position(|t| *t == s) {
                    Some(i) => i,
                    None => {
                        self.strings.push(s.clone());
                        self.strings.len() - 1
                    }
                };
                self.line(&format!("call i32 (ptr, ...) @printf(ptr @fmt.s, ptr @str.{i})"));
            }
            Node::GcAlloc(n) => {
                let n = self.val(n);
                self.line(&format!("{d} = call i64 @rt_alloc(i64 {n})"));
            }
            Node::HeapAlloc(n) => {
                let (m, p) = (self.tmp(), self.tmp());
                let n = self.val(n);
                self.line(&format!("{m} = call i64 @llvm.smax.i64(i64 {n}, i64 1)"));
                self.line(&format!("{p} = call ptr @calloc(i64 {m}, i64 8)"));
                self.line(&format!("{d} = ptrtoint ptr {p} to i64"));
            }
            Node::Alloca(_) => {}
            Node::Abort => {
                self.line("call void @exit(i32 0)");
                self.line("unreachable");
                return Ok(true);
            }
            Node::Intrinsic(which, _) => return Err(format!("{} is only for the VM's runtime", which.name())),
        }
        Ok(false)
    }

    fn binary(&mut self, d: &str, op: BinOp, a: Value, b: Value) {
        use BinOp::*;
        let (a, b) = (self.val(a), self.val(b));
        let simple = |op: &str| format!("{d} = {op} i64 {a}, {b}");
        let compare = |me: &mut Self, cond: &str| {
            let t = me.tmp();
            me.line(&format!("{t} = icmp {cond} i64 {a}, {b}"));
            me.line(&format!("{d} = zext i1 {t} to i64"));
        };
        match op {
            Add => self.line(&simple("add")),
            Sub => self.line(&simple("sub")),
            Mul => self.line(&simple("mul")),
            And => self.line(&simple("and")),
            Or => self.line(&simple("or")),
            Xor => self.line(&simple("xor")),
            // dividing by 0 gives -1 (and a remainder of the dividend), and
            // the most negative number by -1 wraps: the divisor becomes 1 for
            // both, which LLVM can divide by
            Div | Rem | DivU | RemU => {
                let (zero, safe, q) = (self.tmp(), self.tmp(), self.tmp());
                self.line(&format!("{zero} = icmp eq i64 {b}, 0"));
                let divisor = if matches!(op, Div | Rem) {
                    let (min, minus, ovf, s0) = (self.tmp(), self.tmp(), self.tmp(), self.tmp());
                    self.line(&format!("{min} = icmp eq i64 {a}, -9223372036854775808"));
                    self.line(&format!("{minus} = icmp eq i64 {b}, -1"));
                    self.line(&format!("{ovf} = and i1 {min}, {minus}"));
                    self.line(&format!("{s0} = or i1 {zero}, {ovf}"));
                    s0
                } else {
                    zero.clone()
                };
                self.line(&format!("{safe} = select i1 {divisor}, i64 1, i64 {b}"));
                let inst = match op {
                    Div => "sdiv",
                    Rem => "srem",
                    DivU => "udiv",
                    _ => "urem",
                };
                self.line(&format!("{q} = {inst} i64 {a}, {safe}"));
                let by_zero = if matches!(op, Div | DivU) { "-1".to_string() } else { a.clone() };
                self.line(&format!("{d} = select i1 {zero}, i64 {by_zero}, i64 {q}"));
            }
            Shl | Shr | ShrU => {
                let (none, far, amount, shifted, t) = (self.tmp(), self.tmp(), self.tmp(), self.tmp(), self.tmp());
                self.line(&format!("{none} = icmp sle i64 {b}, 0"));
                self.line(&format!("{far} = icmp sge i64 {b}, 64"));
                self.line(&format!("{amount} = call i64 @llvm.smin.i64(i64 {b}, i64 63)"));
                let inst = match op {
                    Shl => "shl",
                    Shr => "ashr",
                    _ => "lshr",
                };
                self.line(&format!("{shifted} = {inst} i64 {a}, {amount}"));
                // past the width: 0, except an arithmetic shift, which
                // keeps the sign (as shifting by 63 does)
                let past = if op == Shr { shifted.clone() } else { "0".to_string() };
                self.line(&format!("{t} = select i1 {far}, i64 {past}, i64 {shifted}"));
                self.line(&format!("{d} = select i1 {none}, i64 {a}, i64 {t}"));
            }
            Eq => compare(self, "eq"),
            Ne => compare(self, "ne"),
            Lt => compare(self, "slt"),
            Le => compare(self, "sle"),
            Gt => compare(self, "sgt"),
            Ge => compare(self, "sge"),
            LtU => compare(self, "ult"),
            LeU => compare(self, "ule"),
            GtU => compare(self, "ugt"),
            GeU => compare(self, "uge"),
            Min => self.line(&format!("{d} = call i64 @llvm.smin.i64(i64 {a}, i64 {b})")),
            Max => self.line(&format!("{d} = call i64 @llvm.smax.i64(i64 {a}, i64 {b})")),
            Index => {
                let (p, q) = (self.tmp(), self.tmp());
                self.line(&format!("{p} = inttoptr i64 {a} to ptr"));
                self.line(&format!("{q} = getelementptr i64, ptr {p}, i64 {b}"));
                self.line(&format!("{d} = ptrtoint ptr {q} to i64"));
            }
        }
    }
}
