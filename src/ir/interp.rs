//! Interpreting a module directly: the reference for what its lowered program
//! should do.

use super::{fold, verify, Function, Intrinsic, Module, Node, Terminator, Value};
use crate::interp::{HostCall, HostFn, Memory};
use std::collections::HashMap;

const MAX_STEPS: u64 = 200_000_000;
const MAX_DEPTH: usize = 10_000;

/// Runs `module` on `xlen`-bit cells (from the module's minimum width to 64),
/// with `input` as its input,
/// and returns its output. Addresses here are cell indices, so a program that
/// prints its addresses can print different ones once it's lowered.
pub fn run(module: &Module, input: &[u8], xlen: u32) -> Result<Vec<u8>, String> {
    run_with(module, input, xlen, &HashMap::new())
}

/// Like [`run`], with the module's external functions given as host
/// functions, by name.
pub fn run_with(module: &Module, input: &[u8], xlen: u32, externs: &HashMap<String, HostFn>) -> Result<Vec<u8>, String> {
    run_counting(module, input, xlen, externs).map(|(out, _)| out)
}

/// Like [`run_with`], also giving how many steps the program took: values
/// worked out, and effects and jumps done.
pub fn run_counting(module: &Module, input: &[u8], xlen: u32, externs: &HashMap<String, HostFn>) -> Result<(Vec<u8>, u64), String> {
    verify(module)?;
    for name in &module.externs {
        if !externs.contains_key(name) {
            return Err(format!("the external function {name} isn't given"));
        }
    }
    if !(module.min_width..=64).contains(&xlen) {
        return Err(format!("this module needs cells of {} to 64 bits, not {xlen}", module.min_width));
    }
    // keep addresses positive
    let cells = 1 << (xlen - 1).min(20);
    // the globals come first, after address 0
    let mut machine = Machine {
        module,
        xlen,
        memory: vec![0; cells],
        sp: 1 + module.globals as usize,
        hp: cells,
        input: input.to_vec(),
        read: 0,
        output: vec![],
        steps: 0,
        pinned: module.funcs.iter().map(|f| f.pinned()).collect(),
        externs,
    };
    match machine.call(0, vec![], 0) {
        Ok(_) | Err(Stop::Aborted) => Ok((machine.output, machine.steps)),
        Err(Stop::Error(e)) => Err(e),
    }
}

/// Why a call ended early.
enum Stop {
    /// The program aborted.
    Aborted,
    Error(String),
}

impl From<String> for Stop {
    fn from(e: String) -> Stop {
        Stop::Error(e)
    }
}

impl From<&str> for Stop {
    fn from(e: &str) -> Stop {
        Stop::Error(e.to_string())
    }
}

struct Machine<'a> {
    module: &'a Module,
    xlen: u32,
    memory: Vec<i64>,
    /// The next free cell for allocas, which grow up from the start.
    sp: usize,
    /// The lowest cell the heap has handed out; it grows down from the end.
    hp: usize,
    input: Vec<u8>,
    read: usize,
    output: Vec<u8>,
    steps: u64,
    pinned: Vec<Vec<Vec<Value>>>,
    externs: &'a HashMap<String, HostFn>,
}

/// The interpreter's memory, as a host function sees it: addresses are cell
/// indices.
struct Cells<'a>(&'a mut [i64]);

impl Memory for Cells<'_> {
    fn load(&self, addr: i64) -> Result<i64, String> {
        usize::try_from(addr).ok().and_then(|a| self.0.get(a).copied()).ok_or(format!("bad address {addr}"))
    }
    fn store(&mut self, addr: i64, value: i64) -> Result<(), String> {
        let cell = usize::try_from(addr).ok().and_then(|a| self.0.get_mut(a)).ok_or(format!("bad address {addr}"))?;
        *cell = value;
        Ok(())
    }
    fn index(&self, addr: i64, i: i64) -> i64 {
        addr.wrapping_add(i)
    }
}

type Env = HashMap<Value, i64>;

impl Machine<'_> {
    fn step(&mut self) -> Result<(), Stop> {
        self.steps += 1;
        if self.steps > MAX_STEPS {
            return Err("step limit reached".into());
        }
        Ok(())
    }

    fn call(&mut self, func: usize, args: Vec<i64>, depth: usize) -> Result<i64, Stop> {
        if depth > MAX_DEPTH {
            return Err("calls nested too deeply".into());
        }
        let module = self.module;
        let f = &module.funcs[func];
        let sp = self.sp;
        let mut env = Env::new();
        let mut block = f.entry();
        let mut args = args;
        loop {
            // entering a block computes its values afresh
            for v in &self.pinned[func][block.index()] {
                env.remove(v);
            }
            let data = &f.blocks[block.index()];
            for (&p, &a) in data.params.iter().zip(&args) {
                env.insert(p, a);
            }
            for &e in &data.effects {
                if let Some(x) = self.effect(f, e, &mut env, depth)? {
                    env.insert(e, x);
                }
            }
            let target = match data.term.as_ref().expect("verified") {
                Terminator::Return(v) => {
                    let x = match v {
                        Some(v) => self.eval(f, *v, &mut env)?,
                        None => 0,
                    };
                    self.sp = sp;
                    return Ok(x);
                }
                Terminator::Jump(t) => t,
                Terminator::Branch(c, t, e) => {
                    if self.eval(f, *c, &mut env)? != 0 {
                        t
                    } else {
                        e
                    }
                }
            };
            args = target.args.iter().map(|&a| self.eval(f, a, &mut env)).collect::<Result<_, _>>()?;
            block = target.block;
        }
    }

    fn eval(&mut self, f: &Function, v: Value, env: &mut Env) -> Result<i64, Stop> {
        if let Some(&x) = env.get(&v) {
            return Ok(x);
        }
        self.step()?;
        let x = match &f.values[v.index()].node {
            Node::Const(k) => return Ok(fold::wrap(*k, self.xlen)),
            Node::Unary(op, a) => {
                let a = self.eval(f, *a, env)?;
                fold::unary(*op, a, self.xlen)
            }
            Node::Binary(op, a, b) => {
                let a = self.eval(f, *a, env)?;
                let b = self.eval(f, *b, env)?;
                fold::binary(*op, a, b, self.xlen)
            }
            // a function's address here is its position, plus one so that
            // it's never 0
            Node::FuncAddr(name) => self.module.index_of(name).expect("verified") as i64 + 1,
            Node::GlobalAddr(i) => 1 + *i as i64,
            _ => return Err(format!("{v} is used before it's defined").into()),
        };
        env.insert(v, x);
        Ok(x)
    }

    fn address(&self, a: i64) -> Result<usize, Stop> {
        usize::try_from(a)
            .ok()
            .filter(|&a| a > 0 && a < self.memory.len())
            .ok_or_else(|| format!("bad address {a}").into())
    }

    fn read_byte(&mut self) -> i64 {
        let byte = self.input.get(self.read).map_or(-1, |&b| b as i64);
        self.read += 1;
        byte
    }

    /// Reads a number the way `asm::getint` does.
    fn read_int(&mut self) -> i64 {
        let mut c = self.read_byte();
        while (1..=32).contains(&c) {
            c = self.read_byte();
        }
        let negative = c == b'-' as i64;
        if negative {
            c = self.read_byte();
        }
        let mut n: i64 = 0;
        while (b'0' as i64..=b'9' as i64).contains(&c) {
            n = fold::wrap(n.wrapping_mul(10).wrapping_add(c - b'0' as i64), self.xlen);
            c = self.read_byte();
        }
        if negative { fold::wrap(n.wrapping_neg(), self.xlen) } else { n }
    }

    fn effect(&mut self, f: &Function, e: Value, env: &mut Env, depth: usize) -> Result<Option<i64>, Stop> {
        self.step()?;
        Ok(match &f.values[e.index()].node {
            Node::Load(a) | Node::Fixed(a) => {
                let a = self.eval(f, *a, env)?;
                Some(self.memory[self.address(a)?])
            }
            Node::Store(a, x) => {
                let a = self.eval(f, *a, env)?;
                let a = self.address(a)?;
                self.memory[a] = self.eval(f, *x, env)?;
                None
            }
            Node::Call(name, args) => {
                let callee = self.module.index_of(name).expect("verified");
                let args = args.iter().map(|&a| self.eval(f, a, env)).collect::<Result<_, _>>()?;
                Some(self.call(callee, args, depth + 1)?)
            }
            Node::CallIndirect(g, args) => {
                let g = self.eval(f, *g, env)?;
                let callee = usize::try_from(g - 1)
                    .ok()
                    .filter(|&i| i > 0 && i < self.module.funcs.len())
                    .ok_or_else(|| Stop::from(format!("{g} isn't a function's address")))?;
                if self.module.funcs[callee].param_count() != args.len() {
                    return Err(format!("{} takes {} arguments, not {}", self.module.funcs[callee].name, self.module.funcs[callee].param_count(), args.len()).into());
                }
                let args = args.iter().map(|&a| self.eval(f, a, env)).collect::<Result<_, _>>()?;
                Some(self.call(callee, args, depth + 1)?)
            }
            // as the VM calls one: the arguments in cells next to each other
            // (just above the stack), with the pointer at the first, and the
            // result left in acc
            Node::CallExtern(name, args) => {
                let args: Vec<i64> = args.iter().map(|&a| self.eval(f, a, env)).collect::<Result<_, _>>()?;
                let at = self.sp;
                if at + args.len() >= self.hp {
                    return Err("out of memory".into());
                }
                self.memory[at..at + args.len()].copy_from_slice(&args);
                let host = self.externs[name].clone();
                let mut memory = Cells(&mut self.memory);
                let mut call = HostCall { tape: &mut memory, ptr: at as i64, acc: 0, output: &mut self.output };
                (host.run)(&mut call)?;
                if call.ptr != at as i64 {
                    return Err(format!("the external function {name} moved the pointer").into());
                }
                Some(fold::wrap(call.acc, self.xlen))
            }
            Node::GetChar => Some(self.read_byte()),
            Node::GetInt => Some(self.read_int()),
            Node::PutChar(x) => {
                let x = self.eval(f, *x, env)?;
                self.output.push(x as u8);
                None
            }
            Node::PutInt(x) => {
                let x = self.eval(f, *x, env)?;
                self.output.extend(x.to_string().bytes());
                None
            }
            Node::PutUInt(x) => {
                let x = self.eval(f, *x, env)?;
                self.output.extend(fold::unsigned(x, self.xlen).to_string().bytes());
                None
            }
            Node::Puts(s) => {
                self.output.extend(s.bytes());
                None
            }
            // nothing is ever freed here, so fresh cells are already 0
            Node::HeapAlloc(n) | Node::GcAlloc(n, _) => {
                let n = self.eval(f, *n, env)?;
                let n = usize::try_from(n).ok().filter(|&n| n <= self.hp - self.sp).ok_or("out of memory")?;
                self.hp -= n;
                Some(self.hp as i64)
            }
            Node::Abort => return Err(Stop::Aborted),
            Node::Intrinsic(which, args) => {
                let args: Vec<i64> = args.iter().map(|&a| self.eval(f, a, env)).collect::<Result<_, _>>()?;
                match which {
                    Intrinsic::StackPointer => Some(self.sp as i64),
                    Intrinsic::HeapPointer => Some(self.hp as i64),
                    Intrinsic::SetHeapPointer => {
                        self.hp = usize::try_from(args[0]).ok().filter(|&a| a >= self.sp && a <= self.memory.len()).ok_or("bad heap pointer")?;
                        None
                    }
                    Intrinsic::RootsStart => Some(1 + self.module.globals as i64),
                }
            }
            Node::Alloca(cells) => {
                let start = self.sp;
                self.sp += *cells as usize;
                if self.sp > self.hp {
                    return Err("out of memory".into());
                }
                Some(start as i64)
            }
            Node::Const(_) | Node::Param(..) | Node::Unary(..) | Node::Binary(..) | Node::FuncAddr(_) | Node::GlobalAddr(_) => {
                unreachable!("not effects")
            }
        })
    }
}
