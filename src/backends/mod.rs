//! The VM's ops as C, two ways:
//!
//! - [`LiteralC`]: each op as the C that does what it does, one after the
//!   other: the plainest translation, to check the other against;
//! - [`OptimizingC`]: C a compiler can make fast code of (the routines it
//!   knows done with the machine's instructions, a function's cells kept in
//!   variables, loops run in parallel where they can be, ...).
//!
//! [`cli`] is the options both `bf` and `fern` take for them.

use crate::Target;
use crate::Op;

pub mod cli;
mod optimizing_c;
pub use optimizing_c::{CSource, OptimizingC};

/// The VM's ops as C, each as the C that does what it does.
#[derive(Clone, Copy, Debug)]
pub struct LiteralC;

/// One of the C backends, as it's set up.
#[derive(Clone, Copy, Debug)]
pub enum CBackend {
    Optimizing(OptimizingC),
    Literal(LiteralC),
}

impl CBackend {
    /// The ops as C, in parts (the literal backend's is one part).
    pub fn source(&self, ops: &[Op]) -> CSource {
        match self {
            CBackend::Optimizing(c) => c.clone().source(ops),
            CBackend::Literal(c) => CSource { head: String::new(), chunks: vec![c.clone().compile(ops)], tail: String::new() },
        }
    }

    /// Whether its loops run in parallel.
    pub fn parallel(&self) -> bool {
        matches!(self, CBackend::Optimizing(c) if c.parallel)
    }

    /// The same, with loops that don't run in parallel.
    pub fn without_parallel(self) -> CBackend {
        match self {
            CBackend::Optimizing(c) => CBackend::Optimizing(OptimizingC { parallel: false, ..c }),
            other => other,
        }
    }
}


pub const PRELUDE: &str = r#"
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>

/* the tape's size, in cells: as big as the program was compiled for (a
   program's heap starts at the end of the tape it was made for) */
#ifndef BF_CELLS
#define BF_CELLS 100000
#endif

static int64_t **stack = NULL;
static int64_t *tape=NULL, *ptr=NULL, acc=0;
static void (*f)() = NULL;
/* (the program runs on the main thread: see bf.h) */
void bf_on_main_thread(void (*job)(void *), void *arg) { job(arg); }
/* the external function an aborting program calls (see the IR's
   `Options::exits`): stops it, with the status it's given */
void bf_exit(int64_t **tape, int64_t **ptr, int64_t *acc) { (void)tape; (void)acc; fflush(stdout); exit((int)**ptr); }
"#;

impl Target for LiteralC {
    fn compile(&mut self, ops: &[Op]) -> String {
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
        

        let result = format!("{PRELUDE} {} {global_defs} int main() {{stack=malloc(1024 * sizeof(int64_t)); tape=calloc(BF_CELLS, sizeof(int64_t)); if (!tape) {{ fputs(\"out of memory\\n\", stdout); return 1; }} ptr=tape; {main} return 0;}}", labels.into_iter().map(|name| format!("void {name}(int64_t **tape, int64_t **ptr, int64_t *acc);")).collect::<String>());
        return result;
    }
}