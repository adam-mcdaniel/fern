use crate::Target;
use crate::Op;

mod parallel_c;
pub use parallel_c::ParallelC;

#[derive(Clone, Copy, Debug)]
pub struct C;


pub const PRELUDE: &str = r#"
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>

static int64_t **stack = NULL;
static int64_t *tape=NULL, *ptr=NULL, acc=0;
static void (*f)() = NULL;
"#;

impl Target for C {
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
        

        let result = format!("{PRELUDE} {} {global_defs} int main() {{stack=malloc(1024 * sizeof(int64_t)); tape=malloc(100000 * sizeof(int64_t)); ptr=tape; {main} return 0;}}", labels.into_iter().map(|name| format!("void {name}(int64_t **tape, int64_t **ptr, int64_t *acc);")).collect::<String>());
        return result;
    }
}