//! Functions that are just a built-in operation: one whose body applies a
//! primitive to its parameters, each once and in order (the standard
//! library's `fn get(self, i: Int) -> T { array_get(self, i) }`), is that
//! primitive, so calls to it become the primitive itself. A method then
//! costs no more than the operation it names, whether or not the IR's
//! optimizer runs (it doesn't in debug builds).

use crate::core::{Core, Func, Prim};
use bf::asm::fx::HashMap;

pub fn inline(funcs: &mut [Func]) {
    let prims: HashMap<String, Prim> = funcs
        .iter()
        .filter_map(|f| match strip(&f.body) {
            Core::Prim(p, args) if args.len() == f.params.len() && args.iter().zip(&f.params).all(|(a, n)| matches!(a, Core::Local(m) if m == n)) => Some((f.name.clone(), *p)),
            _ => None,
        })
        .collect();
    if !prims.is_empty() {
        for f in funcs.iter_mut() {
            rewrite(&mut f.body, &prims);
        }
    }
}

/// `e`, without where it is (see `Core::Located`).
fn strip(e: &Core) -> &Core {
    match e {
        Core::Located(_, e) => strip(e),
        e => e,
    }
}

fn rewrite(e: &mut Core, prims: &HashMap<String, Prim>) {
    if let Core::CallGlobal(name, args, _) = e {
        if let Some(&p) = prims.get(name) {
            *e = Core::Prim(p, std::mem::take(args));
        }
    }
    for c in e.children_mut() {
        rewrite(c, prims);
    }
}
