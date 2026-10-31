//! Which code needs CPS: only code that may perform an operation, which is
//! what needs "the rest of the computation" as a value. The types say what
//! each call and lambda may do (`Eff`), so everything else is compiled to
//! ordinary IR functions, called and returning as usual, with loops as
//! loops and `let mut`s as variables, many times faster than CPS code.
//!
//! - A function whose effects are none, or only its effect parameters'
//!   (`fold`'s `'e`), has a *direct* version: for calls that do nothing,
//!   and calls from a direct version, where those parameters are nothing. One
//!   that may perform operations has a CPS version, so one with effect
//!   parameters has both.
//! - Likewise a closure: it has a CPS entry, and, unless its type says it
//!   performs operations, a direct one (see `codegen`). So calling a closure
//!   from a direct version is an ordinary call too.
//! - A direct version or entry is compiled straight from the core language
//!   if its body can be (see `compilable`). If not (it has a `handle`, say,
//!   whose body performs operations), it runs the CPS version to the end in
//!   a trampoline of its own: which is safe, as everything it performs, its
//!   own handlers handle.

use crate::core::{Core, Eff, Pat};

/// Whether `e` can be compiled straight to IR, for a direct version or
/// entry: it has no `handle`, performs nothing, and calls nothing that may
/// (its lambdas aside: each is a function of its own).
pub fn compilable(e: &Core) -> bool {
    match e {
        Core::Handle { .. } | Core::Perform { .. } | Core::App(_, _, Eff::Impure) | Core::CallGlobal(_, _, Eff::Impure) => false,
        Core::Lam(..) => true,
        _ => children(e).into_iter().all(compilable),
    }
}

/// The lambdas in `e` (not those inside them).
pub fn lambdas<'a>(e: &'a Core, out: &mut Vec<&'a Core>) {
    match e {
        Core::Lam(..) => out.push(e),
        _ => children(e).into_iter().for_each(|c| lambdas(c, out)),
    }
}

/// The local variables `e` uses that it doesn't bind, in the order it
/// first uses them: what a lambda's closure holds.
pub fn free_locals(e: &Core) -> Vec<String> {
    fn go(e: &Core, bound: &mut Vec<String>, out: &mut Vec<String>) {
        let under = |names: &[String], body: &Core, bound: &mut Vec<String>, out: &mut Vec<String>| {
            let n = bound.len();
            bound.extend(names.iter().cloned());
            go(body, bound, out);
            bound.truncate(n);
        };
        match e {
            Core::Local(n) => {
                if !bound.contains(n) && !out.contains(n) {
                    out.push(n.clone());
                }
            }
            Core::Let(n, v, b) => {
                go(v, bound, out);
                under(std::slice::from_ref(n), b, bound, out);
            }
            Core::Lam(_, ps, b, _) => under(ps, b, bound, out),
            Core::Match(s, arms) => {
                go(s, bound, out);
                for (p, b) in arms {
                    let mut names = vec![];
                    pattern_names(p, &mut names);
                    under(&names, b, bound, out);
                }
            }
            Core::Handle { body, ret: (v, r), ops, .. } => {
                go(body, bound, out);
                under(std::slice::from_ref(v), r, bound, out);
                for (ps, resume, b) in ops {
                    let mut names = ps.clone();
                    names.push(resume.clone());
                    under(&names, b, bound, out);
                }
            }
            _ => children(e).into_iter().for_each(|c| go(c, bound, out)),
        }
    }
    let mut out = vec![];
    go(e, &mut vec![], &mut out);
    out
}

fn pattern_names(p: &Pat, out: &mut Vec<String>) {
    match p {
        Pat::Bind(n) => out.push(n.clone()),
        Pat::Con(_, _, ps) | Pat::Tuple(ps) => ps.iter().for_each(|q| pattern_names(q, out)),
        Pat::Wild | Pat::Int(_) | Pat::Str(_) => {}
    }
}

/// Whether local `n` is only read and set (`GetRef` and `SetRef`) in `e`,
/// never used as a value, nor by a lambda (which shares it): then a `let
/// mut` can be a variable, not a cell.
pub fn only_through_refs(n: &str, e: &Core) -> bool {
    match e {
        Core::GetRef(r) if matches!(&**r, Core::Local(m) if m == n) => true,
        Core::SetRef(r, v) if matches!(&**r, Core::Local(m) if m == n) => only_through_refs(n, v),
        Core::Local(m) => m != n,
        Core::Lam(..) => !free_locals(e).iter().any(|m| m == n),
        _ => children(e).into_iter().all(|c| only_through_refs(n, c)),
    }
}

/// The expressions directly inside `e`.
pub fn children(e: &Core) -> Vec<&Core> {
    e.children()
}
