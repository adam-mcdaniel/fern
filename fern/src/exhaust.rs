//! Whether a match's patterns cover every value, and if not, an example of
//! one they miss (Maranget, "Warnings for pattern matching").
//!
//! The idea: look for a value no row of patterns matches, a column at a
//! time. If the first column names every variant of its enum, try each
//! variant in turn (keeping the rows that could match it, with its fields
//! as new columns). If it doesn't, a variant it leaves out works for the
//! first column, if the rest can be missed by the rows that match anything
//! there. Numbers and strings have too many values to name them all, so a
//! column of them is like one naming only some variants.

use crate::core::Pat;

/// A value the patterns miss.
pub enum Example {
    Any,
    Con(String, i64, Vec<Example>),
    Tuple(Vec<Example>),
    /// A number or string none of the patterns name.
    Other,
}

impl Example {
    pub fn show(&self, name: &dyn Fn(&str, i64) -> String) -> String {
        match self {
            Example::Any => "_".into(),
            Example::Other => "some other value".into(),
            Example::Tuple(xs) => format!("({})", xs.iter().map(|x| x.show(name)).collect::<Vec<_>>().join(", ")),
            Example::Con(e, k, xs) if xs.is_empty() => name(e, *k),
            Example::Con(e, k, xs) => format!("{}({})", name(e, *k), xs.iter().map(|x| x.show(name)).collect::<Vec<_>>().join(", ")),
        }
    }
}

/// A value that none of `pats` matches, if there is one. `variants` gives an
/// enum's variants' numbers of fields.
pub fn missing(pats: &[Pat], variants: &dyn Fn(&str) -> Vec<usize>) -> Option<Example> {
    let rows: Vec<Vec<Pat>> = pats.iter().map(|p| vec![p.clone()]).collect();
    witness(&rows, 1, variants).map(|mut w| w.remove(0))
}

fn is_wild(p: &Pat) -> bool {
    matches!(p, Pat::Wild | Pat::Bind(_))
}

/// A row of values (one per column) that no row matches.
fn witness(rows: &[Vec<Pat>], width: usize, variants: &dyn Fn(&str) -> Vec<usize>) -> Option<Vec<Example>> {
    if width == 0 {
        return rows.is_empty().then(Vec::new);
    }
    let firsts: Vec<&Pat> = rows.iter().map(|r| &r[0]).collect();
    // a tuple column: its parts as columns
    if let Some(n) = firsts.iter().find_map(|p| if let Pat::Tuple(ps) = p { Some(ps.len()) } else { None }) {
        let spec: Vec<Vec<Pat>> = rows
            .iter()
            .map(|r| {
                let mut out = match &r[0] {
                    Pat::Tuple(ps) => ps.clone(),
                    _ => vec![Pat::Wild; n],
                };
                out.extend(r[1..].iter().cloned());
                out
            })
            .collect();
        let mut w = witness(&spec, width - 1 + n, variants)?;
        let rest = w.split_off(n);
        let mut out = vec![Example::Tuple(w)];
        out.extend(rest);
        return Some(out);
    }
    // an enum column
    if let Some(e) = firsts.iter().find_map(|p| if let Pat::Con(e, _, _) = p { Some(e.clone()) } else { None }) {
        let arities = variants(&e);
        let named: Vec<i64> = firsts.iter().filter_map(|p| if let Pat::Con(_, k, _) = p { Some(*k) } else { None }).collect();
        let complete = (0..arities.len() as i64).all(|k| named.contains(&k));
        if complete {
            for (k, &arity) in arities.iter().enumerate() {
                let spec = specialize(rows, k as i64, arity);
                if let Some(mut w) = witness(&spec, width - 1 + arity, variants) {
                    let rest = w.split_off(arity);
                    let mut out = vec![Example::Con(e.clone(), k as i64, w)];
                    out.extend(rest);
                    return Some(out);
                }
            }
            return None;
        }
        let mut w = witness(&default(rows), width - 1, variants)?;
        let k = (0..arities.len() as i64).find(|k| !named.contains(k)).unwrap();
        let fields = (0..arities[k as usize]).map(|_| Example::Any).collect();
        w.insert(0, Example::Con(e, k, fields));
        return Some(w);
    }
    // numbers, strings, or nothing but wildcards
    let mut w = witness(&default(rows), width - 1, variants)?;
    let literal = firsts.iter().any(|p| matches!(p, Pat::Int(_) | Pat::Str(_)));
    w.insert(0, if literal { Example::Other } else { Example::Any });
    Some(w)
}

/// The rows that could match variant `k` (with `arity` fields), with its
/// fields' patterns as new first columns.
fn specialize(rows: &[Vec<Pat>], k: i64, arity: usize) -> Vec<Vec<Pat>> {
    rows.iter()
        .filter_map(|r| {
            let mut out = match &r[0] {
                Pat::Con(_, j, ps) if *j == k => ps.clone(),
                Pat::Con(..) => return None,
                p if is_wild(p) => vec![Pat::Wild; arity],
                _ => return None,
            };
            out.extend(r[1..].iter().cloned());
            Some(out)
        })
        .collect()
}

/// The rows that match anything in the first column, without it.
fn default(rows: &[Vec<Pat>]) -> Vec<Vec<Pat>> {
    rows.iter().filter(|r| is_wild(&r[0])).map(|r| r[1..].to_vec()).collect()
}
