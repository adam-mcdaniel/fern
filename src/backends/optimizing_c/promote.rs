//! A function's cells as the C compiler's variables, where it can be done.
//!
//! A function reaches most of the cells it uses at fixed places from where
//! the pointer was when it was called (`asm` keeps a function's values in
//! fixed cells). As plain C, those are memory, which the C compiler has to
//! assume any write through a pointer might change: it can keep none of
//! them in registers, or know what's in them. Here each is a variable of
//! its own instead (`c5` for the cell 5 past where the pointer started,
//! `cm5` for 5 before), and only written to memory where something might
//! look: before a call (which can read anything), before returning, and
//! before what follows is done as the plain C. What's been set since it
//! was last written there (as far as can be told without running it: in a
//! loop, everything the loop sets) is what's written.
//!
//! That's only right while nothing else reads or writes those cells, so
//! the code checks, and where something might, it carries on as the plain
//! C, which goes to memory for everything (the function is both, one after
//! the other, and code that finds it can't go on writes its variables to
//! memory and jumps to the same place in the plain C):
//!
//! - an access through a pointer checks the address against the cells the
//!   function keeps as variables (a read, only if some variable has been
//!   set since memory was written),
//! - a call, which can write anything, is followed by reading the cells
//!   back (the C compiler drops what isn't read), and a check that the
//!   pointer is back where it was; but a call to a function that never
//!   returns (see `stopping`) is the plain code's, since reading the cells
//!   back on a way that's never taken would keep them all from being in
//!   registers everywhere else,
//! - and what isn't worked out here (a loop that moves the pointer, a `*`
//!   that isn't undone in the same place, ...) is done by the plain C.
//!
//! In a program `asm` made, a pointer only reaches a function's fixed cells
//! in the garbage collector, looking for pointers there, and every function
//! leaves the pointer where it found it: the checks pass, and the plain C
//! only runs for what isn't worked out here.

use super::{callee, op_c, Item};
use crate::asm::fx::{HashMap, HashSet};
use crate::Op;
use std::collections::BTreeSet;
use std::fmt::Write;

/// The function `name` done this way: the body of the function (`ptr` and
/// `acc` are its parameters, and it returns a `bf_st`), and the plain code,
/// a function of its own (`bf_plain_NAME`, to go before it), or None if
/// it's nothing this can do anything for.
pub(super) fn function(name: &str, body: &[Item], most_ops: usize, funcs: &HashMap<String, &[Item]>, stops: &HashSet<String>, known: &HashMap<String, String>, linear: &HashMap<String, String>) -> Option<(String, String)> {
    if body.iter().any(|item| matches!(item, Item::Func(..))) || ops(body) > most_ops {
        return None;
    }
    let mut w = Walker::new(funcs, stops, known, linear, "bf_".into());
    w.list(body, true);
    if w.cells.is_empty() {
        return None;
    }
    let plain_name = format!("bf_plain_{name}");
    let mut out = w.prologue();
    out += &w.fast_code();
    out += &w.flush();
    let _ = writeln!(out, "return (bf_st){{bf_e + ({}), acc}};", w.at);
    out += &w.exit_blocks();
    out += "#undef BF_KEPT\n";
    let saved: String = (0..w.depth.max(1)).map(|d| format!(", bf_s{d}")).collect();
    let out = out.replace(TO_PLAIN, &format!("return {plain_name}(ptr, acc, bf_site{saved});"));
    // (the plain code goes on from where the fast code left it: it's only
    // run for what the fast code can't do, so it's made small, and quickly)
    let saved: String = (0..w.depth.max(1)).map(|d| format!(", int64_t *bf_s{d}")).collect();
    let mut plain = format!("\nstatic bf_st __attribute__((cold, noinline)) {plain_name}(int64_t *ptr, int64_t acc, int bf_site{saved}) {{\n");
    plain += &w.dispatch();
    plain += &w.plain;
    plain += "return (bf_st){ptr, acc};\n}\n";
    Some((out, plain))
}

/// The loop `item` (number `id`) done this way, in a function that isn't
/// (it's too big): its cells read into variables when it starts, and what's
/// set written back when it ends; and the plain code of the loop, a
/// function of its own (`bf_rID_plain`, to go before the function), which
/// goes on from where the fast code left it and returns when the loop
/// ends. Or None, if it's nothing this can do anything for.
pub(super) fn region(id: usize, item: &Item, funcs: &HashMap<String, &[Item]>, stops: &HashSet<String>, known: &HashMap<String, String>, linear: &HashMap<String, String>) -> Option<(String, String)> {
    let Item::Loop(body) = item else { return None };
    if net(body) != Some(0) || ops(body) > LOOP_OPS || body.iter().any(|item| matches!(item, Item::Func(..))) {
        return None;
    }
    let mut w = Walker::new(funcs, stops, known, linear, format!("bf_r{id}_"));
    w.list(std::slice::from_ref(item), true);
    if w.cells.is_empty() {
        return None;
    }
    let p = &w.prefix;
    let mut out = String::from("{\n");
    out += &w.prologue();
    out += &w.fast_code();
    out += &w.flush();
    let _ = writeln!(out, "ptr = bf_e + ({});\ngoto {p}done;", w.at);
    out += &w.exit_blocks();
    let _ = writeln!(out, "{p}done:;\n#undef BF_KEPT\n}}");
    let saved: String = (0..w.depth.max(1)).map(|d| format!(", bf_s{d}")).collect();
    let out = out.replace(TO_PLAIN, &format!("{{ bf_st bf_r = {p}plain(ptr, acc, bf_site{saved}); ptr = bf_r.ptr; acc = bf_r.acc; goto {p}done; }}"));
    let saved: String = (0..w.depth.max(1)).map(|d| format!(", int64_t *bf_s{d}")).collect();
    let mut plain = format!("\nstatic bf_st __attribute__((cold, noinline)) {p}plain(int64_t *ptr, int64_t acc, int bf_site{saved}) {{\n");
    plain += &w.dispatch();
    plain += &w.plain;
    plain += "return (bf_st){ptr, acc};\n}\n";
    Some((out, plain))
}

/// The most ops a function can have for this to be done throughout it (by
/// default: see `OptimizingC::promote_ops`). Bigger, and its many
/// variables and the paths between them take the C compiler far longer
/// than the plain code, for code that runs once (making a level, say): what
/// runs a lot is smaller. (Of a game's functions, 99 in 100 are under this.)
pub(super) const MOST_OPS: usize = 16_000;

/// The most ops a loop can have for this to be done to it on its own (in a
/// function too big to be done throughout). A function that big is one
/// that runs once, mostly, and the loops in it that run a lot are its
/// small, inner ones: each of the big ones costs the C compiler as much as
/// a whole function would.
const LOOP_OPS: usize = 3_000;

fn ops(items: &[Item]) -> usize {
    items.iter().map(|item| match item {
        Item::Op(_) => 1,
        Item::Loop(body) | Item::Func(_, body) => 2 + ops(body),
    }).sum()
}

/// Where going on in the plain code goes, once it's known how.
const TO_PLAIN: &str = "/*bf to plain*/";

/// Where a call's reading the cells back goes, once it's known which.
const RELOAD: &str = "/*bf reload*/\n";

fn cell(k: i64) -> String {
    if k < 0 { format!("cm{}", -k) } else { format!("c{k}") }
}

struct Walker<'a> {
    funcs: &'a HashMap<String, &'a [Item]>,
    /// The functions that never return.
    stops: &'a HashSet<String>,
    /// What the labels start with (`bf_`, or a loop's own, `bf_r7_`).
    prefix: String,
    known: &'a HashMap<String, String>,
    linear: &'a HashMap<String, String>,
    /// The code with the cells as variables, and the plain code.
    fast: String,
    plain: String,
    /// Where the pointer is, in the fast code, from where it started.
    at: i64,
    /// Inside `*`s (each undone by a `&` in the same place): how far from
    /// where each went the pointer is (from `bf_q0`, `bf_q1`, ...).
    regions: Vec<i64>,
    cells: BTreeSet<i64>,
    /// The cells whose variables may have been set since they were last
    /// written to memory.
    dirty: BTreeSet<i64>,
    /// The ways the fast code goes on in the plain code, by what each
    /// writes to memory first.
    exits: Vec<BTreeSet<i64>>,
    sites: usize,
    /// The most `*`s in effect at once.
    depth: usize,
    inlining: Vec<String>,
}

impl<'a> Walker<'a> {
    fn new(funcs: &'a HashMap<String, &'a [Item]>, stops: &'a HashSet<String>, known: &'a HashMap<String, String>, linear: &'a HashMap<String, String>, prefix: String) -> Walker<'a> {
        Walker { funcs, stops, known, linear, prefix, fast: String::new(), plain: String::new(), at: 0, regions: vec![], cells: BTreeSet::new(), dirty: BTreeSet::new(), exits: vec![], sites: 0, depth: 0, inlining: vec![] }
    }

    /// The declarations the code needs, with the cells read into their
    /// variables, and `BF_KEPT(p)`: whether `p` is one of their cells (in
    /// one of the runs of them, or with many runs, in a table of which).
    /// It asks first whether `p` is below the last of them, which is all
    /// it takes for the cells above: the heap, in a program `asm` made
    /// (the variables' cells are at the bottom of the stack).
    fn prologue(&self) -> String {
        let cells: Vec<i64> = self.cells.iter().copied().collect();
        let (lo, hi) = (cells[0], cells[cells.len() - 1]);
        let mut out = String::from("int64_t *bf_e = ptr;\nint bf_site = 0;\n");
        for d in 0..self.depth {
            let _ = writeln!(out, "int64_t *bf_q{d} = NULL, *bf_s{d} = NULL;");
        }
        // (the saved pointers aren't used without `*`s, but the plain code
        // is always given them)
        for d in self.depth..self.depth.max(1) {
            let _ = writeln!(out, "int64_t *bf_s{d} = NULL;");
        }
        for chunk in cells.chunks(16) {
            let _ = writeln!(out, "int64_t {};", chunk.iter().map(|&k| format!("{} = bf_e[{k}]", cell(k))).collect::<Vec<_>>().join(", "));
        }
        let mut runs: Vec<(i64, i64)> = vec![];
        for &k in &cells {
            match runs.last_mut() {
                Some((_, end)) if k == *end + 1 => *end = k,
                _ => runs.push((k, k)),
            }
        }
        let below = format!("(uintptr_t)(p) < (uintptr_t)(bf_e + ({}))", hi + 1);
        if runs.len() <= 4 {
            let tests: Vec<String> = runs.iter().map(|&(a, b)| format!("(uintptr_t)(p) - (uintptr_t)(bf_e + ({a})) < {}", (b - a + 1) * 8)).collect();
            let _ = writeln!(out, "#define BF_KEPT(p) ({below} && ({}))", tests.join(" || "));
        } else {
            let table = (lo..=hi).map(|k| if self.cells.contains(&k) { "1" } else { "0" }).collect::<Vec<_>>().join(",");
            let _ = writeln!(out, "static const unsigned char {}kept[{}] = {{{table}}};", self.prefix, hi - lo + 1);
            let _ = writeln!(out, "#define BF_KEPT(p) ({below} && (uintptr_t)(p) >= (uintptr_t)(bf_e + ({lo})) && {}kept[((int64_t *)(p) - (bf_e + ({lo})))])", self.prefix);
        }
        out
    }

    /// The fast code, with the cells read back after each call.
    fn fast_code(&self) -> String {
        let reload: String = self.cells.iter().map(|&k| format!("{} = bf_e[{k}];\n", cell(k))).collect();
        self.fast.replace(RELOAD, &reload)
    }

    /// Each way to the plain code: what it writes to memory first.
    fn exit_blocks(&self) -> String {
        let mut out = String::new();
        for (i, dirty) in self.exits.iter().enumerate() {
            let _ = writeln!(out, "{}x{i}:;", self.prefix);
            for &k in dirty {
                let _ = writeln!(out, "bf_e[{k}] = {};", cell(k));
            }
            let _ = writeln!(out, "{TO_PLAIN}");
        }
        out
    }

    /// Where the plain code goes on, by `bf_site`.
    fn dispatch(&self) -> String {
        let mut out = String::from("switch (bf_site) {\n");
        for site in 1..=self.sites {
            let _ = writeln!(out, "case {site}: goto {}p{site};", self.prefix);
        }
        out + "}\n"
    }

    /// `items` both ways; with `fast` false, only as the plain code (the
    /// fast code has gone on to the plain code before them).
    fn list(&mut self, items: &[Item], fast: bool) {
        let pairs = pairs(items);
        let mut fast = fast;
        let mut i = 0;
        while i < items.len() {
            if !fast {
                self.plain_item(items, i);
                i += 1;
                continue;
            }
            match &items[i] {
                Item::Op(Op::Deref) if pairs.contains_key(&i) => {
                    let end = pairs[&i];
                    self.region(&items[i..=end]);
                    i = end + 1;
                    continue;
                }
                Item::Op(Op::Deref | Op::Refer) => {
                    // (a `*` this doesn't follow: the plain code does it)
                    self.leave();
                    fast = false;
                    continue;
                }
                Item::Op(Op::Call) if callee(items, i).is_some_and(|f| self.stops.contains(&f)) => {
                    // (a call that never returns: the plain code makes it,
                    // so the fast code needn't read the cells back after
                    // it, on a way that's never taken, which would keep
                    // them all from being in registers)
                    self.leave();
                    fast = false;
                    continue;
                }
                Item::Op(Op::Call) => self.call(items, i),
                Item::Op(op) => self.op(*op),
                Item::Loop(body) => {
                    if net(body) == Some(0) {
                        // (anything the loop sets may have been set, all
                        // the way round)
                        let mut head = self.dirty.clone();
                        self.writes(body, self.at, &mut head);
                        self.dirty = head.clone();
                        let open = opening(body);
                        self.fast += open;
                        self.plain += open;
                        let at = self.at;
                        self.list(body, true);
                        self.at = at;
                        debug_assert!(self.dirty.is_subset(&head), "a loop sets only what `writes` says");
                        self.dirty = head;
                        self.fast += "}\n";
                        self.plain += "}\n";
                    } else {
                        // (a loop that moves the pointer: the plain code's)
                        let exit = self.exit();
                        let _ = writeln!(self.fast, "if (acc) {{ {exit} }}");
                        self.plain_item(items, i);
                    }
                }
                Item::Func(..) => unreachable!("no functions inside"),
            }
            i += 1;
        }
    }

    fn site(&mut self) -> usize {
        self.sites += 1;
        self.sites
    }

    /// Goes on in the plain code from here, at the next op.
    fn leave(&mut self) {
        let exit = self.exit();
        let _ = writeln!(self.fast, "{exit}");
    }

    /// C that goes on in the plain code from here (where the plain code gets
    /// a label for it): it sets the pointer as that has it, and writes to
    /// memory, on the way, what has to be.
    fn exit(&mut self) -> String {
        let site = self.site();
        let _ = writeln!(self.plain, "{}p{site}:;", self.prefix);
        let jump = if self.dirty.is_empty() {
            self.to_plain()
        } else {
            let i = match self.exits.iter().position(|d| *d == self.dirty) {
                Some(i) => i,
                None => {
                    self.exits.push(self.dirty.clone());
                    self.exits.len() - 1
                }
            };
            format!("goto {}x{i};", self.prefix)
        };
        format!("{}bf_site = {site}; {jump}", self.where_c())
    }

    /// C that goes on in the plain code (at `bf_site`, with the pointers
    /// set), and returns what it does. (A placeholder, until it's known how
    /// many saved pointers the plain code takes.)
    fn to_plain(&self) -> String {
        TO_PLAIN.to_string()
    }

    /// C that writes to memory the variables that may have been set since
    /// they last were.
    fn flush(&self) -> String {
        self.dirty.iter().map(|&k| format!("bf_e[{k}] = {}; ", cell(k))).collect()
    }

    /// C that sets the pointer (and the pointers the `*`s saved) as the
    /// plain code has them here.
    fn where_c(&self) -> String {
        let mut out = String::new();
        for d in 0..self.regions.len() {
            let saved = if d == 0 { format!("bf_e + ({})", self.at) } else { format!("bf_q{} + ({})", d - 1, self.regions[d - 1]) };
            let _ = write!(out, "bf_s{d} = {saved}; ");
        }
        let _ = write!(out, "ptr = {}; ", self.pointer());
        out
    }

    fn pointer(&self) -> String {
        match self.regions.last() {
            Some(j) => format!("bf_q{} + ({j})", self.regions.len() - 1),
            None => format!("bf_e + ({})", self.at),
        }
    }

    /// The cell the pointer's at, as C: a variable, or memory, in a `*`.
    fn here(&mut self) -> String {
        match self.regions.last() {
            Some(j) => format!("bf_q{}[{j}]", self.regions.len() - 1),
            None => {
                self.cells.insert(self.at);
                cell(self.at)
            }
        }
    }

    /// An op that isn't a call, a `*` or a `&`, both ways.
    fn op(&mut self, op: Op) {
        // (through a pointer, at one of the variables' cells, the plain code
        // goes on from here: a read, only if memory might not have what
        // they hold)
        if !self.regions.is_empty() && (op == Op::Store || (matches!(op, Op::Load | Op::Add) && !self.dirty.is_empty())) {
            let p = self.pointer();
            let exit = self.exit();
            let _ = writeln!(self.fast, "if (BF_KEPT({p})) {{ {exit} }}");
        }
        self.plain += &op_c(op, self.funcs);
        self.plain.push('\n');
        match op {
            Op::Move(n) => match self.regions.last_mut() {
                Some(j) => *j += n,
                None => self.at += n,
            },
            Op::Load => {
                let c = self.here();
                let _ = writeln!(self.fast, "acc = {c};");
            }
            Op::Add => {
                let c = self.here();
                let _ = writeln!(self.fast, "acc = (int64_t)((uint64_t)acc + (uint64_t){c});");
            }
            Op::Store => {
                let c = self.here();
                let _ = writeln!(self.fast, "{c} = acc;");
                if self.regions.is_empty() {
                    self.dirty.insert(self.at);
                }
            }
            Op::Where => {
                let _ = writeln!(self.fast, "acc = (int64_t)({});", self.pointer());
            }
            _ => {
                self.fast += &op_c(op, self.funcs);
                self.fast.push('\n');
            }
        }
    }

    /// A `*` and the `&` that undoes it (`items`, from one to the other),
    /// with nothing between but ops and more of the same.
    fn region(&mut self, items: &[Item]) {
        let d = self.regions.len();
        self.depth = self.depth.max(d + 1);
        let from = self.here();
        let _ = writeln!(self.fast, "bf_q{d} = (int64_t *){from};");
        let _ = writeln!(self.plain, "bf_s{d} = ptr; ptr = (int64_t *)*ptr;");
        self.regions.push(0);
        let inner = &items[1..items.len() - 1];
        let pairs = pairs(inner);
        let mut i = 0;
        while i < inner.len() {
            match &inner[i] {
                Item::Op(Op::Deref) => {
                    let end = pairs[&i];
                    self.region(&inner[i..=end]);
                    i = end + 1;
                    continue;
                }
                Item::Op(op) => self.op(*op),
                _ => unreachable!("only ops in a region"),
            }
            i += 1;
        }
        self.regions.pop();
        let _ = writeln!(self.plain, "ptr = bf_s{d};");
    }

    /// A call: done natively, if it's to a routine the target knows or a
    /// linear function (as the plain code does it too), or else called,
    /// and the cells read back after.
    fn call(&mut self, items: &[Item], i: usize) {
        match self.kind(items, i) {
            Kind::Native(f, native, body) => {
                match native.split_once("ORIGINAL") {
                    Some((before, after)) => {
                        self.native(before);
                        self.inlining.push(f);
                        // (the routine's own code, for what the native code
                        // leaves to it: it leaves the pointer where it found
                        // it)
                        let at = self.at;
                        self.list(body, true);
                        self.at = at;
                        self.inlining.pop();
                        self.native(after);
                    }
                    None => self.native(native),
                }
                return;
            }
            Kind::Linear(code) => {
                self.native(code);
                return;
            }
            Kind::Call => {}
        }
        let site = self.site();
        let at = self.at;
        let call = op_c(Op::Call, self.funcs);
        let _ = writeln!(self.fast, "{}\nptr = bf_e + ({at});\n{call}\nif (ptr != bf_e + ({at})) {{ bf_site = {site}; {TO_PLAIN} }}\n{RELOAD}", self.flush());
        self.dirty.clear();
        let _ = writeln!(self.plain, "{call}\n{}p{site}:;", self.prefix);
    }

    /// Native code (`ptr[n]` for the cells, see `idioms`), both ways: in
    /// the fast code, with the variables (each write a line of its own).
    fn native(&mut self, code: &str) {
        self.plain += code;
        for line in code.lines() {
            let t = line.trim_start();
            if let Some((n, rest)) = t.strip_prefix("ptr[").and_then(|r| r.split_once(']')).and_then(|(n, rest)| Some((n.parse::<i64>().ok()?, rest.trim_start().strip_prefix('=')?.trim()))) {
                let k = self.at + n;
                self.cells.insert(k);
                let value = self.cells_in(rest.strip_suffix(';').unwrap_or(rest));
                let _ = writeln!(self.fast, "{} = {value};", cell(k));
                self.dirty.insert(k);
            } else {
                let line = self.cells_in(line);
                self.fast += &line;
                self.fast.push('\n');
            }
        }
    }

    /// `code` with `ptr[n]` the variables, and the pointer where it is.
    fn cells_in(&mut self, code: &str) -> String {
        let mut out = String::new();
        let mut rest = code;
        while let Some(i) = rest.find("ptr[") {
            out += &rest[..i];
            let (n, tail) = rest[i + 4..].split_once(']').expect("ptr[n]");
            let k = self.at + n.parse::<i64>().expect("a number");
            self.cells.insert(k);
            out += &cell(k);
            rest = tail;
        }
        out += rest;
        out.replace("(intptr_t)ptr", &format!("(intptr_t)(bf_e + ({}))", self.at))
    }

    /// How the fast code does the call `items[i]`.
    fn kind<'b>(&self, items: &[Item], i: usize) -> Kind<'b>
    where
        'a: 'b,
    {
        if let Some(f) = callee(items, i).filter(|f| !self.inlining.contains(f)) {
            if let Some(native) = self.known.get(&f).filter(|n| local(n)) {
                let body = self.funcs[&f];
                if simple(body) {
                    return Kind::Native(f, native, body);
                }
            }
            if let Some(code) = self.linear.get(&f).filter(|c| local(c)) {
                return Kind::Linear(code);
            }
        }
        Kind::Call
    }

    /// Adds to `set` the cells whose variables the fast code of `items`
    /// (starting at `at`) sets.
    fn writes(&mut self, items: &[Item], mut at: i64, set: &mut BTreeSet<i64>) {
        let native = |code: &str, at: i64, set: &mut BTreeSet<i64>| {
            for line in code.lines() {
                if let Some(n) = line.trim_start().strip_prefix("ptr[").and_then(|r| r.split_once(']')).filter(|(_, rest)| rest.trim_start().starts_with('=')).and_then(|(n, _)| n.parse::<i64>().ok()) {
                    set.insert(at + n);
                }
            }
        };
        let pairs = pairs(items);
        let mut i = 0;
        while i < items.len() {
            match &items[i] {
                Item::Op(Op::Move(n)) => at += n,
                Item::Op(Op::Store) => {
                    set.insert(at);
                }
                Item::Op(Op::Deref) if pairs.contains_key(&i) => i = pairs[&i],
                // (the rest is the plain code's, as `list` has it)
                Item::Op(Op::Deref | Op::Refer) => return,
                Item::Op(Op::Call) if callee(items, i).is_some_and(|f| self.stops.contains(&f)) => return,
                Item::Op(Op::Call) => match self.kind(items, i) {
                    Kind::Native(f, code, body) => {
                        native(code, at, set);
                        if code.contains("ORIGINAL") {
                            self.inlining.push(f);
                            self.writes(body, at, set);
                            self.inlining.pop();
                        }
                    }
                    Kind::Linear(code) => native(code, at, set),
                    Kind::Call => {}
                },
                Item::Loop(body) if net(body) == Some(0) => self.writes(body, at, set),
                _ => {}
            }
            i += 1;
        }
    }

    /// `items[i]` as the plain code only.
    fn plain_item(&mut self, items: &[Item], i: usize) {
        match &items[i] {
            Item::Op(Op::Call) => {
                let f = callee(items, i);
                if let Some(native) = f.as_ref().and_then(|f| self.known.get(f)).filter(|_| !self.inlining.contains(f.as_ref().unwrap())) {
                    let f = f.unwrap();
                    match native.split_once("ORIGINAL") {
                        Some((before, after)) => {
                            let (before, after) = (before.to_string(), after.to_string());
                            self.plain += &before;
                            self.inlining.push(f.clone());
                            let body = self.funcs[&f];
                            for k in 0..body.len() {
                                self.plain_item(body, k);
                            }
                            self.inlining.pop();
                            self.plain += &after;
                        }
                        None => self.plain += &native.clone(),
                    }
                } else if let Some(code) = f.and_then(|f| self.linear.get(&f)) {
                    self.plain += code;
                } else {
                    self.plain += &op_c(Op::Call, self.funcs);
                    self.plain.push('\n');
                }
            }
            Item::Op(op) => {
                self.plain += &op_c(*op, self.funcs);
                self.plain.push('\n');
            }
            Item::Loop(body) => {
                self.plain += opening(body);
                for k in 0..body.len() {
                    self.plain_item(body, k);
                }
                self.plain += "}\n";
            }
            Item::Func(..) => unreachable!("no functions inside"),
        }
    }
}

/// How a loop starts, as C: an `if`, if it can only go round once (`asm`
/// writes an `if` as a loop that ends with acc 0, by setting it, or by
/// another loop, which only ends when it is), and otherwise a `while`.
/// (An `if` is what the C compiler makes much better code of, and far more
/// quickly, than of a loop it would have to find goes round once.)
fn opening(body: &[Item]) -> &'static str {
    match body.last() {
        Some(Item::Op(Op::Set(0)) | Item::Loop(_)) => "if (acc) {\n",
        _ => "while (acc) {\n",
    }
}

/// How the fast code does a call: with a routine's native code (and its
/// own code, where that says), with a linear function's, or as a call.
enum Kind<'a> {
    Native(String, &'a str, &'a [Item]),
    Linear(&'a str),
    Call,
}

/// Each `*` in `items` that a `&` in the same list undoes, with nothing
/// between but ops (and more of the same): where that `&` is.
fn pairs(items: &[Item]) -> HashMap<usize, usize> {
    let mut out = HashMap::default();
    let mut open: Vec<usize> = vec![];
    for (i, item) in items.iter().enumerate() {
        match item {
            Item::Op(Op::Deref) => open.push(i),
            Item::Op(Op::Refer) => {
                if let Some(j) = open.pop() {
                    out.insert(j, i);
                }
            }
            Item::Op(Op::Call) | Item::Loop(_) | Item::Func(..) => open.clear(),
            Item::Op(_) => {}
        }
    }
    // (matched as brackets, everything between a pair is pairs too)
    out
}

/// How far `items` moves the pointer, as the fast code follows them, if
/// it's known: calls leave it where it was (or the plain code takes over).
fn net(items: &[Item]) -> Option<i64> {
    let pairs = pairs(items);
    let mut n = 0;
    let mut i = 0;
    while i < items.len() {
        match &items[i] {
            Item::Op(Op::Move(m)) => n += m,
            Item::Op(Op::Deref) if pairs.contains_key(&i) => i = pairs[&i],
            Item::Op(Op::Deref | Op::Refer) => return None,
            Item::Loop(body) if net(body) != Some(0) => return None,
            Item::Func(..) => return None,
            _ => {}
        }
        i += 1;
    }
    Some(n)
}

/// Whether a routine's body is only ops on cells near the pointer, and
/// loops that leave it where it was: nothing in it can need the plain code.
fn simple(items: &[Item]) -> bool {
    items.iter().all(|item| match item {
        Item::Op(op) => !matches!(op, Op::Deref | Op::Refer | Op::Call | Op::Read | Op::Write),
        Item::Loop(body) => simple(body) && net(body) == Some(0),
        Item::Func(..) => false,
    })
}

/// Whether native code only uses the pointer for its cells (`ptr[n]`) and
/// its address.
fn local(code: &str) -> bool {
    let mut rest = code.replace("(intptr_t)ptr", "");
    while let Some(i) = rest.find("ptr[") {
        let tail = &rest[i + 4..];
        match tail.split_once(']') {
            Some((n, _)) if n.parse::<i64>().is_ok() => rest = format!("{}{}", &rest[..i], &tail[n.len() + 1..]),
            _ => return false,
        }
    }
    // (any other `ptr` is the pointer used otherwise; `bf_ptrs` and the
    // like are other names)
    !rest.split(|c: char| !(c.is_alphanumeric() || c == '_')).any(|w| w == "ptr")
}
