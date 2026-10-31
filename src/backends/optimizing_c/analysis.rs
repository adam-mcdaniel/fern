//! Finds the loops whose iterations can run at the same time, and what it
//! takes to run them so.
//!
//! One iteration of a loop is run symbolically, from what the cells held
//! when it started: every value is a linear expression over symbols (what a
//! cell held at the iteration's start, where the pointer was, values the
//! analysis can't follow). Calls are followed into their bodies, loops that
//! run a known number of times are unrolled, and an `if` (or a loop whose
//! count isn't known) joins what its paths leave, with values that differ
//! becoming new symbols that remember what they came from.
//!
//! What that finds:
//!
//! - **Cells near the pointer** (reached by moving from where it is when
//!   the loop starts): each is an induction variable (it gains the same
//!   amount every time round), a reduction (it only accumulates sums), one
//!   that each iteration leaves as it found it, one that each iteration
//!   writes before it reads (private to the iteration), or one that's only
//!   read. Anything else makes the loop sequential. These cells are copied
//!   for each thread.
//! - **Memory a pointer leads to**: every access that writes is to `base +
//!   stride * k + offset`, for iteration `k`, where `base` and `stride` can
//!   be worked out when the loop starts (memory only read can be anywhere:
//!   the generated code checks, as it reads it, that no iteration writes
//!   it). Accesses that differ only by their offset are a
//!   *family*. Families are assumed not to overlap each other (so the
//!   analysis knows exactly what each access reads), and a family that's
//!   written to mustn't touch a cell another iteration does; the generated
//!   code checks both, with the real addresses, before running anything in
//!   parallel. A family whose base is a cell near the pointer that each
//!   iteration leaves as it found it, and that's always written before it's
//!   read (a stack, through its stack pointer), gets a copy for each thread.
//! - **How many times the loop runs**: if what decides whether it goes round
//!   again is linear in `k`, or a comparison of what is, by solving it;
//!   otherwise the ops that decide it (a *slice* of the body) are run for
//!   each `k` to find the first that stops it, which they can be as long as
//!   they only depend on `k`.
//!
//! Functions the target does natively (`asm`'s routines) aren't run, but
//! stand for what they may read and write; an `if`'s `else` is run from the
//! state where the `if` didn't run.

use super::Item;
use crate::Op;
use crate::asm::fx::{HashMap, HashSet};
use std::collections::{BTreeMap, BTreeSet};

/// Each address is in bytes, and cells are 8 bytes, as in C.
const CELL: i64 = 8;
/// The most ops one iteration's analysis can run, and times a loop with a
/// known count can be unrolled.
const BUDGET: usize = 1_000_000;

thread_local! {
    /// How many analyses of loops are under way, each in another's body.
    static DEPTH: std::cell::Cell<usize> = const { std::cell::Cell::new(0) };
    /// Whether loops in bodies are summed up: only once following them a
    /// time round at a time has failed (it finds more when it works).
    static SUMMING: std::cell::Cell<bool> = const { std::cell::Cell::new(false) };
    /// The analyses of loops in bodies (for summing them up), by their own
    /// bodies: what they find doesn't depend on where they are.
    static INNER: std::cell::RefCell<HashMap<*const Item, std::rc::Rc<Result<Plan, String>>>> = std::cell::RefCell::new(HashMap::default());
    /// For each of the program's functions, a function outside the program
    /// it calls (or the functions it calls do), if there is one: worked out
    /// once for all of them (see `outside_calls`).
    static OUTSIDE: std::cell::RefCell<Option<HashMap<String, Option<String>>>> = const { std::cell::RefCell::new(None) };
}

/// For testing: sum up loops in bodies that write memory after the first
/// time round, rather than following them one at a time as long as that's
/// worth it.
#[cfg(test)]
pub static SUMMED: std::sync::atomic::AtomicUsize = std::sync::atomic::AtomicUsize::new(0);
#[cfg(test)]
pub static SUM_UP_EARLY: std::sync::atomic::AtomicBool = std::sync::atomic::AtomicBool::new(false);

/// Forgets the analyses of loops in bodies (see `INNER`): for a new
/// program, whose bodies may be where an old one's were.
pub fn forget() {
    INNER.with(|c| c.borrow_mut().clear());
    OUTSIDE.with(|c| *c.borrow_mut() = None);
}

const UNROLL: usize = 512;
/// The most a loop with a known count can cost the analysis to follow a time
/// round at a time, before what holds however many times it goes round is
/// worked out instead.
const UNROLL_WORK: usize = 300_000;

/// A symbol, by number.
pub type Sym = u32;

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub enum SymKind {
    /// Where the pointer is when the iteration starts.
    P0,
    /// What acc holds when the iteration starts.
    Acc0,
    /// What the cell at this address holds when the iteration starts.
    Init(Lin),
    /// A value the analysis can't follow, made from these symbols.
    Fresh(u32),
}

/// `c + sum(coefficient * symbol)`, wrapping as cells do.
#[derive(Clone, Debug, Default, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct Lin {
    pub c: i64,
    pub terms: Terms,
}

/// A linear expression's terms: each symbol with its coefficient (never 0),
/// in order of symbol. Most have none or a few, so they're a sorted list,
/// not a map: no allocation for none, a short scan to find one. (Ordered
/// and compared as a map of them would be.)
#[derive(Clone, Debug, Default, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct Terms(Vec<(Sym, i64)>);

impl Terms {
    pub fn new() -> Terms {
        Terms(Vec::new())
    }

    fn position(&self, s: &Sym) -> Result<usize, usize> {
        self.0.binary_search_by_key(s, |&(t, _)| t)
    }

    pub fn get(&self, s: &Sym) -> Option<&i64> {
        self.position(s).ok().map(|i| &self.0[i].1)
    }

    pub fn contains_key(&self, s: &Sym) -> bool {
        self.position(s).is_ok()
    }

    /// Sets a symbol's coefficient (a 0 removes it), giving the old one.
    pub fn insert(&mut self, s: Sym, k: i64) -> Option<i64> {
        match self.position(&s) {
            Ok(i) if k == 0 => Some(self.0.remove(i).1),
            Ok(i) => Some(std::mem::replace(&mut self.0[i].1, k)),
            Err(_) if k == 0 => None,
            Err(i) => {
                self.0.insert(i, (s, k));
                None
            }
        }
    }

    pub fn remove(&mut self, s: &Sym) -> Option<i64> {
        self.position(s).ok().map(|i| self.0.remove(i).1)
    }

    pub fn iter(&self) -> impl Iterator<Item = (&Sym, &i64)> + Clone {
        self.0.iter().map(|(s, k)| (s, k))
    }

    pub fn keys(&self) -> impl Iterator<Item = &Sym> + Clone {
        self.0.iter().map(|(s, _)| s)
    }

    pub fn len(&self) -> usize {
        self.0.len()
    }

    pub fn is_empty(&self) -> bool {
        self.0.is_empty()
    }
}

impl<'a> IntoIterator for &'a Terms {
    type Item = (&'a Sym, &'a i64);
    type IntoIter = std::iter::Map<std::slice::Iter<'a, (Sym, i64)>, fn(&'a (Sym, i64)) -> (&'a Sym, &'a i64)>;
    fn into_iter(self) -> Self::IntoIter {
        self.0.iter().map(|(s, k)| (s, k))
    }
}

impl FromIterator<(Sym, i64)> for Terms {
    fn from_iter<I: IntoIterator<Item = (Sym, i64)>>(items: I) -> Terms {
        let mut v: Vec<(Sym, i64)> = items.into_iter().filter(|&(_, k)| k != 0).collect();
        v.sort_by_key(|&(s, _)| s);
        v.dedup_by_key(|&mut (s, _)| s);
        Terms(v)
    }
}

impl Lin {
    pub fn constant(c: i64) -> Lin {
        Lin { c, terms: Terms::new() }
    }

    pub fn sym(s: Sym) -> Lin {
        Lin { c: 0, terms: Terms(vec![(s, 1)]) }
    }

    fn add(&self, other: &Lin) -> Lin {
        let mut out = self.clone();
        out.c = out.c.wrapping_add(other.c);
        for (&s, &k) in &other.terms {
            let sum = out.terms.get(&s).copied().unwrap_or(0).wrapping_add(k);
            out.terms.insert(s, sum);
        }
        out
    }

    fn scale(&self, k: i64) -> Lin {
        let mut out = Lin { c: self.c.wrapping_mul(k), terms: Terms::new() };
        for (&s, &v) in &self.terms {
            let v = v.wrapping_mul(k);
            if v != 0 {
                out.terms.insert(s, v);
            }
        }
        out
    }

    pub fn sub(&self, other: &Lin) -> Lin {
        self.add(&other.scale(-1))
    }

    fn as_const(&self) -> Option<i64> {
        self.terms.is_empty().then_some(self.c)
    }

    /// The part that isn't constant: which family an address is in.
    pub fn family(&self) -> Lin {
        Lin { c: 0, terms: self.terms.clone() }
    }
}

/// A value: linear, or a function's address.
#[derive(Clone, Debug, PartialEq, Eq)]
enum Val {
    Lin(Lin),
    Func(String),
}

/// The symbols, and what each `Fresh` one was made from.
#[derive(Default, Debug)]
pub struct Syms {
    pub kinds: Vec<SymKind>,
    ids: HashMap<SymKind, Sym>,
    pub made_from: HashMap<Sym, BTreeSet<Sym>>,
    fresh: u32,
}

impl Syms {
    pub fn get(&mut self, k: SymKind) -> Sym {
        if let Some(&s) = self.ids.get(&k) {
            return s;
        }
        let s = self.kinds.len() as Sym;
        self.kinds.push(k.clone());
        self.ids.insert(k, s);
        s
    }

    fn fresh(&mut self, from: BTreeSet<Sym>) -> Sym {
        self.fresh += 1;
        let s = self.get(SymKind::Fresh(self.fresh));
        self.made_from.insert(s, from);
        s
    }

    /// Every symbol `s` depends on, itself included (through `Fresh`
    /// symbols, and the addresses of `Init` ones).
    pub fn closure(&self, start: impl IntoIterator<Item = Sym>) -> BTreeSet<Sym> {
        let mut out = BTreeSet::new();
        let mut work: Vec<Sym> = start.into_iter().collect();
        while let Some(s) = work.pop() {
            if !out.insert(s) {
                continue;
            }
            match &self.kinds[s as usize] {
                SymKind::Fresh(_) => work.extend(self.made_from[&s].iter().copied()),
                // what's read through a pointer depends on where that is (but
                // what's in a cell near the pointer doesn't depend on where
                // the pointer is, which is all those addresses say)
                SymKind::Init(a) if !self.near(a) => work.extend(a.terms.keys().copied()),
                _ => {}
            }
        }
        out
    }

    /// `closure`, but not following the addresses of what's read from the
    /// memory in `family`; and whether what was there before is among it.
    pub fn closure_apart(&self, start: impl IntoIterator<Item = Sym>, family: &Lin) -> (BTreeSet<Sym>, bool) {
        let mut out = BTreeSet::new();
        let mut before = false;
        let mut work: Vec<Sym> = start.into_iter().collect();
        while let Some(s) = work.pop() {
            if !out.insert(s) {
                continue;
            }
            match &self.kinds[s as usize] {
                SymKind::Fresh(_) => work.extend(self.made_from[&s].iter().copied()),
                SymKind::Init(a) if a.family() == *family => before = true,
                SymKind::Init(a) if !self.near(a) => work.extend(a.terms.keys().copied()),
                _ => {}
            }
        }
        (out, before)
    }

    /// Whether an address is a cell's near the pointer: `P0 + offset`.
    pub(crate) fn near(&self, a: &Lin) -> bool {
        match a.terms.iter().collect::<Vec<_>>()[..] {
            [(&s, &1)] => self.kinds[s as usize] == SymKind::P0,
            _ => false,
        }
    }

    fn deps(&self, v: &Val) -> BTreeSet<Sym> {
        match v {
            Val::Lin(l) => l.terms.keys().copied().collect(),
            Val::Func(_) => BTreeSet::new(),
        }
    }
}

/// Where a value lives, for slicing.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
enum Loc {
    Acc,
    Mem(Lin),
}

/// What one of the body's items (with everything inside it) reads and
/// writes; a write is definite if the item always does it.
#[derive(Clone, Debug, Default)]
struct Effects {
    reads: Vec<Loc>,
    writes: Vec<(Loc, bool)>,
}

/// When whether the loop goes round again (what acc holds at the end, or
/// what the guard starts on) comes down to a comparison of what's known when
/// the loop starts and induction variables: `x > 0`, for `x` linear in `k`.
fn compare_trip(first: &Interp, guard: Option<&(usize, Lin)>, cells: &BTreeMap<i64, Role>, readonly: &BTreeSet<Lin>, scalars: &HashMap<Lin, i64>) -> Option<Trip> {
    let cond = match guard {
        Some((_, c)) => c.clone(),
        None => match first.end_acc() {
            Val::Lin(c) => c,
            Val::Func(_) => return None,
        },
    };
    // `v` isn't 0 just when `x > 0` (with what's compared)
    fn resolve(it: &Interp, v: &Lin, depth: usize) -> Option<(Lin, Vec<(Lin, bool)>)> {
        if depth > 16 {
            return None;
        }
        let one = |l: &Lin| match l.terms.iter().collect::<Vec<_>>()[..] {
            [(&s, &k)] => Some((s, k, l.c)),
            _ => None,
        };
        let (s, k, c) = one(v)?;
        match (k, c, it.preds.get(&s)) {
            (1, 0, Some(Pred::Positive(x))) => Some((x.clone(), vec![(x.clone(), false)])),
            (1, 0, Some(Pred::Less(a, b, u))) => Some((b.sub(a), vec![(a.clone(), *u), (b.clone(), *u)])),
            // (1 - p, for p 1 or 0, is its negation)
            (-1, 1, Some(Pred::Positive(x))) => Some((Lin::constant(1).sub(x), vec![(x.clone(), false)])),
            (-1, 1, Some(Pred::Less(a, b, u))) => Some((a.sub(b).add(&Lin::constant(1)), vec![(a.clone(), *u), (b.clone(), *u)])),
            (1, 0, None) if it.equiv.contains_key(&s) => resolve(it, &it.equiv[&s].0, depth + 1),
            // an `if`/`else`'s value, where what it decided on is 0 as long as
            // something isn't below 0 (which the generated code checks)
            (1, 0, None) => {
                let (b, _, otherwise) = it.selects.get(&s)?;
                let x = zero_when(it, b)?;
                let (y, mut parts) = resolve(it, otherwise, depth + 1)?;
                parts.push((x, true));
                Some((y, parts))
            }
            _ => None,
        }
    }
    // `v` is 0 when `x` isn't below 0: `(x != 0) - (x > 0)`, which is how
    // `x < 0` is worked out
    fn zero_when(it: &Interp, v: &Lin) -> Option<Lin> {
        match v.terms.iter().collect::<Vec<_>>()[..] {
            [(&a, &ka), (&b, &kb)] if v.c == 0 => {
                let (z, p) = match (ka, kb) {
                    (1, -1) => (a, b),
                    (-1, 1) => (b, a),
                    _ => return None,
                };
                // (1 when it isn't 0, as `#` is when it holds)
                match (it.equiv.get(&z), it.preds.get(&p)) {
                    (Some((x, 1)), Some(Pred::Positive(y))) if x == y => Some(x.clone()),
                    _ => None,
                }
            }
            _ => None,
        }
    }
    let (x, parts) = resolve(first, &cond, 0)?;
    // all of it in cells that are known, or grow, from the start, and memory
    // the loop doesn't write, at addresses in cells it doesn't change
    fn lin_of(first: &Interp, cells: &BTreeMap<i64, Role>, readonly: &BTreeSet<Lin>, scalars: &HashMap<Lin, i64>, l: &Lin, fixed: bool) -> Option<CellLin> {
        let mut out = CellLin { c: l.c, terms: vec![], loads: vec![] };
        for (&s, &k) in &l.terms {
            match &first.syms.kinds[s as usize] {
                SymKind::Init(a) if first.direct(a) => match cells.get(&(a.c / CELL)) {
                    Some(Role::Read | Role::Restored) => out.terms.push((a.c / CELL, k)),
                    Some(Role::Induction(_)) if !fixed => out.terms.push((a.c / CELL, k)),
                    _ => return None,
                },
                // (memory that's like a cell, as the cell)
                SymKind::Init(a) if scalars.contains_key(a) => match cells.get(&scalars[a]) {
                    Some(Role::Read | Role::Restored) => out.terms.push((scalars[a], k)),
                    Some(Role::Induction(_)) if !fixed => out.terms.push((scalars[a], k)),
                    _ => return None,
                },
                SymKind::Init(a) if !fixed && readonly.contains(&a.family()) => out.loads.push((lin_of(first, cells, readonly, scalars, a, true)?, k)),
                _ => return None,
            }
        }
        Some(out)
    }
    let cell = |l: &Lin| lin_of(first, cells, readonly, scalars, l, false);
    let x = cell(&x)?;
    if !x.terms.iter().any(|(o, _)| matches!(cells.get(o), Some(Role::Induction(_)))) {
        return None;
    }
    let parts = parts.iter().map(|(p, u)| Some((cell(p)?, *u))).collect::<Option<Vec<_>>>()?;
    Some(Trip::Compare { x, parts })
}

/// What a comparison's result says.
#[derive(Clone, Debug)]
enum Pred {
    /// `x > 0`, signed.
    Positive(Lin),
    /// `a < b`, signed or unsigned.
    Less(Lin, Lin, bool),
}

/// An `if` the analysis just ran: the state if it was skipped, if it ran,
/// and after it, and the cells that are a number other than 0 if it was
/// skipped and 0 if it ran.
struct LastIf {
    skip: State,
    taken: State,
    merged: State,
    flags: Vec<Lin>,
    /// What it decided on.
    branch: Option<Lin>,
}

/// What the analysis knows at a point in the iteration.
#[derive(Clone, Debug)]
struct State {
    ptr: Lin,
    acc: Val,
    /// What cells hold, by address, where it's known (anything not here
    /// still holds what it held when the iteration started).
    mem: HashMap<Lin, Val>,
    /// The pointers `*` has saved.
    stack: Vec<Lin>,
}

/// An access to memory during the iteration.
#[derive(Clone, Debug)]
pub struct Access {
    pub addr: Lin,
    pub write: bool,
    /// For a read, whether it read what the cell held when the iteration
    /// started (rather than something the iteration wrote).
    pub exposed: bool,
    /// The op that made it, and the calls it was made in (see `chains`).
    pub op: *const Item,
    pub chain: u32,
    /// For accesses by a loop in the body that's summed up (see
    /// `Interp::summarize`): how far apart its iterations' are, and which
    /// of `Interp::inners` says how many there are. It accesses `addr` and
    /// then that much further each time, that many times more.
    pub inner: Option<(Lin, usize)>,
}

/// How many times a loop in the body runs (but for the last time, which
/// leaves it), as worked out when it starts: for `x0 + xs k` with `exact`,
/// the `k` where that's 0; otherwise the first `k` where it isn't above 0.
/// What's compared, `parts` (each where it starts, how much it gains each
/// time, and whether it's unsigned), mustn't wrap round over those.
#[derive(Clone, Debug)]
pub struct InnerTrip {
    pub x0: Lin,
    pub xs: Lin,
    pub exact: bool,
    pub parts: Vec<(Lin, Lin, bool)>,
}

struct Interp<'a> {
    syms: Syms,
    funcs: &'a HashMap<String, &'a [Item]>,
    /// The functions the target does natively, which cost little, however
    /// many ops they have.
    cheap: &'a HashSet<String>,
    /// What the functions done natively may do, in place of running them.
    summaries: &'a HashMap<String, Summary>,
    inlining: Vec<String>,
    /// Whether a cell near the pointer is accessed through a pointer (after a
    /// `*`).
    through: bool,
    /// The op running, and the calls (the ops that made them) it's in, by
    /// number.
    op: *const Item,
    calls: Vec<*const Item>,
    chains: HashMap<Vec<*const Item>, u32>,
    chain: u32,
    /// About how many ops an iteration runs (with the functions done
    /// natively counted as a few), and how many the analysis has.
    steps: usize,
    spent: usize,
    accesses: Vec<Access>,
    /// The counts of the loops in the body that are summed up (see
    /// `Access::inner`), and the families of memory they write (from then
    /// on, what's there isn't known), with what that depends on.
    inners: Vec<InnerTrip>,
    /// Whether each loop body seen so far writes memory (see
    /// `writes_memory`).
    writes: HashMap<*const Item, bool>,
    clobbered: BTreeSet<Lin>,
    clobber_deps: BTreeSet<Sym>,
    /// Values stored outside the cells near the pointer, with where.
    stored: Vec<(Lin, Val)>,
    /// What every value read from memory depended on.
    loaded: BTreeSet<Sym>,
    /// What every branch inside the iteration depended on.
    control: Vec<BTreeSet<Sym>>,
    effects: Vec<Effects>,
    /// The body item being run (`None` inside nested code's own items is
    /// still attributed to the body item that contains it).
    top: usize,
    /// Whether the code running is inside something nested in the body
    /// item, so its writes aren't certain.
    nested: usize,
    p0: Sym,
    /// What the cells hold at the end of the iteration, and acc.
    end: HashMap<Lin, Val>,
    end_acc: Val,
    /// Values known not to be 0, when the iteration is one after which the
    /// loop goes round again: what it leaves in acc, and what that implies.
    assume: Vec<Lin>,
    /// Whether an assumption decided a branch.
    assumed: bool,
    /// The branches assumptions decided: the body item each was in, whether
    /// it was that item itself, and the value.
    decided: BTreeSet<(usize, bool, Lin)>,
    /// How many symbols there were when one first did: the assumptions are
    /// in the first run's symbols, which this run's only are the same as up
    /// to there.
    diverged: Option<usize>,
    /// The `if` just run, for an `else` right after it.
    last_if: Option<LastIf>,
    /// What the symbols that are comparisons' results compare (each is 1 if
    /// it holds and 0 if not), and the symbols that aren't 0 just when
    /// something else isn't.
    preds: HashMap<Sym, Pred>,
    equiv: HashMap<Sym, (Lin, i64)>,
    /// For a value an `if` and its `else` made: what the `if` decided on,
    /// and what it is if that isn't 0, and if it is.
    selects: HashMap<Sym, (Lin, Lin, Lin)>,
    /// For a symbol an `if` made of what a cell held if it ran and if it
    /// didn't (with nothing in common): what it decided on, and those.
    ifs: HashMap<Sym, (Lin, Lin, Lin)>,
    /// The addresses of memory that's like a cell, with their keys in
    /// `cells` (see `Plan::scalars`).
    scalar_at: HashMap<Lin, i64>,
    /// For a value an `if` made by joining its paths, the condition it
    /// implies isn't 0 if it isn't (the path that skips leaves it 0, or the
    /// condition itself, which is 0 on that path).
    implies: HashMap<Sym, Lin>,
}

type R<T> = Result<T, String>;

impl Interp<'_> {
    /// What the iteration leaves in acc.
    fn end_acc(&self) -> Val {
        self.end_acc.clone()
    }

    fn direct(&self, addr: &Lin) -> bool {
        addr.terms.len() == 1 && addr.terms.get(&self.p0) == Some(&1)
    }

    fn effect_read(&mut self, l: Loc) {
        self.effects[self.top].reads.push(l);
    }

    fn effect_write(&mut self, l: Loc) {
        let definite = self.nested == 0;
        self.effects[self.top].writes.push((l, definite));
    }

    fn load(&mut self, s: &mut State, addr: Lin) -> Val {
        self.effect_read(Loc::Mem(addr.clone()));
        self.through |= !s.stack.is_empty() && self.direct(&addr);
        if let Some(v) = s.mem.get(&addr) {
            self.accesses.push(Access { addr, write: false, exposed: false, op: self.op, chain: self.chain, inner: None });
            self.loaded.extend(self.syms.deps(v));
            return v.clone();
        }
        // (not kept in `s.mem`: reading doesn't change what's there, and the
        // symbol for what the cell held is the same each time it's read)
        // (but memory a loop in the body summed up may have written holds
        // something not known)
        if self.clobbered.contains(&addr.family()) && !self.direct(&addr) {
            let v = Val::Lin(Lin::sym(self.syms.fresh(addr.terms.keys().copied().chain(self.clobber_deps.iter().copied()).collect())));
            self.accesses.push(Access { addr, write: false, exposed: false, op: self.op, chain: self.chain, inner: None });
            return v;
        }
        let v = Val::Lin(Lin::sym(self.syms.get(SymKind::Init(addr.clone()))));
        self.accesses.push(Access { addr, write: false, exposed: true, op: self.op, chain: self.chain, inner: None });
        self.loaded.extend(self.syms.deps(&v));
        v
    }

    fn store(&mut self, s: &mut State, addr: Lin, v: Val) {
        self.effect_write(Loc::Mem(addr.clone()));
        self.through |= !s.stack.is_empty() && self.direct(&addr);
        if !self.direct(&addr) {
            self.stored.push((addr.clone(), v.clone()));
        }
        s.mem.insert(addr.clone(), v);
        self.accesses.push(Access { addr, write: true, exposed: false, op: self.op, chain: self.chain, inner: None });
    }

    /// Counts work towards the budget that isn't an op (copying and joining
    /// states takes as long as they're big).
    fn charge(&mut self, work: usize) -> R<()> {
        self.spent += work / 4;
        if self.spent > BUDGET {
            return Err("too much to analyze".into());
        }
        Ok(())
    }

    fn lin(&self, v: &Val) -> R<Lin> {
        match v {
            Val::Lin(l) => Ok(l.clone()),
            Val::Func(_) => Err("arithmetic on a function's address".into()),
        }
    }

    /// Whether acc is known to be zero or not.
    fn truth(v: &Val) -> Option<bool> {
        match v {
            Val::Lin(l) => l.as_const().map(|c| c != 0),
            Val::Func(_) => Some(true),
        }
    }

    /// What two paths' states leave: what they agree on, and new symbols for
    /// what they don't (made from both, and from what the branch depended
    /// on).
    /// `a` is the state of the path that skips an `if` (when its condition
    /// is `branch`, if it's an `if`), and `b` the other's.
    fn join_if(&mut self, a: &State, b: &State, cond: &BTreeSet<Sym>, branch: Option<&Lin>) -> R<State> {
        self.charge(a.mem.len() + b.mem.len())?;
        if a.ptr != b.ptr || a.stack != b.stack {
            return Err("an if or a loop that moves the pointer".into());
        }
        let implies = std::cell::RefCell::new(vec![]);
        let equiv = std::cell::RefCell::new(vec![]);
        let ifs = std::cell::RefCell::new(vec![]);
        let merge = |x: &Val, y: &Val, syms: &mut Syms| -> Val {
            if x == y {
                return x.clone();
            }
            // what the paths have in common (the same symbols, as much of
            // each) stays, and the rest is a new symbol: `h` or `h + 1` is
            // `h + f`, with `f` 0 or 1 by the branch
            let common = match (x, y, branch) {
                (Val::Lin(a), _, Some(c)) if a == c => Lin::default(),
                (Val::Lin(a), Val::Lin(b), _) => Lin { c: 0, terms: a.terms.iter().filter(|(s, k)| b.terms.get(s) == Some(k)).map(|(&s, &k)| (s, k)).collect() },
                _ => Lin::default(),
            };
            let mut from = cond.clone();
            for v in [x, y] {
                match v {
                    Val::Lin(l) => from.extend(l.sub(&common).terms.keys()),
                    Val::Func(_) => {}
                }
            }
            let f = syms.fresh(from);
            if let (Some(c), Val::Lin(skip), Val::Lin(taken), true) = (branch, x, y, common == Lin::default()) {
                ifs.borrow_mut().push((f, (c.clone(), taken.clone(), skip.clone())));
            }
            if let (Some(c), Val::Lin(skip)) = (branch, x) {
                if *skip == Lin::constant(0) || skip == c {
                    implies.borrow_mut().push((f, c.clone()));
                }
                // (0 if skipped, a number other than 0 if not: it's not 0 just
                // when the condition isn't)
                if let (true, Val::Lin(t), true) = (*skip == Lin::constant(0), y, common == Lin::default()) {
                    if let Some(k) = t.as_const().filter(|&k| k != 0) {
                        equiv.borrow_mut().push((f, (c.clone(), k)));
                    }
                }
            }
            Val::Lin(common.add(&Lin::sym(f)))
        };
        let acc = merge(&a.acc, &b.acc, &mut self.syms);
        let mut mem = HashMap::default();
        // (in order, so the symbols made are numbered the same every time)
        let keys: BTreeSet<&Lin> = a.mem.keys().chain(b.mem.keys()).collect();
        for k in keys {
            let clobbered = self.clobbered.contains(&k.family()) && !self.direct(k);
            let deps = &self.clobber_deps;
            let init = |syms: &mut Syms| Val::Lin(Lin::sym(if clobbered { syms.fresh(k.terms.keys().copied().chain(deps.iter().copied()).collect()) } else { syms.get(SymKind::Init(k.clone())) }));
            let x = a.mem.get(k).cloned().unwrap_or_else(|| init(&mut self.syms));
            let y = b.mem.get(k).cloned().unwrap_or_else(|| init(&mut self.syms));
            let v = merge(&x, &y, &mut self.syms);
            mem.insert(k.clone(), v);
        }
        self.implies.extend(implies.into_inner());
        self.equiv.extend(equiv.into_inner());
        self.ifs.extend(ifs.into_inner());
        Ok(State { ptr: a.ptr.clone(), acc, mem, stack: a.stack.clone() })
    }

    fn items(&mut self, items: &[Item], s: &mut State, body: bool) -> R<()> {
        for (i, item) in items.iter().enumerate() {
            if body {
                self.top = i;
            }
            self.steps += 1;
            self.spent += 1;
            if self.spent > BUDGET {
                return Err("too much to analyze".into());
            }
            match item {
                Item::Op(op) => {
                    self.op = item;
                    self.op(*op, s)?
                }
                Item::Loop(inner) => self.inner_loop(inner, s)?,
                Item::Func(..) => return Err("a function defined inside a loop".into()),
            }
        }
        Ok(())
    }

    fn op(&mut self, op: Op, s: &mut State) -> R<()> {
        match op {
            Op::Move(n) => s.ptr = s.ptr.add(&Lin::constant(n.wrapping_mul(CELL))),
            Op::Set(n) => {
                s.acc = Val::Lin(Lin::constant(n as i64));
                self.effect_write(Loc::Acc);
            }
            Op::Label(l) => {
                s.acc = Val::Func(super::label_name(&l));
                self.effect_write(Loc::Acc);
            }
            Op::Load => {
                s.acc = self.load(s, s.ptr.clone());
                self.effect_write(Loc::Acc);
            }
            Op::Store => {
                self.effect_read(Loc::Acc);
                let (p, v) = (s.ptr.clone(), s.acc.clone());
                self.store(s, p, v);
            }
            Op::Add => {
                self.effect_read(Loc::Acc);
                let x = self.load(s, s.ptr.clone());
                let (a, x) = (self.lin(&s.acc)?, self.lin(&x)?);
                s.acc = Val::Lin(a.add(&x));
                self.effect_write(Loc::Acc);
            }
            Op::Neg => {
                self.effect_read(Loc::Acc);
                s.acc = Val::Lin(self.lin(&s.acc)?.scale(-1));
                self.effect_write(Loc::Acc);
            }
            Op::Positive => {
                self.effect_read(Loc::Acc);
                let a = self.lin(&s.acc)?;
                s.acc = Val::Lin(match a.as_const() {
                    Some(c) => Lin::constant((c > 0) as i64),
                    None => {
                        let from = a.terms.keys().copied().collect();
                        let f = self.syms.fresh(from);
                        self.preds.insert(f, Pred::Positive(a));
                        Lin::sym(f)
                    }
                });
                self.effect_write(Loc::Acc);
            }
            Op::Where => {
                s.acc = Val::Lin(s.ptr.clone());
                self.effect_write(Loc::Acc);
            }
            Op::Deref => {
                let v = self.load(s, s.ptr.clone());
                let to = self.lin(&v)?;
                s.stack.push(s.ptr.clone());
                s.ptr = to;
            }
            Op::Refer => match s.stack.pop() {
                Some(p) => s.ptr = p,
                None => return Err("a `&` without its `*`".into()),
            },
            Op::Call => {
                self.effect_read(Loc::Acc);
                let Val::Func(name) = s.acc.clone() else { return Err("a call through an address that isn't known".into()) };
                if let Some(sum) = self.summaries.get(&name) {
                    // what it reads (from where the pointer is), and acc, make
                    // what it writes (with what was there, unless it surely
                    // writes it)
                    let mut from: BTreeSet<Sym> = self.syms.deps(&s.acc);
                    for &r in &sum.reads {
                        let v = self.load(s, s.ptr.add(&Lin::constant(r * CELL)));
                        from.extend(self.syms.deps(&v));
                    }
                    for (&w, &sure) in &sum.writes {
                        let addr = s.ptr.add(&Lin::constant(w * CELL));
                        let mut made = from.clone();
                        if !sure {
                            match s.mem.get(&addr) {
                                Some(old) => made.extend(self.syms.deps(old)),
                                None => {
                                    made.insert(self.syms.get(SymKind::Init(addr.clone())));
                                }
                            }
                        }
                        let v = Val::Lin(Lin::sym(self.syms.fresh(made)));
                        self.nested += usize::from(!sure);
                        self.store(s, addr, v);
                        self.nested -= usize::from(!sure);
                    }
                    let f = self.syms.fresh(from);
                    s.acc = Val::Lin(Lin::sym(f));
                    // (what the comparisons leave in acc is what they compare)
                    if name == "rt_less" || name == "rt_lessu" {
                        let at = |off: i64, s: &State, syms: &mut Syms| match s.mem.get(&s.ptr.add(&Lin::constant(off * CELL))) {
                            Some(Val::Lin(l)) => Some(l.clone()),
                            Some(Val::Func(_)) => None,
                            None => Some(Lin::sym(syms.get(SymKind::Init(s.ptr.add(&Lin::constant(off * CELL)))))),
                        };
                        // (what it was given, if it doesn't write them)
                        if let (false, Some(a), Some(b)) = (sum.writes.contains_key(&13) || sum.writes.contains_key(&14), at(13, s, &mut self.syms), at(14, s, &mut self.syms)) {
                            self.preds.insert(f, Pred::Less(a, b, name == "rt_lessu"));
                        }
                    }
                    self.steps += 20;
                    self.spent += 20;
                    self.effect_write(Loc::Acc);
                    return Ok(());
                }
                let Some(&body) = self.funcs.get(&name) else { return Err(format!("a call to `{name}`, outside the program")) };
                if self.inlining.contains(&name) {
                    return Err(format!("a recursive call to `{name}`"));
                }
                let (before, cheap) = (self.steps, self.cheap.contains(&name));
                self.inlining.push(name);
                self.nested += 1;
                let outer = self.chain;
                self.calls.push(self.op);
                let n = self.chains.len() as u32;
                self.chain = *self.chains.entry(self.calls.clone()).or_insert(n);
                self.items(body, s, false)?;
                self.calls.pop();
                self.chain = outer;
                self.nested -= 1;
                self.inlining.pop();
                if cheap {
                    self.steps = before + 20;
                }
                self.effect_write(Loc::Acc);
            }
            Op::Read | Op::Write => return Err("input or output".into()),
            Op::While | Op::EndWhile | Op::Func | Op::EndFunc => unreachable!("structured"),
        }
        Ok(())
    }

    /// What `l`, in the symbols of the analysis of a loop in the body
    /// (`plan`), starting from `s`, is in this one's, if it can tell.
    fn translate(&mut self, plan: &Plan, s: &State, l: &Lin) -> Option<Lin> {
        let mut out = Lin::constant(l.c);
        for (&sym, &k) in &l.terms {
            let v = match &plan.syms.kinds[sym as usize] {
                SymKind::P0 => s.ptr.clone(),
                SymKind::Acc0 => match &s.acc {
                    Val::Lin(a) => a.clone(),
                    Val::Func(_) => return None,
                },
                SymKind::Init(a) => {
                    let at = match a.terms.iter().collect::<Vec<_>>()[..] {
                        [(&p, &1)] if p == plan.p0 => s.ptr.add(&Lin::constant(a.c)),
                        _ => self.translate(plan, s, a)?,
                    };
                    match s.mem.get(&at) {
                        Some(Val::Lin(v)) => v.clone(),
                        Some(Val::Func(_)) => return None,
                        None if self.clobbered.contains(&at.family()) && !self.direct(&at) => return None,
                        None => Lin::sym(self.syms.get(SymKind::Init(at))),
                    }
                }
                SymKind::Fresh(_) => return None,
            };
            out = out.add(&v.scale(k));
        }
        Some(out)
    }

    /// How much `l` (in `plan`'s symbols) gains each time round the loop
    /// `plan` is of, in this analysis's symbols.
    fn translate_stride(&mut self, plan: &Plan, s: &State, l: &Lin) -> Option<Lin> {
        let mut st = Lin::default();
        for (&sym, &k) in &l.terms {
            if let Some(step) = plan.step(sym) {
                st = st.add(&step.scale(k));
            }
        }
        self.translate(plan, s, &st)
    }

    /// For a loop in the body that can't be followed a time round at a
    /// time: what it does, from its own analysis, if that works and says how
    /// many times it runs. Every cell it writes holds something not known
    /// after it (made from what it started from), and it accesses each of
    /// its families of memory over a range, once for each time round
    /// (`Access::inner`); what's in memory it writes isn't known after it.
    /// Gives whether it could.
    /// Whether `items` (with `depth` `*`s in effect) may store to memory
    /// through a pointer (in the functions it calls too).
    fn writes_memory(&self, items: &[Item], depth: usize, inlining: &mut Vec<String>) -> bool {
        writes_memory(self.funcs, items, depth, inlining)
    }

    /// `ran`, if it's known, is what a few times round from `s` left. If it
    /// can't, it leaves everything as it was.
    fn summarize(&mut self, body: &[Item], s: &mut State, ran: Option<&State>) -> R<bool> {
        let before = (self.accesses.len(), self.stored.len(), self.control.len(), self.loaded.clone(), self.inners.len());
        let mut tried = s.clone();
        if self.summarize_in(body, &mut tried, ran)? {
            *s = tried;
            return Ok(true);
        }
        self.accesses.truncate(before.0);
        self.stored.truncate(before.1);
        self.control.truncate(before.2);
        self.loaded = before.3;
        self.inners.truncate(before.4);
        Ok(false)
    }

    fn summarize_in(&mut self, body: &[Item], s: &mut State, ran: Option<&State>) -> R<bool> {
        if DEPTH.get() >= 2 || !SUMMING.get() {
            return Ok(false);
        }
        // (with its accesses all the iterations', the last's too; and what
        // reads might read a copy of memory reads it as it goes, as the loop
        // runs in order here)
        let plan = match INNER.with(|c| c.borrow().get(&body.as_ptr()).cloned()) {
            Some(p) => p,
            None => {
                DEPTH.set(DEPTH.get() + 1);
                let p = std::rc::Rc::new(analyze(body, self.funcs, self.cheap, self.summaries));
                DEPTH.set(DEPTH.get() - 1);
                INNER.with(|c| c.borrow_mut().insert(body.as_ptr(), p.clone()));
                p
            }
        };
        let Ok(plan) = &*plan else { return Ok(false) };
        if plan.assumed || !plan.private.is_empty() || !plan.gathers.is_empty() || plan.through {
            return Ok(false);
        }
        // where its cells, and its memory that's like cells, are
        let mut scalar_addr: HashMap<i64, Lin> = HashMap::default();
        for (a, &k) in &plan.scalar_at {
            let Some(at) = self.translate(&plan, s, a) else { return Ok(false) };
            if self.direct(&at) || self.clobbered.contains(&at.family()) {
                return Ok(false);
            }
            scalar_addr.insert(k, at);
        }
        let ptr = s.ptr.clone();
        let loc = |o: i64| if o >= SCALAR { scalar_addr[&o].clone() } else { ptr.add(&Lin::constant(o * CELL)) };
        // how many times it runs
        let cell_value = |me: &mut Interp, s: &State, o: i64| -> Option<Lin> {
            let at = s.ptr.add(&Lin::constant(o * CELL));
            match s.mem.get(&at) {
                Some(Val::Lin(v)) => Some(v.clone()),
                Some(Val::Func(_)) => None,
                None => Some(Lin::sym(me.syms.get(SymKind::Init(at)))),
            }
        };
        fn cell_lin(me: &mut Interp, plan: &Plan, s: &State, c: &CellLin, value: &dyn Fn(&mut Interp, &State, i64) -> Option<Lin>) -> Option<(Lin, Lin)> {
            let (mut v, mut st) = (Lin::constant(c.c), Lin::default());
            for &(o, k) in &c.terms {
                v = v.add(&value(me, s, o)?.scale(k));
                if let Some(Role::Induction(step)) = plan.cells.get(&o) {
                    st = st.add(&me.translate(plan, s, step)?.scale(k));
                }
            }
            for (a, k) in &c.loads {
                let (at, _) = cell_lin(me, plan, s, a, value)?;
                let held = match s.mem.get(&at) {
                    Some(Val::Lin(v)) => v.clone(),
                    Some(Val::Func(_)) => return None,
                    None if me.clobbered.contains(&at.family()) && !me.direct(&at) => return None,
                    None => Lin::sym(me.syms.get(SymKind::Init(at))),
                };
                v = v.add(&held.scale(*k));
            }
            Some((v, st))
        }
        let trip = match &plan.trip {
            Trip::Linear { alpha, beta } => {
                let (Some(x0), Some(xs)) = (self.translate(&plan, s, alpha), self.translate(&plan, s, beta)) else { return Ok(false) };
                InnerTrip { x0, xs, exact: true, parts: vec![] }
            }
            Trip::Compare { x, parts } => {
                let Some((x0, xs)) = cell_lin(self, &plan, s, x, &cell_value) else { return Ok(false) };
                let mut ps = vec![];
                for (p, unsigned) in parts {
                    let Some((p0, pst)) = cell_lin(self, &plan, s, p, &cell_value) else { return Ok(false) };
                    ps.push((p0, pst, *unsigned));
                }
                // (and the induction variables in it)
                for &(o, _) in x.terms.iter().chain(parts.iter().flat_map(|p| p.0.terms.iter())) {
                    if let Some(Role::Induction(step)) = plan.cells.get(&o) {
                        let (Some(v), Some(st)) = (cell_value(self, s, o), self.translate(&plan, s, step)) else { return Ok(false) };
                        ps.push((v, st, false));
                    }
                }
                InnerTrip { x0, xs, exact: false, parts: ps }
            }
            Trip::Slice(_) => return Ok(false),
        };
        // its memory
        let mut families = vec![];
        for f in &plan.shared {
            let (Some(base), Some(st)) = (self.translate(&plan, s, &f.base), self.translate_stride(&plan, s, &f.base)) else { return Ok(false) };
            if self.direct(&base) {
                return Ok(false);
            }
            families.push((base, st, f.offsets.clone()));
        }
        // what it depends on (and, apart, what each cell it reads before
        // writing it held)
        let mut deps: BTreeSet<Sym> = BTreeSet::new();
        let mut own: HashMap<i64, BTreeSet<Sym>> = HashMap::default();
        for l in [&trip.x0, &trip.xs].into_iter().chain(trip.parts.iter().flat_map(|p| [&p.0, &p.1])).chain(families.iter().flat_map(|f| [&f.0, &f.1])) {
            deps.extend(l.terms.keys());
        }
        // (and what's in the cells it uses, which it reads, but for its
        // maximums and what's set with them, which nothing else depends on)
        let special: BTreeSet<i64> = plan.extremes.iter().flat_map(|e| std::iter::once(e.cell).chain(e.with.iter().copied())).collect();
        let mut reads = vec![];
        let mut olds: HashMap<i64, Lin> = HashMap::default();
        for (&o, role) in &plan.cells {
            // (a cell it writes before reading it, it doesn't read)
            let at = loc(o);
            let v = if o >= SCALAR || matches!(role, Role::Private | Role::Maybe) {
                match s.mem.get(&at) {
                    Some(v) => v.clone(),
                    None => Val::Lin(Lin::sym(self.syms.get(SymKind::Init(at)))),
                }
            } else {
                self.load(s, at)
            };
            let Val::Lin(old) = v else { return Ok(false) };
            // (only what it reads before writing it is what it uses)
            if !special.contains(&o) && matches!(role, Role::Read | Role::Restored | Role::Induction(_) | Role::Reduction) {
                own.insert(o, old.terms.keys().copied().collect());
            }
            olds.insert(o, old);
            reads.push((o, role.clone()));
        }
        // (its accesses to memory that's like cells, by its own ops, which
        // stay the same op, and in the same calls, here)
        for ((calls, op), &j) in &plan.scalar_slots {
            let o = SCALAR + j as i64;
            let mut chain = self.calls.clone();
            chain.extend(calls.iter().copied());
            let n = self.chains.len() as u32;
            let chain = *self.chains.entry(chain).or_insert(n);
            let write = !matches!(plan.cells.get(&o), Some(Role::Read | Role::Restored));
            self.accesses.push(Access { addr: scalar_addr[&o].clone(), write, exposed: false, op: *op, chain, inner: None });
        }
        let inputs = deps.clone();
        for d in own.values() {
            deps.extend(d.iter().copied());
        }
        self.control.push(trip.x0.terms.keys().chain(trip.xs.terms.keys()).copied().collect());
        let n = self.inners.len();
        self.inners.push(trip);
        for (base, st, offsets) in families {
            for (&off, &written) in &offsets {
                let addr = base.add(&Lin::constant(off));
                if written {
                    let v = Val::Lin(Lin::sym(self.syms.fresh(deps.clone())));
                    self.stored.push((addr.clone(), v));
                }
                self.accesses.push(Access { addr, write: written, exposed: false, op: std::ptr::null(), chain: self.chain, inner: Some((st.clone(), n)) });
            }
            if offsets.values().any(|&w| w) {
                let fam = base.family();
                s.mem.retain(|k, _| k.family() != fam);
                self.clobbered.insert(fam);
                self.clobber_deps.extend(deps.iter().copied());
            }
        }
        // its cells: its maximums (and what's set with them) as an `if` that
        // sets them to what it found, just when that's more, and the rest to
        // something not known (made from everything, those too)
        let mut all = deps.clone();
        for o in &special {
            all.extend(olds[o].terms.keys());
        }
        let mut after: HashMap<i64, Lin> = HashMap::default();
        for e in &plan.extremes {
            let held = olds[&e.cell].clone();
            let found = Lin::sym(self.syms.fresh(deps.clone()));
            let t = self.syms.fresh(deps.iter().copied().chain(held.terms.keys().copied()).collect());
            let (a, b, negated) = match (e.max, e.strict) {
                (true, true) => (held.clone(), found.clone(), false),
                (false, true) => (found.clone(), held.clone(), false),
                (true, false) => (found.clone(), held.clone(), true),
                (false, false) => (held.clone(), found.clone(), true),
            };
            self.preds.insert(t, Pred::Less(a, b, e.unsigned));
            let branch = if negated { Lin::constant(1).sub(&Lin::sym(t)) } else { Lin::sym(t) };
            let mut set = vec![(e.cell, found)];
            for &o in &e.with {
                set.push((o, Lin::sym(self.syms.fresh(deps.clone()))));
            }
            for (o, taken) in set {
                let skipped = olds[&o].clone();
                let f = self.syms.fresh(all.iter().copied().chain([t]).chain(taken.terms.keys().copied()).collect());
                self.ifs.insert(f, (branch.clone(), taken, skipped));
                after.insert(o, Lin::sym(f));
            }
        }
        for (o, role) in reads {
            if matches!(role, Role::Read | Role::Restored) {
                continue;
            }
            // (what only some times round write may be what was there; and
            // what it only adds to is what was there and the sum, made from
            // everything else)
            // (unless the first few times round left something that isn't
            // made from it, so they wrote it)
            let mut made = all.clone();
            if role == Role::Maybe {
                let overwritten = ran.is_some_and(|r| match r.mem.get(&loc(o)) {
                    Some(Val::Lin(l)) => !self.syms.closure(l.terms.keys().copied()).iter().any(|t| olds[&o].terms.contains_key(t)),
                    _ => false,
                });
                if !overwritten {
                    made.extend(olds[&o].terms.keys());
                }
            }
            let v = match after.remove(&o) {
                Some(v) => v,
                None if role == Role::Reduction && !special.contains(&o) => {
                    let mut rest = inputs.clone();
                    for (k, d) in &own {
                        if *k != o {
                            rest.extend(d.iter().copied());
                        }
                    }
                    for k in &special {
                        rest.extend(olds[k].terms.keys());
                    }
                    olds[&o].add(&Lin::sym(self.syms.fresh(rest)))
                }
                None => Lin::sym(self.syms.fresh(made)),
            };
            let v = Val::Lin(v);
            let at = loc(o);
            if o >= SCALAR {
                self.stored.push((at.clone(), v.clone()));
                s.mem.insert(at, v);
            } else {
                self.store(s, at, v);
            }
        }
        s.acc = Val::Lin(Lin::constant(0));
        #[cfg(test)]
        SUMMED.fetch_add(1, std::sync::atomic::Ordering::Relaxed);
        Ok(true)
    }

    fn inner_loop(&mut self, body: &[Item], s: &mut State) -> R<()> {
        self.effect_read(Loc::Acc);
        self.nested += 1;
        // an `else`: right after an `if`, a loop on a flag the `if` left 1 if
        // it was skipped and 0 if it ran, runs just when it was skipped
        if let Some(last) = self.last_if.take() {
            let flag = last.flags.iter().find(|f| last.merged.mem.get(f) == Some(&s.acc)).cloned();
            if let (Some(f), true) = (flag, s.mem == last.merged.mem && s.ptr == last.merged.ptr && s.stack == last.merged.stack) {
                let cond = self.syms.deps(&s.acc);
                self.control.push(cond.clone());
                self.charge(last.skip.mem.len() + last.taken.mem.len())?;
                let mut ran = last.skip.clone();
                ran.acc = ran.mem.get(&f).cloned().unwrap_or_else(|| Val::Lin(Lin::sym(self.syms.get(SymKind::Init(f.clone())))));
                self.items(body, &mut ran, false)?;
                if Self::truth(&ran.acc) == Some(false) && ran.ptr == s.ptr && ran.stack == s.stack {
                    let mut skipped = last.taken.clone();
                    skipped.acc = Val::Lin(Lin::constant(0));
                    *s = self.join_if(&skipped, &ran, &cond, None)?;
                    // (what each value it made is, by what the `if` decided)
                    if let Some(b) = &last.branch {
                        let mut picks = vec![];
                        if let Val::Lin(l) = &s.acc {
                            picks.push((l.clone(), skipped.acc.clone(), ran.acc.clone()));
                        }
                        for (k, v) in &s.mem {
                            if let Val::Lin(l) = v {
                                let get = |st: &State| st.mem.get(k).cloned();
                                if let (Some(x), Some(y)) = (get(&skipped), get(&ran)) {
                                    picks.push((l.clone(), x, y));
                                }
                            }
                        }
                        for (l, x, y) in picks {
                            let terms: Vec<(&Sym, &i64)> = l.terms.iter().collect();
                            if let (&[(&f, &1)], 0, Val::Lin(x), Val::Lin(y)) = (&terms[..], l.c, x, y) {
                                if self.syms.made_from.contains_key(&f) && !self.selects.contains_key(&f) {
                                    self.selects.insert(f, (b.clone(), x, y));
                                }
                            }
                        }
                    }
                    s.acc = Val::Lin(Lin::constant(0));
                    self.nested -= 1;
                    self.effect_write(Loc::Acc);
                    return Ok(());
                }
            }
        }
        let mut rounds = 0;
        let started = self.spent;
        // (where it started, and what had been found by then, to sum it up
        // from there instead if it runs many times)
        // (only for one that writes memory, which is the kind that's summed
        // up)
        let writes = match self.writes.get(&body.as_ptr()) {
            Some(&w) => w,
            None => {
                let w = self.writes_memory(body, 0, &mut vec![]);
                self.writes.insert(body.as_ptr(), w);
                w
            }
        };
        let entry = writes.then(|| (s.clone(), self.accesses.len(), self.stored.len(), self.control.len(), self.loaded.clone()));
        loop {
            let valid = |l: &Lin, diverged: Option<usize>| diverged.is_none_or(|n| l.terms.keys().all(|&t| (t as usize) < n));
            let assumed = matches!(&s.acc, Val::Lin(l) if self.assume.iter().any(|a| a == l && valid(a, self.diverged))) && Self::truth(&s.acc).is_none();
            if assumed && !self.assumed {
                self.assumed = true;
                self.diverged = Some(self.syms.kinds.len());
            }
            if let (true, Val::Lin(l)) = (assumed, &s.acc) {
                self.decided.insert((self.top, self.nested == 1, l.clone()));
            }
            // (past as many times round as are worth following one at a
            // time, what holds however many more it goes)
            // (past as many as are worth following one at a time, what its own
            // analysis finds it does, from where it started, if it can tell:
            // for one that writes memory, which following it one at a time
            // can't tell after it, sooner)
            if let (Some(true), Some(entry), true, false) = (Self::truth(&s.acc), &entry, rounds > 0, assumed) {
                #[cfg(test)]
                let early = SUM_UP_EARLY.load(std::sync::atomic::Ordering::Relaxed);
                #[cfg(not(test))]
                let early = false;
                if early || rounds > UNROLL || self.spent - started > UNROLL_WORK / 10 {
                let (accesses, stored, control) = (self.accesses.split_off(entry.1), self.stored.split_off(entry.2), self.control.split_off(entry.3));
                let loaded = std::mem::replace(&mut self.loaded, entry.4.clone());
                let mut from = entry.0.clone();
                if self.summarize(body, &mut from, Some(s))? {
                    *s = from;
                    break;
                }
                self.accesses.extend(accesses);
                self.stored.extend(stored);
                self.control.extend(control);
                self.loaded.extend(loaded);
                }
            }
            let known = match Self::truth(&s.acc) {
                Some(true) if rounds > UNROLL || self.spent - started > UNROLL_WORK => None,
                None if assumed && rounds <= UNROLL => Some(true),
                t => t,
            };
            match known {
                Some(false) => break,
                Some(true) => {
                    // a known count, so far: go round
                    let (ptr, depth) = (s.ptr.clone(), s.stack.len());
                    self.items(body, s, false)?;
                    if s.ptr != ptr || s.stack.len() != depth {
                        return Err("a loop that moves the pointer".into());
                    }
                    rounds += 1;
                }
                None => {
                    let cond = self.syms.deps(&s.acc);
                    self.control.push(cond.clone());
                    let branch = match &s.acc {
                        Val::Lin(l) => Some(l.clone()),
                        Val::Func(_) => None,
                    };
                    // run it once: if that always leaves acc 0, it's an `if`
                    self.charge(s.mem.len())?;
                    let mut once = s.clone();
                    self.items(body, &mut once, false)?;
                    if Self::truth(&once.acc) == Some(false) {
                        let merged = self.join_if(s, &once, &cond, branch.as_ref())?;
                        // (the cells that tell whether it ran, for an `else`)
                        let flags: Vec<Lin> = once
                            .mem
                            .iter()
                            .filter(|(a, v)| **v == Val::Lin(Lin::constant(0)) && matches!(s.mem.get(*a), Some(Val::Lin(l)) if l.as_const().is_some_and(|c| c != 0)))
                            .map(|(a, _)| a.clone())
                            .collect();
                        let skip = std::mem::replace(s, merged);
                        s.acc = Val::Lin(Lin::constant(0));
                        if !flags.is_empty() {
                            self.charge(skip.mem.len() + once.mem.len())?;
                            self.last_if = Some(LastIf { skip, taken: once, merged: s.clone(), flags, branch: branch.clone() });
                            self.nested -= 1;
                            self.effect_write(Loc::Acc);
                            return Ok(());
                        }
                        break;
                    }
                    // otherwise, what its own analysis finds it does, if it can
                    // tell
                    if writes && self.summarize(body, s, None)? {
                        break;
                    }
                    // otherwise, what holds however many times it runs: the
                    // cells that change become new symbols, until no more do.
                    // Each is made from what the cell held before the loop
                    // (it may not run at all), what the body leaves in it
                    // (from the others' symbols, and its own), and what
                    // decides how many times it runs. A cell the body only
                    // adds to (something that doesn't depend on it) is what
                    // it held before plus a new symbol, the sum of what was
                    // added, made from what that was made from.
                    let mut varying: BTreeSet<Option<Lin>> = BTreeSet::new();
                    let mut plain: BTreeSet<Option<Lin>> = BTreeSet::from([None]);
                    let differs = |a: &State, b: &State, varying: &mut BTreeSet<Option<Lin>>| {
                        let mut grew = false;
                        if a.acc != b.acc {
                            grew |= varying.insert(None);
                        }
                        for (k, v) in &b.mem {
                            if a.mem.get(k) != Some(v) {
                                grew |= varying.insert(Some(k.clone()));
                            }
                        }
                        grew
                    };
                    differs(s, &once, &mut varying);
                    let mut rounds = 0;
                    let head = loop {
                        rounds += 1;
                        if rounds > 16 {
                            return Err("a loop whose effect doesn't settle".into());
                        }
                        if once.ptr != s.ptr || once.stack != s.stack {
                            return Err("a loop that moves the pointer".into());
                        }
                        self.charge(2 * s.mem.len())?;
                        let mut head = s.clone();
                        let mut made = vec![];
                        let init = |syms: &mut Syms, st: &State, k: &Option<Lin>| match k {
                            None => st.acc.clone(),
                            Some(a) => st.mem.get(a).cloned().unwrap_or_else(|| Val::Lin(Lin::sym(syms.get(SymKind::Init(a.clone()))))),
                        };
                        for k in &varying {
                            let f = self.syms.fresh(BTreeSet::new());
                            let before = init(&mut self.syms, s, k);
                            let sum = match &before {
                                Val::Lin(b) if !plain.contains(k) => Some(b.clone()),
                                _ => None,
                            };
                            let v = Val::Lin(match &sum {
                                Some(b) => b.add(&Lin::sym(f)),
                                None => Lin::sym(f),
                            });
                            made.push((k.clone(), f, sum.is_some()));
                            match k {
                                None => head.acc = v,
                                Some(addr) => {
                                    head.mem.insert(addr.clone(), v);
                                }
                            }
                        }
                        self.control.push(self.syms.deps(&head.acc));
                        let mut again = head.clone();
                        self.items(body, &mut again, false)?;
                        if again.ptr != head.ptr || again.stack != head.stack {
                            return Err("a loop that moves the pointer".into());
                        }
                        let count: BTreeSet<Sym> = self.syms.deps(&head.acc);
                        let mut demoted = false;
                        for (k, f, sum) in &made {
                            let mut from = cond.clone();
                            from.extend(&count);
                            let after = init(&mut self.syms, &again, k);
                            if *sum {
                                // what one pass adds, which mustn't depend on the
                                // sum so far
                                let added = match (&after, &head.mem[k.as_ref().unwrap()]) {
                                    (Val::Lin(a), Val::Lin(h)) => Some(a.sub(h)),
                                    _ => None,
                                };
                                match added {
                                    Some(d) if !d.terms.contains_key(f) => from.extend(d.terms.keys()),
                                    _ => {
                                        plain.insert(k.clone());
                                        demoted = true;
                                    }
                                }
                            } else {
                                let before = init(&mut self.syms, s, k);
                                from.extend(self.syms.deps(&before));
                                from.extend(self.syms.deps(&after));
                            }
                            self.syms.made_from.insert(*f, from);
                        }
                        if !differs(&head, &again, &mut varying) && !demoted {
                            break head;
                        }
                    };
                    *s = head;
                    s.acc = Val::Lin(Lin::constant(0));
                    break;
                }
            }
        }
        self.nested -= 1;
        self.effect_write(Loc::Acc);
        Ok(())
    }

}

/// What a cell near the pointer is to the loop.
#[derive(Clone, Debug, PartialEq)]
pub enum Role {
    /// It gains this much every time round (over symbols known when the
    /// loop starts).
    Induction(Lin),
    /// It only accumulates: each iteration adds something to it.
    Reduction,
    /// Each iteration leaves it as it found it.
    Restored,
    /// Each iteration writes it before reading it.
    Private,
    /// Never read for what it held when the iteration started, but not
    /// every iteration writes it: what it holds after the iterations is
    /// what the last one that wrote it left (or what it held before them).
    Maybe,
    /// Only read.
    Read,
}

/// How to say which cell (or memory that's like one) `off` is.
fn what(off: i64) -> String {
    if off >= SCALAR { format!("memory {}", off - SCALAR) } else { format!("cell {off}") }
}

/// Where `cells` has memory that's like a cell (see `Plan::scalars`): from
/// this on.
pub const SCALAR: i64 = 1 << 40;

/// Memory that's like a cell: the cell holding the pointer to it (an offset
/// from where the pointer is when the iteration starts), and how far past
/// that it is, in bytes.
#[derive(Clone, Debug)]
pub struct Scalar {
    pub cell: i64,
    pub off: i64,
}

/// A running maximum or minimum: a cell that each iteration either leaves
/// alone or sets to something it compares it with, just when that's more
/// (or less). Each thread can keep its own, from what it held before; the
/// one to keep is the most (or least), and on a tie, the first one's (or,
/// if it's set on a tie too, the last's), with the cells the iterations
/// that set it also set (an index, say).
#[derive(Clone, Debug)]
pub struct Extreme {
    pub cell: i64,
    pub max: bool,
    /// Whether a tie leaves it alone.
    pub strict: bool,
    pub unsigned: bool,
    /// The cells set along with it.
    pub with: Vec<i64>,
    /// Whether cells each iteration sets (before reading them) are worked
    /// out from it: what one thread leaves in them is from what it found,
    /// not what came before it, so the last iteration that goes on can't
    /// run in parallel (it runs after, from what all of them found, and
    /// sets them).
    pub tainted: bool,
}

/// Memory a pointer leads to, accessed at `base + stride * k + offset`.
#[derive(Clone, Debug)]
pub struct Family {
    /// In symbols that are known when the loop starts (with the induction
    /// variables' values for the first iteration).
    pub base: Lin,
    /// The offsets accessed, in bytes, each with whether it's written.
    pub offsets: BTreeMap<i64, bool>,
    /// The offsets only read, that read what later iterations write (and no
    /// earlier one): those read a copy of the memory as it was before the
    /// iterations, which is what they'd find.
    pub later: BTreeSet<i64>,
    /// Whether the ops that read it read nothing else, so that they can read
    /// a copy instead: of all of it, for memory no iteration writes, if
    /// what does write it does so only in later iterations (which the
    /// generated code works out).
    pub copyable: bool,
    /// If a loop in the body (summed up) accesses it: how far apart its
    /// times round access it, and which of `Plan::inners` says how many
    /// there are (each offset is accessed that far on, that many times
    /// more).
    pub inner: Option<(Lin, usize)>,
}

impl Family {
    pub fn written(&self) -> bool {
        self.offsets.values().any(|&w| w)
    }
}

/// How the number of iterations is found.
#[derive(Clone, Debug)]
pub enum Trip {
    /// What acc holds at the end of iteration `k` is `alpha + beta * k`.
    Linear { alpha: Lin, beta: Lin },
    /// By running the body's items marked here, for each `k`.
    Slice(Vec<bool>),
    /// It goes round again while `x > 0`, where `x` is linear in `k`, as long
    /// as none of `parts` (what's compared) wraps round (or, marked, goes
    /// below 0) for the iterations that do.
    Compare { x: CellLin, parts: Vec<(CellLin, bool)> },
}

/// `c + sum(coefficient * cell)`, of cells near the pointer as the
/// iteration starts (as offsets).
#[derive(Clone, Debug)]
pub struct CellLin {
    pub c: i64,
    pub terms: Vec<(i64, i64)>,
    /// `coefficient * what memory holds`, at addresses of this form (of
    /// cells the loop doesn't change), that the loop doesn't write.
    pub loads: Vec<(CellLin, i64)>,
}

/// How to run a loop's iterations in parallel.
#[derive(Debug)]
pub struct Plan {
    pub syms: Syms,
    pub p0: Sym,
    /// The cells near the pointer that the iteration uses, as offsets from
    /// it, with their roles.
    pub cells: BTreeMap<i64, Role>,
    /// Families each thread gets a copy of: the cell holding their base,
    /// and the lowest and highest offsets accessed.
    pub private: Vec<(i64, i64, i64)>,
    /// Families shared by every thread.
    pub shared: Vec<Family>,
    /// The ops that read memory where only the iteration knows (that the
    /// generated code checks).
    pub gathers: HashSet<*const Item>,
    /// For each op (in the calls it's inlined in) that only accesses one cell
    /// of a stack in `private`: which, and the cell (as a byte offset from
    /// the stack's base). Empty unless every access to those stacks is one.
    pub slots: HashMap<(Vec<*const Item>, *const Item), (usize, i64)>,
    /// Memory at addresses that don't change, through pointers in cells the
    /// loop doesn't write, that only ops that always access the same one of
    /// them access: each is like a cell (in `cells`, as `SCALAR` plus which
    /// it is), each thread's own copy. And for each op (in the calls it's
    /// inlined in) that accesses one, which.
    pub scalars: Vec<Scalar>,
    pub scalar_slots: HashMap<(Vec<*const Item>, *const Item), usize>,
    /// Each of those by its address (in the plan's symbols), as its key in
    /// `cells`.
    pub scalar_at: HashMap<Lin, i64>,
    /// The ops that read memory that may be read from a copy of it, as it
    /// was before the iterations (see `Family::later`), and which family.
    pub copied: HashMap<(Vec<*const Item>, *const Item), usize>,
    /// How many times the loops in the body that are summed up run (see
    /// `Family::inner`).
    pub inners: Vec<InnerTrip>,
    /// Whether what it found assumed the iterations go on: then the last
    /// one (which doesn't) may do something else.
    pub assumed: bool,
    /// Whether a cell near the pointer is accessed through a pointer.
    pub through: bool,
    pub trip: Trip,
    /// The bodies of the loops in the body (not in loops in it) that every
    /// iteration that runs in parallel starts.
    pub entered: Vec<*const Item>,
    /// The cells (only some iterations write) that are running maximums or
    /// minimums.
    pub extremes: Vec<Extreme>,
    /// About how many ops an iteration runs.
    pub cost: u64,
}

impl Plan {
    /// The cell an `Init` symbol is of, if it's one near the pointer.
    pub fn cell_of(&self, s: Sym) -> Option<i64> {
        match &self.syms.kinds[s as usize] {
            SymKind::Init(a) if a.terms.len() == 1 && a.terms.get(&self.p0) == Some(&1) => Some(a.c / CELL),
            _ => None,
        }
    }

    /// How much a symbol gains every time round: its step, if it's an
    /// induction variable, and otherwise nothing.
    pub fn step(&self, s: Sym) -> Option<&Lin> {
        match self.cells.get(&self.var_of(s)?) {
            Some(Role::Induction(step)) => Some(step),
            _ => None,
        }
    }

    /// The cell, or memory that's like one (as its key in `cells`), an
    /// `Init` symbol is of.
    pub fn var_of(&self, s: Sym) -> Option<i64> {
        match &self.syms.kinds[s as usize] {
            SymKind::Init(a) => self.cell_of(s).or_else(|| self.scalar_at.get(a).copied()),
            _ => None,
        }
    }
}

/// A function outside the program that `items` call by name (or the
/// functions they call do), if there is one. (Functions with summaries
/// aren't looked into.)
fn calls_outside(funcs: &HashMap<String, &[Item]>, summaries: &HashMap<String, Summary>, items: &[Item], _inlining: &mut Vec<String>) -> Option<String> {
    OUTSIDE.with(|cache| {
        let mut cache = cache.borrow_mut();
        let table = cache.get_or_insert_with(|| outside_calls(funcs, summaries));
        let mut found = None;
        each_call(items, &mut |name| {
            if found.is_none() && !summaries.contains_key(name) {
                found = match table.get(name) {
                    None => Some(name.to_string()),
                    Some(through) => through.clone(),
                };
            }
        });
        found
    })
}

/// The functions each of the program's functions calls by name, in its
/// body and the loops in it (not in functions defined in it).
fn each_call(items: &[Item], f: &mut dyn FnMut(&str)) {
    for (i, item) in items.iter().enumerate() {
        match item {
            Item::Op(Op::Call) => {
                if let Some(name) = super::callee(items, i) {
                    f(&name);
                }
            }
            Item::Loop(body) => each_call(body, f),
            Item::Op(_) | Item::Func(..) => {}
        }
    }
}

/// For each function, a function outside the program it reaches by calls,
/// if it does: what each calls directly, then what it reaches through the
/// functions it calls, over and over until nothing more is found (which
/// takes recursion in its stride).
fn outside_calls(funcs: &HashMap<String, &[Item]>, summaries: &HashMap<String, Summary>) -> HashMap<String, Option<String>> {
    let mut direct: HashMap<String, (Option<String>, Vec<String>)> = HashMap::default();
    for (name, body) in funcs {
        let (mut outside, mut inside) = (None, vec![]);
        each_call(body, &mut |callee| {
            if summaries.contains_key(callee) {
                return;
            }
            if funcs.contains_key(callee) {
                inside.push(callee.to_string());
            } else if outside.is_none() {
                outside = Some(callee.to_string());
            }
        });
        direct.insert(name.clone(), (outside, inside));
    }
    let mut table: HashMap<String, Option<String>> = direct.iter().map(|(name, (outside, _))| (name.clone(), outside.clone())).collect();
    loop {
        let mut changed = false;
        for (name, (_, inside)) in &direct {
            if table[name].is_none() {
                if let Some(found) = inside.iter().find_map(|c| table[c].clone()) {
                    table.insert(name.clone(), Some(found));
                    changed = true;
                }
            }
        }
        if !changed {
            return table;
        }
    }
}

/// Whether `items` (with `depth` `*`s in effect) may store to memory
/// through a pointer (in the functions it calls too).
fn writes_memory(funcs: &HashMap<String, &[Item]>, items: &[Item], mut depth: usize, inlining: &mut Vec<String>) -> bool {
    for (i, item) in items.iter().enumerate() {
        match item {
            Item::Op(Op::Deref) => depth += 1,
            Item::Op(Op::Refer) => depth = depth.saturating_sub(1),
            Item::Op(Op::Store) if depth > 0 => return true,
            Item::Op(Op::Call) => {
                let Some(name) = super::callee(items, i) else { return true };
                if inlining.contains(&name) {
                    continue;
                }
                let Some(body) = funcs.get(&name) else { return true };
                inlining.push(name);
                let w = writes_memory(funcs, body, depth, inlining);
                inlining.pop();
                if w {
                    return true;
                }
            }
            Item::Loop(body) | Item::Func(_, body) => {
                if writes_memory(funcs, body, depth, inlining) {
                    return true;
                }
            }
            Item::Op(_) => {}
        }
    }
    false
}


/// Works out how to run the loop with this body in parallel, or why it
/// can't be.
pub fn analyze(body: &[Item], funcs: &HashMap<String, &[Item]>, cheap: &HashSet<String>, summaries: &HashMap<String, Summary>) -> Result<Plan, String> {
    if DEPTH.get() > 0 {
        return analyze_once(body, funcs, cheap, summaries);
    }
    let start = std::time::Instant::now();
    let plan = analyze_top(body, funcs, cheap, summaries);
    PLANS.with(|p| {
        let (n, ok) = p.get();
        p.set((n + 1, ok + usize::from(plan.is_ok())));
    });
    crate::log!(crate::asm::log::TRACE, "a loop of {} items: {} ({})", body.len(), match &plan { Ok(_) => "parallel".to_string(), Err(why) => why.clone() }, crate::asm::log::show(start.elapsed()));
    plan
}

thread_local! {
    /// How many loops were analyzed, and how many can run in parallel.
    pub static PLANS: std::cell::Cell<(usize, usize)> = const { std::cell::Cell::new((0, 0)) };
}

fn analyze_top(body: &[Item], funcs: &HashMap<String, &[Item]>, cheap: &HashSet<String>, summaries: &HashMap<String, Summary>) -> Result<Plan, String> {
    if DEPTH.get() > 0 {
        return analyze_once(body, funcs, cheap, summaries);
    }
    // (a call to a function outside the program ends the analysis wherever
    // it's reached, so where the body has one, that's known at once, without
    // following everything before it: a game's main loop, say, whose body
    // draws the whole screen and then calls C to show it)
    if let Some(name) = calls_outside(funcs, summaries, body, &mut vec![]) {
        return Err(format!("a call to `{name}`, outside the program"));
    }
    // (following loops in the body a time round at a time, and if that's
    // too much, or doesn't settle, summing them up instead)
    #[cfg(test)]
    let early = SUM_UP_EARLY.load(std::sync::atomic::Ordering::Relaxed);
    #[cfg(not(test))]
    let early = false;
    SUMMING.set(early);
    // (which only matters for loops in the body that write memory)
    let nested = body.iter().any(|i| matches!(i, Item::Loop(b) if writes_memory(funcs, b, 0, &mut vec![])));
    match analyze_once(body, funcs, cheap, summaries) {
        Err(why) if nested && !early => {
            SUMMING.set(true);
            let plan = analyze_once(body, funcs, cheap, summaries);
            SUMMING.set(false);
            plan.map_err(|again| if again == "too much to analyze" { why } else { again })
        }
        plan => plan,
    }
}

fn analyze_once(body: &[Item], funcs: &HashMap<String, &[Item]>, cheap: &HashSet<String>, summaries: &HashMap<String, Summary>) -> Result<Plan, String> {
    let (first, cond) = run(body, funcs, cheap, summaries, vec![])?;
    // the iterations that run in parallel are the ones after which the
    // loop goes round again, so what they leave in acc isn't 0, nor what
    // that implies: knowing that settles the branches that decide on those
    // values (a body guarded by whether the loop goes on, say)
    let mut assume = vec![cond.clone()];
    let mut i = 0;
    while i < assume.len() {
        if let [(&s, &1)] = assume[i].terms.iter().collect::<Vec<_>>()[..] {
            if assume[i].c == 0 {
                if let Some(c) = first.implies.get(&s) {
                    if !assume.contains(c) {
                        assume.push(c.clone());
                    }
                }
            }
        }
        i += 1;
    }
    let second = run(body, funcs, cheap, summaries, assume);
    match second {
        // (if the assumptions decided anything, the runs' symbols differ
        // from there, and what decides whether the loop goes round again
        // comes from the first)
        Ok((again, c)) => {
            let linear = !again.assumed;
            // if the only assumption was what one of the body's own loops
            // starts on (a guard), and with it the iteration always goes on,
            // whether it goes on is what the guard decides
            let guard = match again.decided.iter().collect::<Vec<_>>()[..] {
                [(g, true, c)] if Interp::truth(&again.end_acc()) == Some(true) => Some((*g, c.clone())),
                _ => None,
            };
            // (the body's loops that the assumptions say start)
            let entered: Vec<*const Item> = again
                .decided
                .iter()
                .filter(|d| d.1)
                .filter_map(|d| match &body[d.0] {
                    Item::Loop(inner) => Some(inner.as_ptr()),
                    _ => None,
                })
                .collect();
            // (what the run that assumed nothing accesses, which the last
            // iteration may, the other accesses too, where that can be told:
            // the runs' symbols are the same until it assumed something)
            fn canon(syms: &Syms, l: &Lin) -> Option<String> {
                let mut terms = vec![];
                for (&t, &k) in &l.terms {
                    let what = match &syms.kinds[t as usize] {
                        SymKind::P0 => "P".to_string(),
                        SymKind::Acc0 => "A".to_string(),
                        SymKind::Init(a) => format!("I({})", canon(syms, a)?),
                        SymKind::Fresh(_) => return None,
                    };
                    terms.push(format!("{k}*{what}"));
                }
                terms.sort();
                Some(format!("{}+{}", l.c, terms.join("+")))
            }
            let theirs: BTreeSet<String> = again.accesses.iter().filter_map(|a| canon(&again.syms, &a.addr)).collect();
            let covered = first.accesses.iter().all(|a| canon(&first.syms, &a.addr).is_some_and(|c| theirs.contains(&c)));
            let assumed = (again.assumed || !again.decided.is_empty()) && !covered;
            let mut plan = classify(body, again, c, &first, linear, guard)?;
            plan.entered = entered;
            plan.assumed = assumed;
            Ok(plan)
        }
        Err(_) => {
            let (it, cond) = run(body, funcs, cheap, summaries, vec![])?;
            classify(body, it, cond, &first, true, None)
        }
    }
}

/// Runs one iteration of the loop with this body, from what's there when
/// it starts, giving what it found and what it leaves in acc.
fn run<'a>(body: &[Item], funcs: &'a HashMap<String, &'a [Item]>, cheap: &'a HashSet<String>, summaries: &'a HashMap<String, Summary>, assume: Vec<Lin>) -> R<(Interp<'a>, Lin)> {
    let mut it = Interp {
        syms: Syms::default(),
        funcs,
        cheap,
        summaries,
        inlining: vec![],
        through: false,
        op: std::ptr::null(),
        calls: vec![],
        chains: [(vec![], 0)].into_iter().collect(),
        chain: 0,
        steps: 0,
        spent: 0,
        accesses: vec![],
        inners: vec![],
        writes: HashMap::default(),
        clobbered: BTreeSet::new(),
        clobber_deps: BTreeSet::new(),
        stored: vec![],
        loaded: BTreeSet::new(),
        control: vec![],
        effects: vec![Effects::default(); body.len()],
        top: 0,
        nested: 0,
        p0: 0,
        assume,
        assumed: false,
        decided: BTreeSet::new(),
        diverged: None,
        implies: HashMap::default(),
        last_if: None,
        preds: HashMap::default(),
        equiv: HashMap::default(),
        selects: HashMap::default(),
        ifs: HashMap::default(),
        scalar_at: HashMap::default(),
        end: HashMap::default(),
        end_acc: Val::Lin(Lin::constant(0)),
    };
    it.p0 = it.syms.get(SymKind::P0);
    it.syms.get(SymKind::Acc0);
    let mut s = State { ptr: Lin::sym(it.p0), acc: Val::Lin(Lin::sym(1)), mem: HashMap::default(), stack: vec![] };
    it.items(body, &mut s, true)?;
    if s.ptr != Lin::sym(it.p0) || !s.stack.is_empty() {
        return Err("the body doesn't come back to where it started".into());
    }
    let cond = it.lin(&s.acc).map_err(|_| "it goes round again on a function's address".to_string())?;
    it.end = s.mem;
    it.end_acc = s.acc;
    Ok((it, cond))
}

/// Whether the cell at `off` (which held `xs` when the iteration started,
/// and holds `end` after it) is a running maximum or minimum, and if so, the
/// cells set along with it. What it held is used for nothing else but
/// deciding whether to set it, and setting the others then (with what
/// doesn't depend on it), and in cells each iteration sets before reading.
fn extreme(it: &mut Interp, off: i64, xs: Sym, end: &Lin, ends: &BTreeMap<i64, Lin>, cond: &Lin, uses: &BTreeSet<Sym>, x: impl Fn(&mut Interp, i64) -> Sym) -> Option<Extreme> {
    let one = |l: &Lin| match l.terms.iter().collect::<Vec<_>>()[..] {
        [(&s, &k)] => Some((s, k, l.c)),
        _ => None,
    };
    let (f, 1, 0) = one(end)? else { return None };
    let (branch, taken, skipped) = it.ifs.get(&f)?.clone();
    if skipped != Lin::sym(xs) || it.syms.closure(taken.terms.keys().copied()).contains(&xs) {
        return None;
    }
    // set just when `a < b`, or `b <= a` (for 1 minus that)
    let (t, negated) = match one(&branch)? {
        (t, 1, 0) => (t, false),
        (t, -1, 1) => (t, true),
        _ => return None,
    };
    let Some(Pred::Less(a, b, unsigned)) = it.preds.get(&t).cloned() else { return None };
    let held = Lin::sym(xs);
    let (max, strict) = match (a == held && b == taken, a == taken && b == held, negated) {
        (true, _, false) => (true, true),
        (_, true, false) => (false, true),
        (_, true, true) => (true, false),
        (true, _, true) => (false, false),
        _ => return None,
    };
    // what it held, used anywhere but in deciding
    let decides: BTreeSet<Sym> = branch.terms.keys().copied().collect();
    let mut used: BTreeSet<Sym> = BTreeSet::new();
    for a in &it.accesses {
        if !it.direct(&a.addr) {
            used.extend(a.addr.terms.keys());
        }
    }
    for c in &it.control {
        if *c != decides {
            used.extend(c);
        }
    }
    for (a, v) in &it.stored {
        // (what's stored in memory that's like a cell is in its end)
        if !it.scalar_at.contains_key(a) {
            used.extend(it.syms.deps(v));
        }
    }
    used.extend(cond.terms.keys());
    if it.syms.closure(used).contains(&xs) {
        return None;
    }
    // and in the other cells: those set with it, and those each iteration
    // sets before reading (what any cell held when the iteration started,
    // used anywhere)
    let mut anywhere = uses.clone();
    for e in ends.values() {
        anywhere.extend(it.syms.closure(e.terms.keys().copied()));
    }
    let mut with = vec![];
    let mut tainted = false;
    for (&other, e) in ends {
        if other == off || !it.syms.closure(e.terms.keys().copied()).contains(&xs) {
            continue;
        }
        let xo = x(it, other);
        let alongside = one(e).and_then(|(g, k, c)| (k == 1 && c == 0).then_some(g)).and_then(|g| it.ifs.get(&g)).is_some_and(|(br, v, skip)| *br == branch && *skip == Lin::sym(xo) && !it.syms.closure(v.terms.keys().copied()).contains(&xs));
        if alongside {
            with.push(other);
        } else if anywhere.contains(&xo) {
            return None;
        } else {
            tainted = true;
        }
    }
    Some(Extreme { cell: off, max, strict, unsigned, with, tainted })
}

/// Works out the plan from an iteration's run (`it`, which leaves `cond`
/// in acc), with the run that assumed nothing (`first`) for what decides
/// whether the loop goes round again.
fn classify(body: &[Item], mut it: Interp, cond: Lin, first: &Interp, linear: bool, guard: Option<(usize, Lin)>) -> Result<Plan, String> {
    let p0 = it.p0;
    let acc0: Sym = 1;

    // the cells near the pointer: which are written, and what each holds
    // at the end
    let mut cells: BTreeMap<i64, Role> = BTreeMap::new();
    let mut ends: BTreeMap<i64, Lin> = BTreeMap::new();
    for a in &it.accesses {
        if it.direct(&a.addr) {
            if a.addr.c % CELL != 0 {
                return Err("a cell that isn't aligned".into());
            }
            cells.entry(a.addr.c / CELL).or_insert(Role::Read);
            if a.write {
                let end = it.lin(&it.end[&a.addr]).map_err(|_| "a function's address left in a cell".to_string())?;
                ends.insert(a.addr.c / CELL, end);
            }
        }
    }
    // memory like a cell: a family that's written, at a pointer in a cell
    // the loop doesn't write (and doesn't move), with each op that accesses
    // it always accessing the same address
    let mut by_op: HashMap<(u32, *const Item), BTreeSet<Lin>> = HashMap::default();
    for a in &it.accesses {
        by_op.entry((a.chain, a.op)).or_default().insert(a.addr.clone());
    }
    let mut scalar_fams: BTreeMap<Lin, (i64, BTreeSet<i64>)> = BTreeMap::new();
    for a in &it.accesses {
        if it.direct(&a.addr) {
            continue;
        }
        let fam = a.addr.family();
        let base = match fam.terms.iter().collect::<Vec<_>>()[..] {
            [(&s, &1)] => match &it.syms.kinds[s as usize] {
                SymKind::Init(b) if it.direct(b) && b.c % CELL == 0 && !ends.contains_key(&(b.c / CELL)) => Some(b.c / CELL),
                _ => None,
            },
            _ => None,
        };
        if let Some(cell) = base {
            scalar_fams.entry(fam).or_insert((cell, BTreeSet::new())).1.insert(a.addr.c);
        }
    }
    scalar_fams.retain(|fam, _| {
        if it.accesses.iter().any(|a| a.inner.is_some() && a.addr.family() == *fam) {
            return false;
        }
        let written = it.accesses.iter().any(|a| a.write && !it.direct(&a.addr) && a.addr.family() == *fam);
        let alone = by_op.values().all(|addrs| addrs.len() == 1 || addrs.iter().all(|a| it.direct(a) || a.family() != *fam));
        written && alone
    });
    let mut scalars = vec![];
    let mut scalar_at: HashMap<Lin, i64> = HashMap::default();
    for (fam, (cell, offs)) in &scalar_fams {
        for &off in offs {
            let key = SCALAR + scalars.len() as i64;
            let addr = Lin { c: off, terms: fam.terms.clone() };
            cells.insert(key, Role::Read);
            if let Some(v) = it.end.get(&addr) {
                let end = it.lin(v).map_err(|_| "a function's address left in memory".to_string())?;
                ends.insert(key, end);
            }
            scalar_at.insert(addr, key);
            scalars.push(Scalar { cell: *cell, off });
        }
    }
    let addr_of = scalar_at.iter().map(|(a, &k)| (k, a.clone())).collect::<HashMap<i64, Lin>>();
    it.scalar_at = scalar_at.clone();
    let x = |it: &mut Interp, off: i64| match addr_of.get(&off) {
        Some(a) => it.syms.get(SymKind::Init(a.clone())),
        None => it.syms.get(SymKind::Init(Lin::sym(p0).add(&Lin::constant(off * CELL)))),
    };

    // what everything else depends on: where memory is accessed (other
    // than the cells near the pointer), what's decided, what's stored
    // elsewhere, and whether it goes round again
    let mut uses: BTreeSet<Sym> = BTreeSet::new();
    for a in &it.accesses {
        if !it.direct(&a.addr) {
            uses.extend(a.addr.terms.keys());
        }
        if let Some((st, _)) = &a.inner {
            uses.extend(st.terms.keys());
        }
    }
    for t in &it.inners {
        for l in [&t.x0, &t.xs].into_iter().chain(t.parts.iter().flat_map(|p| [&p.0, &p.1])) {
            uses.extend(l.terms.keys());
        }
    }
    for c in &it.control {
        uses.extend(c);
    }
    for (a, v) in &it.stored {
        if !scalar_at.contains_key(a) {
            uses.extend(it.syms.deps(v));
        }
    }
    uses.extend(cond.terms.keys());
    let uses = it.syms.closure(uses);
    // (what acc holds when an iteration starts is what the one before left,
    // which only the first can be given)
    if uses.contains(&acc0) || ends.values().any(|e| it.syms.closure(e.terms.keys().copied()).contains(&acc0)) {
        return Err("it uses what acc held when it started".into());
    }
    if uses.contains(&p0) {
        let mut why = vec![];
        if it.accesses.iter().any(|a| !it.direct(&a.addr) && it.syms.closure(a.addr.terms.keys().copied()).contains(&p0)) {
            why.push("an address");
        }
        if it.control.iter().any(|c| it.syms.closure(c.iter().copied()).contains(&p0)) {
            why.push("a branch");
        }
        if it.stored.iter().any(|(_, v)| it.syms.closure(it.syms.deps(v)).contains(&p0)) {
            why.push("a value stored to memory");
        }
        if it.syms.closure(cond.terms.keys().copied()).contains(&p0) {
            why.push("whether it goes round again");
        }
        return Err(format!("it depends on where the pointer is ({})", why.join(", ")));
    }

    // roles: cells that aren't written, or that each iteration restores,
    // are the same every time round
    for (&off, role) in cells.iter_mut() {
        let xs = x(&mut it, off);
        match ends.get(&off) {
            Some(end) if *end == Lin::sym(xs) => *role = Role::Restored,
            // (not yet worked out, so not known to be the same each time)
            Some(_) => *role = Role::Private,
            None => {}
        }
    }
    // then the rest: private, induction, reduction, or written by some
    // iterations (whatever any of them reads depends on these)
    let loaded = it.syms.closure(it.loaded.iter().copied());
    let mut extremes = vec![];
    for (&off, end) in &ends {
        if cells[&off] == Role::Restored {
            continue;
        }
        let xs = x(&mut it, off);
        let mut elsewhere = uses.clone();
        for (&other, e) in &ends {
            if other != off {
                elsewhere.extend(it.syms.closure(e.terms.keys().copied()));
            }
        }
        // its end is `x + delta`, where it matters whether `delta` doesn't
        // depend on `x` (if `x` is in it at all)
        let delta = end.sub(&Lin::sym(xs));
        let in_end = it.syms.closure(end.terms.keys().copied()).contains(&xs);
        let in_delta = it.syms.closure(delta.terms.keys().copied()).contains(&xs);
        let role = if !elsewhere.contains(&xs) && !in_end {
            Role::Private
        } else if !in_delta && delta.terms.keys().all(|&t| eval(&it, t, &cells, p0) == Kind::Invariant) {
            Role::Induction(delta)
        } else if !in_delta && !elsewhere.contains(&xs) {
            Role::Reduction
        } else if !elsewhere.contains(&xs) && !loaded.contains(&xs) {
            Role::Maybe
        } else if let Some(e) = extreme(&mut it, off, xs, end, &ends, &cond, &uses, x) {
            extremes.push(e);
            Role::Maybe
        } else {
            return Err(format!("{} carries something from one iteration to the next", what(off)));
        };
        cells.insert(off, role);
    }
    // (what's set along with a maximum is only set then)
    for e in &extremes {
        if e.with.iter().any(|o| cells.get(o) != Some(&Role::Maybe)) {
            return Err(format!("{} is a maximum or minimum, set along with something else", what(e.cell)));
        }
    }
    // a reduction's partial sums mean nothing to anything else
    for (&off, role) in &cells {
        if *role == Role::Reduction {
            let xs = x(&mut it, off);
            for (&other, e) in &ends {
                if other != off && it.syms.closure(e.terms.keys().copied()).contains(&xs) {
                    return Err(format!("{} is summed into, and used", what(off)));
                }
            }
        }
    }

    // memory: families, by base
    let mut families: BTreeMap<Lin, Family> = BTreeMap::new();
    for a in &it.accesses {
        if it.direct(&a.addr) {
            continue;
        }
        let f = families.entry(a.addr.family()).or_insert_with(|| Family { base: a.addr.family(), offsets: BTreeMap::new(), later: BTreeSet::new(), copyable: false, inner: None });
        *f.offsets.entry(a.addr.c).or_insert(false) |= a.write;
        if let Some(inner) = &a.inner {
            match &f.inner {
                None => f.inner = Some(inner.clone()),
                Some(i) if i == inner => {}
                Some(_) => return Err("loops in the body access memory differently".into()),
            }
        }
    }
    let mut private = vec![];
    let mut shared = vec![];
    let mut gathers = HashSet::default();
    for (base, f) in families {
        if scalar_fams.contains_key(&base) {
            continue;
        }
        // (memory a loop in the body accesses over a range: shared, at an
        // address known when the loop starts, over a range that is too)
        if let Some((st, n)) = &f.inner {
            let t = &it.inners[*n];
            let all: Vec<&Lin> = [&base, st, &t.x0, &t.xs].into_iter().chain(t.parts.iter().flat_map(|p| [&p.0, &p.1])).collect();
            if !base.terms.keys().all(|&s| eval(&it, s, &cells, p0) != Kind::Unknown) {
                return Err("a loop in the body accesses memory where only the iteration knows".into());
            }
            if !all[1..].iter().all(|l| l.terms.keys().all(|&s| eval(&it, s, &cells, p0) == Kind::Invariant)) {
                return Err("a loop in the body runs a different number of times, or differently, each time".into());
            }
            let st0 = stride(&it, &base, &cells, p0);
            if f.written() && st0 == Lin::constant(0) {
                return Err("every iteration writes the same memory".into());
            }
            shared.push(f);
            continue;
        }
        // a base that's a cell each iteration restores, whose memory is
        // always written before it's read, and that nothing else depends
        // on, is a stack: each thread gets its own
        let stack_cell = match base.terms.iter().collect::<Vec<_>>()[..] {
            [(&s, &1)] => match &it.syms.kinds[s as usize] {
                SymKind::Init(a) if it.direct(a) && cells.get(&(a.c / CELL)) == Some(&Role::Restored) => Some((s, a.c / CELL)),
                _ => None,
            },
            _ => None,
        };
        if let Some((s, cell)) = stack_cell {
            let exposed = it.accesses.iter().any(|a| a.exposed && a.addr.family() == base);
            let mut elsewhere: BTreeSet<Sym> = BTreeSet::new();
            for c in &it.control {
                elsewhere.extend(c);
            }
            // (what's stored in the stack itself, its pointers among it, is
            // the thread's own too)
            for (a, v) in &it.stored {
                if a.family() != base {
                    elsewhere.extend(it.syms.deps(v));
                }
            }
            elsewhere.extend(cond.terms.keys());
            for a in &it.accesses {
                if a.addr.family() != base && !it.direct(&a.addr) {
                    elsewhere.extend(a.addr.terms.keys());
                }
            }
            for e in ends.values() {
                elsewhere.extend(e.terms.keys().filter(|&&t| t != s));
            }
            // (what the stack holds depends on where it is only as far as
            // which memory that is: the thread's own copy holds the same, as
            // long as nothing depends on what was there before)
            let (deps, before) = it.syms.closure_apart(elsewhere, &base);
            if f.written() && !exposed && !before && !deps.contains(&s) {
                let (lo, hi) = (*f.offsets.keys().next().unwrap(), *f.offsets.keys().last().unwrap());
                private.push((cell, lo, hi));
                continue;
            }
        }
        if !base.terms.keys().all(|&t| eval(&it, t, &cells, p0) != Kind::Unknown) {
            // memory only read, where only the iteration knows: the generated
            // code checks, as it reads, that that isn't memory any iteration
            // writes (and if it is, puts back what they wrote, and runs the
            // loop in order)
            if f.written() {
                return Err("memory at an address that can't be worked out when the loop starts is written".into());
            }
            gathers.extend(it.accesses.iter().filter(|a| !it.direct(&a.addr) && a.addr.family() == base).map(|a| a.op));
            continue;
        }
        let st = stride(&it, &base, &cells, p0);
        if f.written() && st == Lin::constant(0) {
            return Err("every iteration writes the same memory".into());
        }
        // (an iteration that writes what one of the next few accesses,
        // whatever the addresses turn out to be: further apart, the
        // generated code checks, as that depends on how many there are; but
        // what's only read, and only written by later iterations, is read
        // from a copy of how it was)
        let mut f = f;
        if let (true, Some(st)) = (f.written(), st.as_const()) {
            for (&c1, &w) in &f.offsets {
                for (&c2, &w2) in &f.offsets {
                    if !w || c1 == c2 || (c1 - c2) % st != 0 {
                        continue;
                    }
                    // what reads c2 at iteration k, an iteration d later
                    // writes at c1
                    let d = (c2 - c1) / st;
                    if !w2 && d >= 1 {
                        f.later.insert(c2);
                    } else if d.abs() <= 16 {
                        return Err("an iteration writes memory another accesses".into());
                    }
                }
            }
        }
        shared.push(f);
    }

    // the ops that read memory that may be read from a copy (see
    // `Family::later` and `Family::copyable`), and which
    let mut copied: HashMap<(Vec<*const Item>, *const Item), usize> = HashMap::default();
    {
        let names: HashMap<u32, &Vec<*const Item>> = it.chains.iter().map(|(c, &n)| (n, c)).collect();
        let mut by_op: HashMap<(u32, *const Item), Vec<&Access>> = HashMap::default();
        for a in &it.accesses {
            by_op.entry((a.chain, a.op)).or_default().push(a);
        }
        let mut alone = vec![true; shared.len()];
        let mut ops: Vec<Vec<(u32, *const Item)>> = vec![vec![]; shared.len()];
        for (&key, accesses) in &by_op {
            let fams: BTreeSet<Option<usize>> = accesses.iter().map(|a| shared.iter().position(|f| !it.direct(&a.addr) && a.addr.family() == f.base)).collect();
            let reads = accesses.iter().all(|a| !a.write);
            for i in fams.iter().flatten() {
                if fams.len() > 1 || !reads {
                    alone[*i] = false;
                } else {
                    ops[*i].push(key);
                }
            }
        }
        for (i, f) in shared.iter_mut().enumerate() {
            // (what a loop in the body reads, it reads as it goes)
            if f.inner.is_some() {
                continue;
            }
            if f.written() {
                // (each op reads only offsets read from a copy, or none)
                for &key in &ops[i] {
                    let offs: BTreeSet<bool> = by_op[&key].iter().map(|a| f.later.contains(&a.addr.c)).collect();
                    match offs.len() {
                        1 if offs.contains(&true) => {
                            copied.insert((names[&key.0].clone(), key.1), i);
                        }
                        1 => {}
                        _ => return Err("an op reads memory as it was and as iterations leave it".into()),
                    }
                }
            } else if alone[i] {
                f.copyable = true;
                for &key in &ops[i] {
                    copied.insert((names[&key.0].clone(), key.1), i);
                }
            }
        }
    }

    // where each access to a stack each thread has its own is, if each op
    // (in each place it's inlined) always accesses the same cell of it: those
    // can be the thread's own variables
    let mut slots = HashMap::default();
    if !private.is_empty() {
        let bases: Vec<Lin> = private.iter().map(|&(cell, _, _)| Lin::sym(x(&mut it, cell))).collect();
        let mut by_op: HashMap<(u32, *const Item), BTreeSet<&Lin>> = HashMap::default();
        for a in &it.accesses {
            by_op.entry((a.chain, a.op)).or_default().insert(&a.addr);
        }
        let names: HashMap<u32, &Vec<*const Item>> = it.chains.iter().map(|(c, &n)| (n, c)).collect();
        let mut whole = true;
        for (&(chain, op), addrs) in &by_op {
            let stacky: Vec<usize> = addrs.iter().filter_map(|a| bases.iter().position(|b| a.family() == *b)).collect();
            if stacky.is_empty() {
                continue;
            }
            match (addrs.len(), stacky.len()) {
                (1, 1) => {
                    let a = addrs.iter().next().unwrap();
                    slots.insert((names[&chain].clone(), op), (stacky[0], a.c));
                }
                _ => whole = false,
            }
        }
        if !whole {
            slots.clear();
        }
    }

    let names: HashMap<u32, &Vec<*const Item>> = it.chains.iter().map(|(c, &n)| (n, c)).collect();
    let scalar_slots: HashMap<(Vec<*const Item>, *const Item), usize> = by_op
        .iter()
        .filter_map(|(&(chain, op), addrs)| {
            let a = addrs.iter().next()?;
            scalar_at.get(a).map(|&k| ((names[&chain].clone(), op), (k - SCALAR) as usize))
        })
        .collect();

    // how many times it runs ((memory that the loop doesn't write, at an
    // address that doesn't move, is what it is whichever iteration reads it)
    let readonly: BTreeSet<Lin> = shared.iter().filter(|f| !f.written() && stride(&it, &f.base, &cells, p0) == Lin::constant(0)).map(|f| f.base.clone()).collect();
    let trip = if linear && cond.terms.keys().all(|&t| eval(&it, t, &cells, p0) != Kind::Unknown) {
        let beta = stride(&it, &cond, &cells, p0);
        if beta == Lin::constant(0) {
            return Err("it runs at most once, or forever".into());
        }
        Trip::Linear { alpha: cond.clone(), beta }
    } else if let Some(t) = {
        // (memory that's like a cell, at its address in the first run's
        // symbols)
        let at = |cell: i64| first.syms.kinds.iter().position(|k| matches!(k, SymKind::Init(a) if *a == Lin::sym(first.p0).add(&Lin::constant(cell * CELL))));
        let first_scalars: HashMap<Lin, i64> = scalars
            .iter()
            .enumerate()
            .filter_map(|(j, sc)| Some((Lin { c: sc.off, terms: Terms(vec![(at(sc.cell)? as Sym, 1)]) }, SCALAR + j as i64)))
            .collect();
        compare_trip(first, guard.as_ref(), &cells, &readonly, &first_scalars)
    } {
        t
    } else {
        if !scalars.is_empty() {
            return Err("what decides whether it goes on is worked out with memory that's like a cell".into());
        }
        let stacks: Vec<i64> = private.iter().map(|p| p.0).collect();
        Trip::Slice(slice(body, first, &cells, &stacks, &readonly, guard.as_ref())?)
    };
    if !it.inners.is_empty() && (matches!(trip, Trip::Slice(_)) || !gathers.is_empty()) {
        return Err("a loop in the body is summed up, and what decides whether it goes on, or reads where only the iteration knows, isn't".into());
    }
    let p0 = it.p0;
    let cost = it.steps as u64;
    let through = it.through;
    Ok(Plan { syms: it.syms, p0, cells, private, shared, gathers, slots, scalars, scalar_slots, scalar_at: it.scalar_at.clone(), copied, inners: it.inners.clone(), assumed: false, through, trip, entered: vec![], extremes, cost })
}

/// What a symbol is, across iterations.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum Kind {
    /// The same every time round, and known when the loop starts.
    Invariant,
    /// An induction variable's value: known for the first iteration, and
    /// growing by its step.
    Moving,
    /// Neither.
    Unknown,
}

fn eval(it: &Interp, s: Sym, cells: &BTreeMap<i64, Role>, p0: Sym) -> Kind {
    match &it.syms.kinds[s as usize] {
        SymKind::Init(a) if it.direct(a) => match cells.get(&(a.c / CELL)) {
            Some(Role::Read | Role::Restored) => Kind::Invariant,
            Some(Role::Induction(_)) => Kind::Moving,
            _ => Kind::Unknown,
        },
        // (memory that's like a cell is as the cell would be)
        SymKind::Init(a) if it.scalar_at.contains_key(a) => match cells.get(&it.scalar_at[a]) {
            Some(Role::Read | Role::Restored) => Kind::Invariant,
            Some(Role::Induction(_)) => Kind::Moving,
            _ => Kind::Unknown,
        },
        // what's at an address that doesn't change, which no iteration
        // writes (the generated code checks that)
        SymKind::Init(a) if a.terms.keys().all(|&t| eval(it, t, cells, p0) == Kind::Invariant) => Kind::Invariant,
        _ => Kind::Unknown,
    }
}

/// How much `l` gains every time round: the induction variables in it,
/// times their steps.
fn stride(it: &Interp, l: &Lin, cells: &BTreeMap<i64, Role>, p0: Sym) -> Lin {
    let mut out = Lin::default();
    for (&s, &k) in &l.terms {
        if let SymKind::Init(a) = &it.syms.kinds[s as usize] {
            let var = if a.terms.len() == 1 && a.terms.get(&p0) == Some(&1) { Some(a.c / CELL) } else { it.scalar_at.get(a).copied() };
            if let Some(Role::Induction(step)) = var.and_then(|v| cells.get(&v)) {
                out = out.add(&step.scale(k));
            }
        }
    }
    out
}

/// The body's items that decide whether the loop goes round again (with the
/// moves between them), from the run that assumed nothing (`first`), if
/// running just those for any iteration is safe: what decides it depends
/// only on what's known when the loop starts (given the cells' `roles`)
/// and what the iteration works out from that, and they write only cells
/// near the pointer and `stacks`, and read only those.
/// With `guard`, the body item whose start decides it, with what acc holds
/// there: the slice is of what comes before that.
/// It may also read memory in `readonly` families (which the generated code
/// checks no iteration writes), which are where they are whichever iteration
/// it is.
fn slice(body: &[Item], first: &Interp, roles: &BTreeMap<i64, Role>, stacks: &[i64], readonly: &BTreeSet<Lin>, guard: Option<&(usize, Lin)>) -> Result<Vec<bool>, String> {
    let upto = guard.map_or(body.len(), |g| g.0);

    let cell = |a: &Lin| first.direct(a).then(|| a.c / CELL);
    let stack = |a: &Lin| match a.terms.iter().collect::<Vec<_>>()[..] {
        [(&s, &1)] => matches!(&first.syms.kinds[s as usize], SymKind::Init(b) if cell(b).is_some_and(|c| stacks.contains(&c))),
        _ => false,
    };
    let cond = match guard {
        Some((_, c)) => c.clone(),
        None => match first.end_acc() {
            Val::Lin(c) => c,
            Val::Func(_) => return Err("it goes round again on a function's address".into()),
        },
    };
    for d in first.syms.closure(cond.terms.keys().copied()) {
        match &first.syms.kinds[d as usize] {
            SymKind::Fresh(_) => {}
            SymKind::Init(a) if cell(a).is_some() => {
                if !matches!(roles.get(&cell(a).unwrap()), Some(Role::Induction(_) | Role::Restored | Role::Read)) {
                    return Err("whether it goes round again depends on something carried between iterations".into());
                }
            }
            SymKind::Init(a) if stack(a) || readonly.contains(&a.family()) => {}
            _ => return Err("whether it goes round again depends on memory that changes".into()),
        }
    }
    let effects = &first.effects;
    let alias = |a: &Loc, b: &Loc| match (a, b) {
        (Loc::Acc, Loc::Acc) => true,
        (Loc::Mem(x), Loc::Mem(y)) => x == y,
        _ => false,
    };
    // the `*`s and `&`s that pair up among the body's own items
    let mut pairs = vec![];
    let mut open = vec![];
    for (i, item) in body.iter().enumerate() {
        match item {
            Item::Op(Op::Deref) => open.push(i),
            Item::Op(Op::Refer) => {
                if let Some(j) = open.pop() {
                    pairs.push((j, i));
                }
            }
            _ => {}
        }
    }
    let mut forced: HashSet<usize> = HashSet::default();
    let mut include = loop {
        let mut include = vec![false; body.len()];
        let mut needed: Vec<Loc> = vec![Loc::Acc];
        for i in (0..upto).rev() {
            if matches!(body[i], Item::Op(Op::Move(_))) {
                continue;
            }
            let wanted = forced.contains(&i) || effects[i].writes.iter().any(|(w, _)| needed.iter().any(|n| alias(w, n)));
            if !wanted {
                continue;
            }
            include[i] = true;
            needed.retain(|n| !effects[i].writes.iter().any(|(w, definite)| *definite && alias(w, n)));
            needed.extend(effects[i].reads.iter().cloned());
        }
        let mut more = forced.clone();
        for &(a, b) in &pairs {
            if (a + 1..b).any(|i| include[i] && !matches!(body[i], Item::Op(Op::Move(_)))) {
                more.insert(a);
                more.insert(b);
            }
        }
        if more == forced {
            break include;
        }
        forced = more;
    };
    // (a `*` the slice keeps must have its `&` before where it stops)
    if pairs.iter().any(|&(a, b)| a < upto && b >= upto && include[a]) {
        return Err("whether it goes round again is decided under a `*`".into());
    }
    // moves too, except inside a `*` and `&` that are left out
    for i in 0..upto {
        if matches!(body[i], Item::Op(Op::Move(_))) {
            include[i] = !pairs.iter().any(|&(a, b)| a < i && i < b && !include[a]);
        }
    }
    // a `*` without its `&` among the body's items can't be left out
    for i in 0..upto {
        if matches!(body[i], Item::Op(Op::Deref | Op::Refer)) && !pairs.iter().any(|&(a, b)| a == i || b == i) && !include[i] {
            return Err("whether it goes round again is decided under a `*` that isn't undone".into());
        }
    }
    for i in (0..body.len()).filter(|&i| include[i]) {
        for (w, _) in &effects[i].writes {
            if let Loc::Mem(a) = w {
                if cell(a).is_none() && !stack(&a.family()) {
                    return Err("deciding whether it goes round again writes memory".into());
                }
            }
        }
        // (memory elsewhere, even at a fixed address, isn't among what the
        // generated code checks no iteration writes)
        for r in &effects[i].reads {
            if let Loc::Mem(a) = r {
                if cell(a).is_none() && !stack(&a.family()) && !readonly.contains(&a.family()) {
                    return Err("deciding whether it goes round again reads memory".into());
                }
            }
        }
    }
    Ok(include)
}

/// What a function may do, worked out from its code: the cells (offsets from
/// where the pointer is when it's called) it may read before writing them,
/// and those it may write, each with whether it surely does.
#[derive(Clone, Debug, Default)]
pub struct Summary {
    pub reads: BTreeSet<i64>,
    pub writes: BTreeMap<i64, bool>,
}

/// A function's summary, if it only accesses cells near the pointer (at
/// offsets known from its code), calls nothing, and leaves the pointer
/// where it found it.
pub fn summary(body: &[Item]) -> Option<Summary> {
    // (`written` is what's surely been written by this point; `sure`, whether
    // the code here surely runs)
    fn walk(items: &[Item], mut at: i64, written: &mut BTreeSet<i64>, sure: bool, out: &mut Summary) -> Option<i64> {
        for item in items {
            match item {
                Item::Op(Op::Move(n)) => at = at.checked_add(*n)?,
                Item::Op(Op::Load | Op::Add) => {
                    if !written.contains(&at) {
                        out.reads.insert(at);
                    }
                }
                Item::Op(Op::Store) => {
                    written.insert(at);
                    let e = out.writes.entry(at).or_insert(sure);
                    *e |= sure;
                }
                Item::Op(Op::Deref | Op::Refer | Op::Call | Op::Read | Op::Write | Op::Func | Op::EndFunc | Op::While | Op::EndWhile) => return None,
                Item::Op(_) => {}
                Item::Loop(inner) => {
                    // (it may not run: what it writes isn't surely written
                    // after it, but is for what follows within it)
                    let mut inside = written.clone();
                    if walk(inner, at, &mut inside, false, out)? != at {
                        return None;
                    }
                }
                Item::Func(..) => return None,
            }
        }
        Some(at)
    }
    let mut out = Summary::default();
    (walk(body, 0, &mut BTreeSet::new(), true, &mut out)? == 0).then_some(out)
}

/// What a function does, if it's linear: every cell near the pointer it
/// writes, and acc, end up linear in what the cells (and acc, and where the
/// pointer is) held when it was called, and it accesses no memory a pointer
/// leads to.
pub struct LinearEffect {
    pub syms: Syms,
    pub p0: Sym,
    pub acc0: Sym,
    /// The cells it writes, as offsets from the pointer, with what they end
    /// up holding.
    pub writes: Vec<(i64, Lin)>,
    pub acc: Lin,
}

impl LinearEffect {
    /// The cell an `Init` symbol is of (an offset from the pointer).
    pub fn cell_of(&self, s: Sym) -> Option<i64> {
        match &self.syms.kinds[s as usize] {
            SymKind::Init(a) if self.syms.near(a) => Some(a.c / CELL),
            _ => None,
        }
    }
}

/// The most ops a function can run (counting what it calls) for
/// `linear_effect` to look for a linear effect in it.
const LINEAR_OPS: usize = 600;

/// Whether a body, with the bodies of what it calls, has at most `budget`
/// ops (taken from the budget as they're counted).
fn within(body: &[Item], funcs: &HashMap<String, &[Item]>, budget: &mut usize, depth: usize) -> bool {
    let mut called: Option<&str> = None;
    for item in body {
        if *budget == 0 || depth > 16 {
            return false;
        }
        *budget -= 1;
        match item {
            Item::Op(Op::Label(l)) => called = Some(funcs.get_key_value(super::label_name(l).as_str()).map_or("", |(k, _)| k.as_str())),
            Item::Op(Op::Call) => {
                if let Some(f) = called.take().and_then(|name| funcs.get(name)) {
                    if !within(f, funcs, budget, depth + 1) {
                        return false;
                    }
                }
            }
            Item::Op(_) => {}
            Item::Loop(inner) | Item::Func(_, inner) => {
                if !within(inner, funcs, budget, depth + 1) {
                    return false;
                }
            }
        }
    }
    true
}

/// The effect of the function with this body, if it's linear.
pub fn linear_effect(body: &[Item], funcs: &HashMap<String, &[Item]>) -> Option<LinearEffect> {
    // (a linear effect is a short one: not worth interpreting a big body,
    // with what it calls, to find out it isn't)
    let mut budget = LINEAR_OPS;
    if !within(body, funcs, &mut budget, 0) {
        return None;
    }
    let (cheap, summaries) = (HashSet::default(), HashMap::default());
    let mut it = Interp {
        syms: Syms::default(),
        funcs,
        cheap: &cheap,
        summaries: &summaries,
        inlining: vec![],
        through: false,
        op: std::ptr::null(),
        calls: vec![],
        chains: [(vec![], 0)].into_iter().collect(),
        chain: 0,
        steps: 0,
        spent: 0,
        accesses: vec![],
        inners: vec![],
        writes: HashMap::default(),
        clobbered: BTreeSet::new(),
        clobber_deps: BTreeSet::new(),
        stored: vec![],
        loaded: BTreeSet::new(),
        control: vec![],
        effects: vec![Effects::default(); body.len()],
        top: 0,
        nested: 0,
        p0: 0,
        assume: vec![],
        assumed: false,
        decided: BTreeSet::new(),
        diverged: None,
        implies: HashMap::default(),
        last_if: None,
        preds: HashMap::default(),
        equiv: HashMap::default(),
        selects: HashMap::default(),
        ifs: HashMap::default(),
        scalar_at: HashMap::default(),
        end: HashMap::default(),
        end_acc: Val::Lin(Lin::constant(0)),
    };
    it.p0 = it.syms.get(SymKind::P0);
    let acc0 = it.syms.get(SymKind::Acc0);
    let mut s = State { ptr: Lin::sym(it.p0), acc: Val::Lin(Lin::sym(acc0)), mem: HashMap::default(), stack: vec![] };
    it.items(body, &mut s, true).ok()?;
    if s.ptr != Lin::sym(it.p0) || !s.stack.is_empty() || it.accesses.iter().any(|a| !it.direct(&a.addr)) {
        return None;
    }
    // only what the cells held, acc, and where the pointer was
    let plain = |l: &Lin, syms: &Syms| {
        l.terms.keys().all(|&t| match &syms.kinds[t as usize] {
            SymKind::Init(a) => syms.near(a),
            SymKind::P0 | SymKind::Acc0 => true,
            SymKind::Fresh(_) => false,
        })
    };
    let Val::Lin(acc) = s.acc else { return None };
    if !plain(&acc, &it.syms) {
        return None;
    }
    let mut writes = vec![];
    let mut written: Vec<&Lin> = it.accesses.iter().filter(|a| a.write).map(|a| &a.addr).collect();
    written.sort();
    written.dedup();
    for addr in written {
        let Val::Lin(v) = &s.mem[addr] else { return None };
        if !plain(v, &it.syms) || addr.c % CELL != 0 {
            return None;
        }
        writes.push((addr.c / CELL, v.clone()));
    }
    Some(LinearEffect { syms: it.syms, p0: it.p0, acc0, writes, acc })
}
