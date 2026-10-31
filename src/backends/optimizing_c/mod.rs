//! The optimizing C backend: C that a C compiler can make fast code of.
//! Against `LiteralC`'s op-by-op C:
//!
//! - the pointer and the accumulator are each function's local variables,
//!   passed to the functions it calls and given back, in registers;
//! - functions that are exactly `asm`'s routines for what the VM has no
//!   instructions for (multiplying, dividing, comparing, shifting, ...) are
//!   done with the machine's own instructions (see [`idioms`]), and
//!   functions whose effect is linear in what they're given are
//!   straight-line code;
//! - each function keeps the cells it reaches at fixed places in variables
//!   of its own, written to memory only where something might look (see
//!   [`promote`]);
//! - and with `parallel`, loops' iterations run in parallel, with OpenMP,
//!   where it can tell that gives the same results (below). The language
//!   doesn't change: the parallelism is found in the program. The stack of
//!   pointers `*` saves is each thread's own, so that VM code can run on
//!   several threads at once; only the tape is shared. Compiled without
//!   OpenMP, the pragmas are ignored and the program runs on one thread.
//!
//! For each loop, [`analysis`] works out whether its iterations can run in
//! parallel. If so, the loop runs as it would for a few iterations, so short
//! loops cost almost nothing more. If it's still going, the generated code
//! then:
//!
//! 1. checks, with the real addresses, that the memory each part of the
//!    iteration accesses doesn't overlap any other part's, and that no
//!    iteration writes a cell another one accesses;
//! 2. works out how many more times the loop will go round, `N`;
//! 3. runs the first `N - 1` of those iterations in code made for running
//!    them in parallel: a part at a time on one thread, timed, until what's
//!    left is worth starting threads for (see `min_time`), and then on as
//!    many as it's worth, sharing it out as they finish. Each thread has its
//!    own copy of the cells near the pointer, accessed directly (so they can
//!    be the C compiler's to keep in registers), and of any stack the
//!    iteration uses (each cell of which, where it's known which, is a
//!    variable of its own); each iteration gets its induction variables'
//!    values, and reductions are summed. Memory read where only the
//!    iteration knows is checked, as it's read, not to be memory any
//!    iteration writes: if it is, what they wrote is put back, and the loop
//!    runs on in order;
//! 4. sets the cells to what they'd hold when the last iteration starts,
//!    and lets the loop run on, which runs the last iteration and leaves
//!    every cell as the sequential program would. (For a cell that only
//!    some iterations write, that's what the last of those left, so each
//!    iteration notes which of those cells it writes. A cell that nothing
//!    after the loop reads before writing it, in the rest of the program,
//!    is left alone.)
//!
//! If a check fails, or the rest of the loop isn't worth it, the loop just
//! runs on. Each loop in the output has a comment saying what was decided,
//! and why; compiled with `-DBF_STATS`, the program also says on stderr,
//! each time, whether the checks passed, how many iterations ran in
//! parallel, and how long that took.
//!

mod analysis;
mod idioms;
mod promote;

#[cfg(test)]
mod tests;

use crate::ir::EXIT;
use crate::{Op, Target};
use analysis::{Lin, Plan, Role, SymKind, Trip, SCALAR};
use crate::asm::fx::HashMap;
use std::fmt::Write;

/// The optimizing C backend (see the module).
#[derive(Clone, Copy, Debug)]
pub struct OptimizingC {
    /// The fewest iterations to run in parallel: fewer, and the loop runs
    /// on one thread.
    pub min_iterations: u64,
    /// The least time (in nanoseconds) the rest of a loop must be going to
    /// take on one thread for starting threads to be worth it, to begin
    /// with: starting them takes a microsecond or so, and most of one more
    /// for each (see `FORK_NS`), so the default is 10 µs. Each loop then
    /// learns its own: whenever running it in parallel didn't pay (the
    /// memory its iterations use has to move between the cores' caches,
    /// which for some loops costs far more than the threads), it needs
    /// twice as long, and a little less each time it's run on one thread.
    /// Threads are as many as starting them is worth (see
    /// `Emitter::threads`). Each time, a loop first runs on one thread a
    /// part at a time, timing them (from the 16th iteration, unless they
    /// look like a lot of work), until a part has taken a fifth of this, to
    /// know how long the rest would take. (On one thread, that code is
    /// faster than the loop's own, which checks where the pointer goes as it
    /// goes.) With 0, loops go parallel straight away, however short.
    pub min_time: u64,
    /// Whether the routines it knows are done with the machine's
    /// instructions (see [`idioms`]).
    pub idioms: bool,
    /// Whether functions whose effect is linear in what they're given are
    /// straight-line code.
    pub linear: bool,
    /// The most ops a function can come to, with the calls in it inlined,
    /// for ordinary code to inline it at every call (see `INLINE_OPS`, the
    /// default). Lower makes less C, which compiles faster, for programs of
    /// many small functions called from many places.
    pub inline_ops: usize,
    /// Whether loops run in parallel where they can (with OpenMP). Without
    /// (the default), each loop is just C, and the program comes out much
    /// smaller, faster to make, and for most programs, faster: their loops
    /// are too short for threads to pay.
    pub parallel: bool,
    /// Whether each function keeps the cells it reaches at fixed places in
    /// variables of its own (see [`promote`]), where loops don't run in
    /// parallel (that code works on the cells in memory).
    pub promote: bool,
    /// The most ops a function can have for that to be done throughout it:
    /// in a bigger one, it's done to each loop that's small enough (see
    /// `promote::MOST_OPS`). A function this big takes the C compiler far
    /// longer done throughout than as plain code (a big game's took
    /// minutes, where the rest took seconds), and only its loops run much.
    pub promote_ops: usize,
    /// How many files `compile_units` makes of the program: the same C as
    /// `compile`'s one file, shared out so a C compiler can work on them
    /// at once (a big program's C takes most of building it, on one core).
    pub units: usize,
}

impl Default for OptimizingC {
    fn default() -> Self {
        OptimizingC { min_iterations: 16, min_time: 10_000, idioms: true, linear: true, inline_ops: INLINE_OPS, parallel: false, promote: true, promote_ops: promote::MOST_OPS, units: 1 }
    }
}

/// About how long starting threads takes, in nanoseconds: this, and
/// `THREAD_NS` more for each (with the threads spinning while they wait for
/// work, as the generated code has them do; sleeping, it's tens of
/// microseconds).
const FORK_NS: u64 = 1000;
const THREAD_NS: u64 = 700;
/// And about how much more, at least, for more threads than share a cache.
const CLUSTER_NS: u64 = 40_000;
/// And how long starting them the first time takes.
const START_NS: u64 = 500_000;
/// The most ops a function can come to, with the calls in it inlined, for
/// ordinary code to inline it (more, and it's called: inlining everything
/// everywhere makes programs a compiler generates, with big functions
/// called from many places, too big for the C compiler).
const INLINE_OPS: usize = 2000;

/// An op, a loop, or a function's definition.
pub(crate) enum Item {
    Op(Op),
    Loop(Vec<Item>),
    Func(String, Vec<Item>),
}

pub(crate) fn label_name(l: &[u8; 16]) -> String {
    l.iter().take_while(|&&c| c != 0).map(|&c| c as char).collect()
}

/// The program as items: loops and functions (named by the label before
/// them, as in the C backend) hold their bodies.
fn parse(ops: &[Op]) -> Vec<Item> {
    fn seq(ops: &mut std::slice::Iter<Op>, last: &mut String) -> Vec<Item> {
        let mut out = vec![];
        while let Some(&op) = ops.next() {
            match op {
                Op::While => out.push(Item::Loop(seq(ops, last))),
                Op::EndWhile | Op::EndFunc => return out,
                Op::Func => {
                    let name = last.clone();
                    out.push(Item::Func(name, seq(ops, last)));
                }
                Op::Label(l) => {
                    *last = label_name(&l);
                    out.push(Item::Op(op));
                }
                op => out.push(Item::Op(op)),
            }
        }
        out
    }
    seq(&mut ops.iter(), &mut String::new())
}

const PRELUDE: &str = r#"#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
#include <time.h>
#include <pthread.h>
#include <sys/resource.h>
#ifdef _OPENMP
#include <omp.h>
#endif
#ifdef __APPLE__
#include <sys/sysctl.h>
#endif

#ifndef BF_CELLS
#define BF_CELLS 100000
#endif
/* The C stack, which the program's calls go on as well as the tape's: as
   big as the tape (at least 64 MB), so a program can recurse as deep as its
   memory allows. Pages it never touches cost nothing. */
#ifndef BF_C_STACK
#define BF_C_STACK ((size_t)BF_CELLS * sizeof(int64_t) * 4)
#endif
/* What the program's parts share. As one file, each is static; as several
   (`BF_UNIT`, see `OptimizingC::units`), each file declares it, and the one
   with `main` (`BF_MAIN_UNIT`) defines it. The program's functions, too:
   static as one file, so the C compiler can inline them where they're
   called. */
#if defined(BF_UNIT) && !defined(BF_MAIN_UNIT)
#define BF_SHARED(declaration, value) extern declaration
#elif defined(BF_UNIT)
#define BF_SHARED(declaration, value) declaration = value
#else
#define BF_SHARED(declaration, value) static declaration = value
#endif
#ifdef BF_UNIT
#define BF_LINK
#else
#define BF_LINK static
#endif

BF_SHARED(int64_t *tape, NULL);

/* How far down the C stack can go (it grows down), less some room for C the
   program calls; a function that calls others stops the program there, as
   the VM does when its stack runs into its heap, rather than crash. (Each of
   the VM's calls is a C call too, which takes more of the C stack than of
   the tape: a program can run out of the one before the other.) */
BF_SHARED(uintptr_t bf_stack_end, 0);
BF_SHARED(size_t bf_stack_size, 0);
static void bf_overflow(void) { fputs("stack overflow\n", stdout); fflush(stdout); exit(1); }
#define BF_STACK_CHECK { char bf_here; if ((uintptr_t)&bf_here < bf_stack_end) bf_overflow(); }

/* What a function gives back: where the pointer is, and acc. A function
   takes them, and gives them back, by value, in registers: given their
   addresses, the C compiler would have to keep them in memory, and to
   assume that writing to any cell might change them. */
typedef struct { int64_t *ptr; int64_t acc; } bf_st;

/* What the program's thread has the main thread do (see bf.h): one call at
   a time, which the main thread waits for until the program's done. */
BF_SHARED(pthread_mutex_t bf_lock, PTHREAD_MUTEX_INITIALIZER);
BF_SHARED(pthread_cond_t bf_signal, PTHREAD_COND_INITIALIZER);
BF_SHARED(void (*bf_job)(void *), NULL);
BF_SHARED(void *bf_job_arg, NULL);
BF_SHARED(int bf_threaded, 0);
BF_SHARED(int bf_job_done, 0);
BF_SHARED(int bf_finished, 0);

/* the pointers `*` has saved: each thread's own */
BF_SHARED(_Thread_local int64_t **stack, NULL);

/* whether two ranges of addresses, each from its first byte to its last,
   don't overlap */
static int bf_apart(__int128 a, __int128 b, __int128 c, __int128 d) { return b < c || d < a; }

/* whether, over iterations 0 to m - 1, the cells read at rb + ro[i] + s k
   are only ever written (at wb + wo[j] + s k') by later iterations, k' > k:
   then reading a copy of them as they were reads what they'd hold */
static int bf_later(__int128 rb, __int128 rs, const int64_t *ro, int nr, __int128 wb, __int128 ws, const int64_t *wo, int nw, int64_t m) {
    if (rs != ws || rs == 0) return 0;
    for (int i = 0; i < nr; i++)
        for (int j = 0; j < nw; j++) {
            __int128 d = rb + ro[i] - wb - wo[j];
            if (d % 8 != 0) return 0;
            if (d % rs != 0) continue;
            __int128 k = d / rs;
            if (k < 1 && k > -(__int128)m) return 0;
        }
    return 1;
}

/* the most threads to run on, and the most that share a cache */
BF_SHARED(int bf_most_threads, 1);
BF_SHARED(int bf_cluster, 1);

/* whether the threads have been started, and until they are, how much
   time running loops on them would have saved so far: starting them the
   first time takes most of a millisecond, so not until that's worth it */
BF_SHARED(int bf_started, 0);
BF_SHARED(double bf_saved, 0);

/* the time, in nanoseconds */
static double bf_now(void) { struct timespec t; clock_gettime(CLOCK_MONOTONIC, &t); return (double)t.tv_sec * 1e9 + (double)t.tv_nsec; }

/* in an iteration running in parallel, that it wrote the cell `p` (if
   it's one of the thread's copies of the cells near the pointer that only
   some iterations write: each has a bit) */
#define BF_NOTE(p) do { if ((uintptr_t)(p) - (uintptr_t)bf_win < sizeof bf_win) bf_wbits |= bf_bit[(int64_t *)(p) - bf_win]; } while (0)
"#;

/// What only the part with `main` holds: what the program's thread asks
/// of the main thread, and setting up the threads.
const PRELUDE_MAIN: &str = r#"
/* the external function an aborting program calls (see the IR's
   `Options::exits`): stops it, with the status it's given */
void bf_exit(int64_t **tape, int64_t **ptr, int64_t *acc) {
    (void)tape; (void)acc;
    fflush(stdout);
    exit((int)**ptr);
}

void bf_on_main_thread(void (*f)(void *), void *arg) {
    if (!bf_threaded) { f(arg); return; }
    pthread_mutex_lock(&bf_lock);
    bf_job = f;
    bf_job_arg = arg;
    bf_job_done = 0;
    pthread_cond_broadcast(&bf_signal);
    while (!bf_job_done) pthread_cond_wait(&bf_signal, &bf_lock);
    pthread_mutex_unlock(&bf_lock);
}

/* the main thread, while the program runs: doing what it's asked */
static void bf_serve(void) {
    pthread_mutex_lock(&bf_lock);
    while (!bf_finished) {
        if (bf_job) {
            void (*f)(void *) = bf_job;
            bf_job = NULL;
            pthread_mutex_unlock(&bf_lock);
            f(bf_job_arg);
            pthread_mutex_lock(&bf_lock);
            bf_job_done = 1;
            pthread_cond_broadcast(&bf_signal);
        } else {
            pthread_cond_wait(&bf_signal, &bf_lock);
        }
    }
    pthread_mutex_unlock(&bf_lock);
}

/* Threads that wait for more work by sleeping take tens of microseconds to
   start again, and by spinning about one, so they spin for a while (unless
   whoever runs the program says otherwise). And there are as many as there
   are cores, or on a Mac, fast cores: a team with a slow one in it waits
   for it. More than share a cache only if it's a lot of work: the memory
   they share goes back and forth between the caches. */
static void bf_setup(void) {
    setenv("KMP_BLOCKTIME", "20", 0);
#ifdef _OPENMP
    bf_most_threads = bf_cluster = omp_get_max_threads();
#ifdef __APPLE__
    int fast = 0, shared = 0;
    size_t size = sizeof fast;
    if (!getenv("OMP_NUM_THREADS") && sysctlbyname("hw.perflevel0.physicalcpu", &fast, &size, NULL, 0) == 0 && fast > 0 && fast < bf_most_threads) bf_most_threads = bf_cluster = fast;
    size = sizeof shared;
    if (sysctlbyname("hw.perflevel0.cpusperl2", &shared, &size, NULL, 0) == 0 && shared > 0 && shared < bf_cluster) bf_cluster = shared;
#endif
#endif
}
"#;

/// A program as C, in parts: what every file needs (the prelude, and every
/// function declared), the definitions (each function with the loops it
/// runs in parallel), and what goes with `main`. As one file, or as several
/// to compile at once (see `OptimizingC::units`).
pub struct CSource {
    pub head: String,
    pub chunks: Vec<String>,
    pub tail: String,
}

impl CSource {
    /// The program as one file.
    pub fn single(&self) -> String {
        self.single_with("")
    }

    /// The program as one file, after `prefix` (`#define`s, say).
    pub fn single_with(&self, prefix: &str) -> String {
        let mut out = String::from(prefix);
        out += &self.head;
        for c in &self.chunks {
            out += c;
        }
        out += &self.tail;
        out
    }

    /// The program as `n` files (at least one), the definitions shared out
    /// among them by size, `main` in the first: each compiles on its own,
    /// and together they link into the program.
    pub fn units(&self, n: usize) -> Vec<String> {
        let n = n.max(1);
        if n == 1 {
            return vec![self.single()];
        }
        let mut files: Vec<String> = (0..n)
            .map(|k| format!("#define BF_UNIT\n{}{}", if k == 0 { "#define BF_MAIN_UNIT\n" } else { "" }, self.head))
            .collect();
        // (the biggest first, each to the smallest file so far; the first
        // starts with main's share)
        let mut sizes: Vec<usize> = files.iter().map(String::len).collect();
        sizes[0] += self.tail.len();
        let mut order: Vec<&String> = self.chunks.iter().collect();
        order.sort_by_key(|c| std::cmp::Reverse(c.len()));
        for c in order {
            let k = (0..n).min_by_key(|&k| sizes[k]).unwrap();
            files[k] += c;
            sizes[k] += c.len();
        }
        files[0] += &self.tail;
        files
    }
}

impl Target for OptimizingC {
    fn compile(&mut self, ops: &[Op]) -> String {
        self.source(ops).single()
    }
}

impl OptimizingC {
    /// The program as `units` files of C (see `units`).
    pub fn compile_units(&mut self, ops: &[Op]) -> Vec<String> {
        self.source(ops).units(self.units)
    }

    /// The program as C, in its parts, to make one file or several of.
    pub fn source(&mut self, ops: &[Op]) -> CSource {
        let mut phase = crate::asm::log::phase(crate::asm::log::INFO, "optimizing C");
        let out = self.compile_ops(ops);
        let plans = analysis::PLANS.with(|p| p.replace((0, 0)));
        crate::log!(crate::asm::log::DEBUG, "{} loops analyzed, {} to run in parallel", plans.0, plans.1);
        let size = out.head.len() + out.chunks.iter().map(String::len).sum::<usize>() + out.tail.len();
        phase.done(format!("{} KB of C", size / 1024));
        out
    }

    fn compile_ops(&mut self, ops: &[Op]) -> CSource {
        analysis::forget();
        let items = parse(ops);
        let mut funcs: HashMap<String, &[Item]> = HashMap::default();
        fn collect<'a>(items: &'a [Item], out: &mut HashMap<String, &'a [Item]>) {
            for item in items {
                match item {
                    Item::Func(name, body) => {
                        out.insert(name.clone(), body);
                        collect(body, out);
                    }
                    Item::Loop(body) => collect(body, out),
                    Item::Op(_) => {}
                }
            }
        }
        collect(&items, &mut funcs);
        let mut labels: Vec<String> = ops.iter().filter_map(|op| if let Op::Label(l) = op { Some(label_name(l)) } else { None }).collect();
        labels.sort();
        labels.dedup();
        let even = even_functions(&funcs);
        let stops = stopping(&funcs);
        let mut refs: HashMap<String, usize> = HashMap::default();
        for op in ops {
            if let Op::Label(l) = op {
                *refs.entry(label_name(l)).or_default() += 1;
            }
        }
        // (a function's label is where it's defined, and then where it's used)
        let once = refs.into_iter().filter(|(f, n)| *n == 2 && funcs.contains_key(f)).map(|(f, _)| f).collect();
        // the functions that are routines the target knows, by label: C that
        // does what they do
        let known: HashMap<String, String> = idioms::idioms()
            .into_iter()
            .filter(|_| self.idioms)
            .filter(|i| {
                funcs.get(&i.label).is_some_and(|body| {
                    let mut ops = vec![];
                    flatten(body, &mut ops);
                    // (as `asm` writes it, or as `asm::opt` leaves it)
                    ops == i.body || crate::asm::opt::routine_forms().get(&i.label).is_some_and(|forms| forms.contains(&ops))
                })
            })
            .map(|i| (i.label, i.native))
            .collect();
        // the functions whose effect is linear, worked out once
        let linear: HashMap<String, String> = funcs
            .iter()
            .filter(|_| self.linear)
            .filter_map(|(name, body)| analysis::linear_effect(body, &funcs).map(|e| (name.clone(), linear_c(&e))))
            .collect();
        let cheap = known.keys().chain(linear.keys()).cloned().collect();
        let summaries: HashMap<String, analysis::Summary> = known.keys().filter_map(|f| Some((f.clone(), analysis::summary(funcs[f])?))).collect();
        // (every loop's analysis, at once on every core: each depends only on
        // the loop's body and the functions, so they're what the emitter
        // would otherwise work out one at a time as it came to them)
        let plans = if self.parallel { analyze_all(&items, &funcs, &cheap, &summaries) } else { HashMap::default() };
        // (the program's own code is like a function too big to be done as
        // `promote::function`: its loops are each done as regions)
        let mut e = Emitter { promote: self.promote, promote_ops: self.promote_ops, regions: self.promote && !self.parallel, funcs: &funcs, even: &even, stops: &stops, linear: &linear, known: &known, cheap, min: self.min_iterations, work: self.min_time, inline_ops: self.inline_ops, inlining: vec![], sizes: Default::default(), once, loops: 0, entered: vec![], scalars: None, copied: None, via: None, saved_via: vec![], plans, summaries, notes: None, unnoted: false, at: None, saved_at: vec![], depth: 0, gathers: None, call_chain: vec![], slots: None, direct: None, seq: None, defs: String::new(), chunks: vec![], func_depth: 0, main_defs: String::new() };
        let mut main = String::new();
        e.items(&items, &mut main, self.parallel, false);
        let mut head = String::from(PRELUDE);
        // (the program's own functions are BF_LINK: static as one file)
        for name in labels {
            if funcs.contains_key(&name) {
                let _ = writeln!(head, "BF_LINK bf_st {name}(int64_t *ptr, int64_t acc);");
            } else {
                head += &external_c(&name);
            }
        }
        // (what main's own loops need goes with it)
        let mut out = String::from(PRELUDE_MAIN);
        out += &e.main_defs;
        out += &e.defs;
        // (the program runs on a thread of its own, for its stack: see
        // BF_C_STACK; or on this one, if that can't be had)
        let _ = write!(
            out,
            "\nstatic void *bf_run(void *unused) {{\n(void)unused;\n{{ char here; size_t room = (size_t)1 << 20; bf_stack_end = (uintptr_t)&here - (bf_stack_size > 2 * room ? bf_stack_size - room : bf_stack_size / 2); }}\nstack = malloc(1024 * sizeof(int64_t *));\nint64_t *ptr = tape;\nint64_t acc = 0;\n{main}pthread_mutex_lock(&bf_lock);\nbf_finished = 1;\npthread_cond_broadcast(&bf_signal);\npthread_mutex_unlock(&bf_lock);\nreturn NULL;\n}}\n\nint main(void) {{\nbf_setup();\ntape = calloc(BF_CELLS, sizeof(int64_t));\nsize_t size = BF_C_STACK < ((size_t)64 << 20) ? (size_t)64 << 20 : BF_C_STACK;\nbf_stack_size = size;\npthread_attr_t attr;\npthread_t t;\npthread_attr_init(&attr);\n/* (threaded before the thread starts, which can ask for the main thread at once) */\nbf_threaded = 1;\nif (pthread_attr_setstacksize(&attr, size) != 0 || pthread_create(&t, &attr, bf_run, NULL) != 0) bf_threaded = 0;\nif (bf_threaded) {{\nbf_serve();\npthread_join(t, NULL);\n}} else {{\n/* (this thread's own stack, then) */\nstruct rlimit limit;\nbf_stack_size = getrlimit(RLIMIT_STACK, &limit) == 0 && limit.rlim_cur != RLIM_INFINITY ? (size_t)limit.rlim_cur : (size_t)8 << 20;\nbf_run(NULL);\n}}\nreturn 0;\n}}\n"
        );
        CSource { head, chunks: e.chunks, tail: out }
    }
}

/// The analyses of all the loops in `items` (by their bodies), worked out
/// on as many threads as there are cores, each taking the next loop there
/// is to do.
fn analyze_all(items: &[Item], funcs: &HashMap<String, &[Item]>, cheap: &crate::asm::fx::HashSet<String>, summaries: &HashMap<String, analysis::Summary>) -> HashMap<*const Item, std::rc::Rc<Result<Plan, String>>> {
    fn loops<'a>(items: &'a [Item], out: &mut Vec<&'a [Item]>) {
        for item in items {
            match item {
                Item::Loop(body) => {
                    out.push(body);
                    loops(body, out);
                }
                Item::Func(_, body) => loops(body, out),
                Item::Op(_) => {}
            }
        }
    }
    let mut bodies = vec![];
    loops(items, &mut bodies);
    let next = std::sync::atomic::AtomicUsize::new(0);
    let threads = std::thread::available_parallelism().map_or(1, |n| n.get()).min(bodies.len().max(1));
    let done: Vec<(Vec<(usize, Analyzed)>, (usize, usize))> = std::thread::scope(|scope| {
        let workers: Vec<_> = (0..threads)
            .map(|_| {
                scope.spawn(|| {
                    let mut out = vec![];
                    loop {
                        let i = next.fetch_add(1, std::sync::atomic::Ordering::Relaxed);
                        let Some(body) = bodies.get(i) else { break };
                        out.push((i, Analyzed(analysis::analyze(body, funcs, cheap, summaries))));
                    }
                    // (and how many this thread analyzed, and found parallel)
                    (out, analysis::PLANS.with(|p| p.replace((0, 0))))
                })
            })
            .collect();
        workers.into_iter().map(|w| w.join().unwrap()).collect()
    });
    let mut plans = HashMap::default();
    let (mut n, mut ok) = (0, 0);
    for (results, counts) in done {
        n += counts.0;
        ok += counts.1;
        for (i, Analyzed(plan)) in results {
            plans.insert(bodies[i].as_ptr(), std::rc::Rc::new(plan));
        }
    }
    analysis::PLANS.with(|p| {
        let (a, b) = p.get();
        p.set((a + n, b + ok));
    });
    plans
}

/// A loop's analysis, from the thread that worked it out. A plan names ops
/// by their addresses in the program's items (`*const Item`), only as who
/// they are; those items outlive the threads and nothing changes them, so
/// a plan means the same on any thread.
struct Analyzed(Result<Plan, String>);
unsafe impl Send for Analyzed {}

struct Emitter<'a> {
    promote: bool,
    promote_ops: usize,
    /// Whether loops are each done as `promote::region` where they can be:
    /// in a function too big to be done as `promote::function`, and in the
    /// program's own code.
    regions: bool,
    funcs: &'a HashMap<String, &'a [Item]>,
    /// See `OptimizingC::inline_ops`.
    inline_ops: usize,
    /// The functions that leave the stack of saved pointers as they found
    /// it, without looking at what was on it.
    even: &'a crate::asm::fx::HashSet<String>,
    /// The functions that never return (see `stopping`).
    stops: &'a crate::asm::fx::HashSet<String>,
    min: u64,
    /// `min_time`.
    work: u64,
    /// The functions that are routines the target knows, as C that does what
    /// they do (`ORIGINAL` standing for their own code).
    known: &'a HashMap<String, String>,
    /// The functions whose effect is linear, as C that has it.
    linear: &'a HashMap<String, String>,
    /// Those and the known routines: the ones done natively.
    cheap: crate::asm::fx::HashSet<String>,
    /// What each loop's analysis found, by its body (a function's loops are
    /// emitted wherever it's inlined, the same each time).
    plans: HashMap<*const Item, std::rc::Rc<Result<Plan, String>>>,
    /// What the known routines may do, for the analysis.
    summaries: HashMap<String, analysis::Summary>,
    /// The functions whose bodies are being inlined.
    inlining: Vec<String>,
    /// How many ops each function comes to with what it calls inlined.
    sizes: std::cell::RefCell<HashMap<String, usize>>,
    /// The functions only one place in the program calls (or refers to):
    /// inlining those makes nothing bigger.
    once: crate::asm::fx::HashSet<String>,
    /// Loops so far, to number them.
    loops: usize,
    /// While emitting an iteration that runs in parallel: the loops in it
    /// that always start (they're what decides whether it goes on).
    entered: Vec<*const Item>,
    /// While emitting an iteration that runs in parallel: for each op that
    /// accesses memory that's like a cell (see `Plan::scalars`), which, and
    /// where the copies of those start in the thread's window.
    scalars: Option<(HashMap<(Vec<*const Item>, *const Item), usize>, i64)>,
    /// And the ops that read memory that may be read from a copy of how it
    /// was (see `Family::later`): which family (the copy is `bf_sd{i}` bytes
    /// from it, 0 if there's no copy).
    copied: Option<HashMap<(Vec<*const Item>, *const Item), usize>>,
    /// Where the pointer leads, where it's through a pointer in a cell near
    /// it: that cell, and how far on (see `seq_frames`); and that for each
    /// `*` still in effect.
    via: Option<(i64, i64)>,
    saved_via: Vec<Option<(i64, i64)>>,
    /// While writes to some cells are noted (in an iteration running in
    /// parallel): the first cell of the thread's copies, and those cells
    /// (offsets from where the pointer is when the iteration starts); and
    /// whether any code that writes cells without noting it has been
    /// emitted since.
    notes: Option<(i64, std::collections::BTreeSet<i64>)>,
    unnoted: bool,
    /// Where the pointer is, as an offset from where it was when the
    /// iteration started, where that's known (and where it was when each
    /// `*` that's still in effect moved it).
    at: Option<i64>,
    saved_at: Vec<Option<i64>>,
    /// While emitting an iteration that runs in parallel: the ops that read
    /// where only the iteration knows, to check.
    gathers: Option<(crate::asm::fx::HashSet<*const Item>, usize)>,
    /// The calls (their ops) being inlined; and, while emitting an iteration
    /// that runs in parallel, the cells of its stacks each op accesses (see
    /// `Plan::slots`), with each stack's lowest offset.
    call_chain: Vec<*const Item>,
    slots: Option<(HashMap<(Vec<*const Item>, *const Item), (usize, i64)>, Vec<i64>)>,
    /// While emitting an iteration that runs in parallel, if nothing reaches
    /// the cells near the pointer through a pointer: the first of the
    /// thread's copies of them (`bf_win`), which are then accessed directly
    /// wherever it's known which they are, so that the pointer never points
    /// into them (and the C compiler can keep them in registers).
    direct: Option<i64>,
    /// Inside a loop running on its own with copies of the cells near the
    /// pointer (see `seq_loop`).
    seq: Option<Seq>,
    /// How deep in `items` the emitter is (1 for the program's own code,
    /// outside any loop or function).
    depth: usize,
    /// The functions' definitions.
    defs: String,
    /// The definitions so far, a function (with its loops) each.
    chunks: Vec<String>,
    /// How deep in function definitions the emitter is.
    func_depth: usize,
    /// What the loops in main's own code define (they go with main).
    main_defs: String,
}

/// A loop that runs on its own with copies of the cells near the pointer
/// (`bf_win`, from `lo`), as it's emitted: twice, the code that uses the
/// copies (`fast`), and the code that doesn't, which that jumps into (at the
/// same place) if something reaches the cells through a pointer.
/// What `seq_frames` finds.
#[derive(Default)]
struct Frames {
    slots: std::collections::BTreeSet<(i64, i64)>,
    written: std::collections::BTreeSet<i64>,
}

struct Seq {
    id: usize,
    lo: i64,
    fast: bool,
    /// Memory that's like the cells near the pointer (see `seq_frames`):
    /// for each cell holding where it is and each offset from there, its
    /// copy (`bf_fs{j}`); and the cells holding where some is, with the
    /// lowest and highest offsets.
    frames: HashMap<(i64, i64), usize>,
    bases: std::collections::BTreeMap<i64, (i64, i64)>,
    /// The places where the pointer leads elsewhere, so far, by number (the
    /// same in both).
    site: usize,
    /// How many `*`s that pair up are in effect, and the most.
    depth: usize,
    most: usize,
    /// C that copies the cells in, and back.
    copy_in: std::rc::Rc<str>,
    copy_out: std::rc::Rc<str>,
}

/// Whether `items` call a function.
fn calls(items: &[Item]) -> bool {
    items.iter().any(|item| match item {
        Item::Op(op) => *op == Op::Call,
        Item::Loop(body) => calls(body),
        Item::Func(..) => false,
    })
}

/// The cells native code accesses (`ptr[n]`, see `idioms`), from where
/// the pointer is.
fn native_cells(code: &str) -> Vec<i64> {
    let mut out = vec![];
    let mut rest = code;
    while let Some(i) = rest.find("ptr[") {
        rest = &rest[i + 4..];
        if let Some(n) = rest.split_once(']').and_then(|(n, _)| n.parse().ok()) {
            out.push(n);
        }
    }
    out
}

/// An external function (C written with `bf.h`, which takes the pointer's
/// and acc's addresses), and the adapter the program calls it through.
fn external_c(name: &str) -> String {
    format!("void {name}(int64_t **tape, int64_t **ptr, int64_t *acc);\nstatic bf_st bf_x_{name}(int64_t *ptr, int64_t acc) {{ {name}(&tape, &ptr, &acc); return (bf_st){{ptr, acc}}; }}\n")
}

/// An op as C, with the pointer and accumulator in `ptr` and `acc`. (A
/// label is a function's address: of the program's own, or of the adapter
/// to an external one, see `external_c`.)
fn op_c(op: Op, funcs: &HashMap<String, &[Item]>) -> String {
    match op {
        Op::Deref => "*stack = ptr; stack += 1; ptr = (int64_t *)*ptr;".into(),
        Op::Refer => "stack -= 1; ptr = (int64_t *)*stack;".into(),
        Op::Where => "acc = (int64_t)ptr;".into(),
        Op::Move(n) => format!("ptr += {n};"),
        Op::Set(n) => format!("acc = (int64_t){n}ull;"),
        Op::Label(l) if funcs.contains_key(&label_name(&l)) => format!("acc = (int64_t){};", label_name(&l)),
        Op::Label(l) => format!("acc = (int64_t)bf_x_{};", label_name(&l)),
        Op::Add => "acc = (int64_t)((uint64_t)acc + (uint64_t)*ptr);".into(),
        Op::Neg => "acc = (int64_t)(0 - (uint64_t)acc);".into(),
        Op::Positive => "acc = acc > 0;".into(),
        Op::Load => "acc = *ptr;".into(),
        Op::Store => "*ptr = acc;".into(),
        Op::Call => "{ bf_st bf_r = ((bf_st (*)(int64_t *, int64_t))acc)(ptr, acc); ptr = bf_r.ptr; acc = bf_r.acc; }".into(),
        Op::Read => "acc = getchar();".into(),
        Op::Write => "putchar(acc);".into(),
        Op::While | Op::EndWhile | Op::Func | Op::EndFunc => unreachable!("structured"),
    }
}

impl Emitter<'_> {
    /// `items` as C; with `parallel`, loops are run in parallel where they
    /// can be (not inside code that's already running in parallel).
    /// With `inline`, calls to the program's functions (that aren't already
    /// being inlined) are replaced by their bodies, so that nothing in the
    /// code takes the pointer's or acc's address, and the C compiler can keep
    /// them, and the cells near the pointer, in registers.
    fn items(&mut self, items: &[Item], out: &mut String, parallel: bool, inline: bool) {
        self.depth += 1;
        self.items_in(items, out, parallel, inline);
        self.depth -= 1;
    }

    fn items_in(&mut self, items: &[Item], out: &mut String, parallel: bool, inline: bool) {
        // a `*` whose `&` is in the same block, with nothing between that
        // uses the stack unevenly, saves the pointer in a local instead (so
        // it never goes into memory, where it would keep the C compiler from
        // keeping the cells near it in registers)
        let pairs = pairs(items, self.even);
        for (i, item) in items.iter().enumerate() {
            match item {
                Item::Op(op @ (Op::Load | Op::Store | Op::Add | Op::Deref | Op::Refer)) if self.seq.is_some() && (self.at.is_none() || matches!(op, Op::Deref | Op::Refer)) => {
                    self.seq_op(*op, pairs.contains_key(&i), pairs.values().any(|&j| j == i), out);
                }
                Item::Op(Op::Deref) if pairs.contains_key(&i) => {
                    if let Some(c) = self.window_cell(0) {
                        let _ = writeln!(out, "{{ ptr = (int64_t *){c};");
                    } else {
                        *out += &self.gather(item);
                        let from = self.slot(item).unwrap_or_else(|| "*ptr".into());
                        let _ = writeln!(out, "{{ int64_t *bf_saved_ptr = ptr; ptr = (int64_t *){from};");
                    }
                    self.saved_at.push(self.at.take());
                }
                Item::Op(Op::Refer) if pairs.values().any(|&j| j == i) => {
                    self.at = self.saved_at.pop().flatten();
                    // (back to a cell near the pointer, in the copies)
                    *out += if self.direct.is_some() && self.at.is_some() { "}\n" } else { "ptr = bf_saved_ptr; }\n" };
                }
                // (a routine the target knows, or a linear function, is done
                // natively wherever it's called: that's a few instructions)
                Item::Op(Op::Call) if callee(items, i).is_some_and(|f| self.known.contains_key(&f) && !self.inlining.contains(&f)) => {
                    let f = callee(items, i).unwrap();
                    let body = self.funcs[&f];
                    self.inlining.push(f.clone());
                    let mut original = String::new();
                    // (the routine leaves the pointer where it found it)
                    let at = self.at;
                    self.items(body, &mut original, parallel, true);
                    self.at = at;
                    self.inlining.pop();
                    *out += &self.localized(&self.noted(&self.known[&f].replace("ORIGINAL", &original)));
                }
                Item::Op(Op::Call) if callee(items, i).is_some_and(|f| self.linear.contains_key(&f)) => {
                    *out += &self.localized(&self.noted(&self.linear[&callee(items, i).unwrap()]));
                }
                Item::Op(Op::Call) if inline && callee(items, i).is_some_and(|f| self.funcs.contains_key(&f) && !self.inlining.contains(&f) && (!self.plain(parallel) || self.once.contains(&f) || self.size(&f, &mut vec![]) <= self.inline_ops)) => {
                    let f = callee(items, i).unwrap();
                    let body = self.funcs[&f];
                    self.inlining.push(f);
                    self.call_chain.push(item);
                    *out += "{\n";
                    self.items(body, out, parallel, true);
                    *out += "}\n";
                    self.call_chain.pop();
                    self.inlining.pop();
                }
                Item::Op(op @ (Op::Move(_) | Op::Load | Op::Store | Op::Add | Op::Deref | Op::Refer | Op::Where)) if self.direct.is_some() && (self.at.is_some() || (*op == Op::Refer && matches!(self.saved_at.last(), Some(Some(_))))) => {
                    // (a cell near the pointer, in the copies)
                    let c = self.window_cell(0).unwrap_or_default();
                    match op {
                        Op::Move(n) => self.at = self.at.map(|a| a + n),
                        Op::Load => {
                            let _ = writeln!(out, "acc = {c};");
                        }
                        Op::Store => {
                            let _ = writeln!(out, "{c} = acc;{}", self.note(0));
                        }
                        Op::Add => {
                            let _ = writeln!(out, "acc = (int64_t)((uint64_t)acc + (uint64_t){c});");
                        }
                        Op::Deref => {
                            let _ = writeln!(out, "ptr = (int64_t *){c};");
                            self.saved_at.push(self.at.take());
                        }
                        Op::Refer => self.at = self.saved_at.pop().flatten(),
                        // (where it is, in the tape: what that's used for
                        // doesn't depend on it)
                        _ => {
                            let _ = writeln!(out, "acc = (int64_t)(intptr_t)(bf_p0 + ({}));", self.at.unwrap());
                        }
                    }
                }
                Item::Op(op @ (Op::Load | Op::Store | Op::Add | Op::Deref)) if self.slot(item).is_some() => {
                    // (a cell of a stack the thread has its own of, as its
                    // own variable)
                    let c = self.slot(item).unwrap();
                    let _ = writeln!(
                        out,
                        "{}",
                        match op {
                            Op::Load => format!("acc = {c};"),
                            Op::Store => format!("{c} = acc;{}", self.slot_note(item)),
                            Op::Add => format!("acc = (int64_t)((uint64_t)acc + (uint64_t){c});"),
                            _ => format!("*stack = ptr; stack += 1; ptr = (int64_t *){c};"),
                        }
                    );
                    if *op == Op::Deref {
                        self.saved_at.push(self.at.take());
                    }
                }
                Item::Op(op @ (Op::Load | Op::Add | Op::Deref)) if self.copy(item).is_some() => {
                    // (memory read as it was, from a copy, if there is one)
                    let c = format!("*(int64_t *)((char *)ptr + bf_sd{})", self.copy(item).unwrap());
                    let _ = writeln!(
                        out,
                        "{}",
                        match op {
                            Op::Load => format!("acc = {c};"),
                            Op::Add => format!("acc = (int64_t)((uint64_t)acc + (uint64_t){c});"),
                            _ => format!("*stack = ptr; stack += 1; ptr = (int64_t *){c};"),
                        }
                    );
                    if *op == Op::Deref {
                        self.saved_at.push(self.at.take());
                    }
                }
                Item::Op(op) => {
                    if matches!(op, Op::Load | Op::Add | Op::Deref) {
                        *out += &self.gather(item);
                    }
                    *out += &op_c(*op, self.funcs);
                    match op {
                        Op::Move(n) => {
                            self.at = self.at.map(|a| a + n);
                            self.via = self.via.map(|(c, k)| (c, k + n));
                        }
                        Op::Deref => self.saved_at.push(self.at.take()),
                        Op::Refer => self.at = self.saved_at.pop().flatten(),
                        Op::Store => *out += &self.note(0),
                        Op::Call => {
                            self.unnoted = true;
                            self.at = None;
                        }
                        _ => {}
                    }
                    out.push('\n');
                }
                Item::Func(name, body) => {
                    // (what main's own loops have defined so far is main's,
                    // not this function's part)
                    if self.func_depth == 0 {
                        let mains = std::mem::take(&mut self.defs);
                        self.main_defs += &mains;
                    }
                    self.func_depth += 1;
                    let mut code = String::new();
                    if let Some(native) = self.known.get(name) {
                        // (the machine's instructions, for a routine the
                        // target knows)
                        let mut original = String::new();
                        self.items(body, &mut original, parallel, false);
                        code += &native.replace("ORIGINAL", &original);
                    } else if let Some(c) = self.linear.get(name) {
                        // (straight-line code, if its effect is linear)
                        code += c;
                    } else if let Some((c, plain)) = Some(()).filter(|_| self.promote && !parallel).and_then(|()| promote::function(name, body, self.promote_ops, self.funcs, self.stops, self.known, self.linear)) {
                        // (its cells as variables, where it can be done)
                        code += &c;
                        self.defs += &plain;
                    } else {
                        // (or each loop's, where that can be done)
                        let regions = std::mem::replace(&mut self.regions, self.promote && !parallel);
                        self.items(body, &mut code, parallel, false);
                        self.regions = regions;
                    }
                    let _ = write!(
                        self.defs,
                        "\nBF_LINK bf_st {name}(int64_t *ptr, int64_t acc) {{\n{}{code}return (bf_st){{ptr, acc}};\n}}\n",
                        // (only a function that calls others can recurse)
                        if calls(body) { "BF_STACK_CHECK\n" } else { "" }
                    );
                    // (a function and the loops in it are a part of their
                    // own, to go in whichever file: see `CSource::units`)
                    self.func_depth -= 1;
                    if self.func_depth == 0 {
                        self.chunks.push(std::mem::take(&mut self.defs));
                    }
                }
                Item::Loop(body) => {
                    // (its cells as variables, where that can be done; after
                    // it, the pointer may be anywhere, if the plain code took
                    // over)
                    if self.regions && self.inlining.is_empty() && self.seq.is_none() && self.direct.is_none() && self.notes.is_none() && self.gathers.is_none() && self.slots.is_none() && self.scalars.is_none() && self.copied.is_none() && self.via.is_none() {
                        if let Some((c, plain)) = promote::region(self.loops + 1, item, self.funcs, self.stops, self.known, self.linear) {
                            self.loops += 1;
                            *out += &c;
                            self.defs += &plain;
                            self.at = None;
                            continue;
                        }
                    }
                    // (a loop in an iteration that's running in parallel
                    // leaves the pointer where it found it)
                    let at = self.at;
                    // (what comes after it, if that's the rest of the program)
                    let after = Some(&items[i + 1..]).filter(|_| self.depth == 1);
                    if !self.seq_loop(body, after, out, parallel) {
                        self.loop_item(body, after, out, parallel, inline);
                    }
                    self.at = at;
                }
            }
        }
    }

    /// Whether this is ordinary code, that can call a function instead of
    /// inlining it: not code running in parallel (`parallel` is false there),
    /// or with copies of cells, or noting what it writes.
    fn plain(&self, parallel: bool) -> bool {
        parallel && self.seq.is_none() && self.direct.is_none() && self.notes.is_none() && self.gathers.is_none() && self.slots.is_none() && self.scalars.is_none() && self.copied.is_none() && self.via.is_none()
    }

    /// How many ops a function comes to with the calls in it to the
    /// program's functions inlined (but not ones already on `stack`), loops
    /// counting twice (they're emitted more than once). (Up to a limit.)
    fn size(&self, f: &str, stack: &mut Vec<String>) -> usize {
        if let Some(&n) = self.sizes.borrow().get(f) {
            return n;
        }
        fn count(e: &Emitter, items: &[Item], stack: &mut Vec<String>) -> usize {
            let mut n = 0usize;
            for (i, item) in items.iter().enumerate() {
                n = n.saturating_add(match item {
                    Item::Op(Op::Call) => match callee(items, i) {
                        Some(g) if e.funcs.contains_key(&g) && !e.known.contains_key(&g) && !e.linear.contains_key(&g) && !stack.contains(&g) => e.size(&g, stack),
                        _ => 1,
                    },
                    Item::Op(_) => 1,
                    Item::Loop(body) => count(e, body, stack).saturating_mul(2),
                    Item::Func(..) => 0,
                });
                if n > e.inline_ops.max(INLINE_OPS) * 4 {
                    break;
                }
            }
            n
        }
        stack.push(f.to_string());
        let n = count(self, self.funcs[f], stack);
        stack.pop();
        // (what's on the stack makes it smaller than it is: only kept if
        // nothing was)
        if stack.is_empty() {
            self.sizes.borrow_mut().insert(f.to_string(), n);
        }
        n
    }

    /// An op that accesses memory through the pointer, or moves it there (or
    /// back), in a loop running on its own with copies of the cells near the
    /// pointer (see `seq_loop`).
    fn seq_op(&mut self, op: Op, paired_deref: bool, paired_refer: bool, out: &mut String) {
        let cell = self.window_cell(0);
        let seq = self.seq.as_mut().unwrap();
        let (id, lo, fast) = (seq.id, seq.lo, seq.fast);
        // (memory that's like a cell, which has a copy, where the pointer
        // leads there)
        let copy = self.via.and_then(|cv| seq.frames.get(&cv).copied());
        let others: String = seq.bases.keys().map(|c| format!(" || (uintptr_t)ptr - bf_flo{n} < bf_fsz{n}", n = c_name(*c))).collect();
        // (where the pointer is elsewhere, the code that uses the copies first
        // checks it's not at one of their cells, and the code that doesn't
        // has a label there to carry on from if it is)
        let site = |out: &mut String, seq: &mut Seq| {
            let k = seq.site;
            seq.site += 1;
            if fast {
                let _ = writeln!(out, "if ((uintptr_t)ptr - (uintptr_t)(bf_p0 + ({lo})) < sizeof bf_win{others}) goto bf_bail{id}_{k};");
            } else {
                let _ = writeln!(out, "bf_slow{id}_{k}:;");
            }
        };
        if matches!(op, Op::Deref) {
            self.saved_via.push(self.via);
            self.via = self.at.map(|a| (a, 0));
        }
        if op == Op::Refer {
            self.via = self.saved_via.pop().flatten();
        }
        match (op, self.at) {
            (Op::Deref, Some(a)) => {
                // (from a cell near the pointer: where it'd be in the tape is
                // what's saved)
                let from = if fast { cell.unwrap() } else { "*ptr".into() };
                if paired_deref {
                    let d = seq.depth;
                    seq.depth += 1;
                    seq.most = seq.most.max(seq.depth);
                    let _ = writeln!(out, "bf_sv{d} = bf_p0 + ({a}); ptr = (int64_t *){from};");
                } else {
                    let _ = writeln!(out, "*stack = bf_p0 + ({a}); stack += 1; ptr = (int64_t *){from};");
                }
                self.saved_at.push(Some(a));
                self.at = None;
            }
            (Op::Deref, None) => {
                // (a copy's place, if it has one, which the other code still
                // numbers)
                let from = match copy {
                    Some(j) => {
                        seq.site += 1;
                        format!("bf_fs{j}")
                    }
                    None => {
                        site(out, seq);
                        "*ptr".to_string()
                    }
                };
                if paired_deref {
                    let d = seq.depth;
                    seq.depth += 1;
                    seq.most = seq.most.max(seq.depth);
                    let _ = writeln!(out, "bf_sv{d} = ptr; ptr = (int64_t *){from};");
                } else {
                    let _ = writeln!(out, "*stack = ptr; stack += 1; ptr = (int64_t *){from};");
                }
                self.saved_at.push(None);
            }
            (Op::Refer, _) => {
                if paired_refer {
                    seq.depth -= 1;
                    let _ = writeln!(out, "ptr = bf_sv{};", seq.depth);
                } else {
                    *out += "stack -= 1; ptr = (int64_t *)*stack;\n";
                }
                self.at = self.saved_at.pop().flatten();
            }
            (op, None) => match copy {
                Some(j) => {
                    seq.site += 1;
                    let _ = writeln!(
                        out,
                        "{}",
                        match op {
                            Op::Load => format!("acc = bf_fs{j};"),
                            Op::Store => format!("bf_fs{j} = acc;"),
                            _ => format!("acc = (int64_t)((uint64_t)acc + (uint64_t)bf_fs{j});"),
                        }
                    );
                }
                None => {
                    site(out, seq);
                    *out += &op_c(op, self.funcs);
                    out.push('\n');
                }
            },
            _ => unreachable!("a cell near the pointer"),
        }
    }

    /// Whether a loop's body (from `at`, where the pointer is) is one that
    /// can run with copies of the cells near the pointer: wherever it's at a
    /// cell near the pointer, it's known which (the loops inside leave the
    /// pointer where they found it, and every call is to one of the
    /// program's functions, which can be inlined). Collects those cells;
    /// gives where it ends up.
    fn seq_window(&self, items: &[Item], mut at: Option<i64>, saved: &mut Vec<Option<i64>>, inlining: &mut Vec<String>, cells: &mut std::collections::BTreeSet<i64>) -> Option<Option<i64>> {
        for (i, item) in items.iter().enumerate() {
            match item {
                Item::Op(Op::Move(n)) => at = at.map(|a| a + n),
                Item::Op(Op::Load | Op::Store | Op::Add) => {
                    if let Some(a) = at {
                        cells.insert(a);
                    }
                }
                Item::Op(Op::Deref) => {
                    if let Some(a) = at {
                        cells.insert(a);
                    }
                    saved.push(at.take());
                }
                Item::Op(Op::Refer) => at = saved.pop()?,
                Item::Op(Op::Call) => {
                    let f = callee(items, i).filter(|f| self.funcs.contains_key(f) && !inlining.contains(f) && (self.known.contains_key(f) || self.once.contains(f) || self.size(f, &mut vec![]) <= self.inline_ops))?;
                    let start = at?;
                    // (the cells the native code that does it accesses, too:
                    // a linear function's are what its ops reach through
                    // pointers as well as at fixed places)
                    if let Some(code) = self.known.get(&f).or_else(|| self.linear.get(&f)) {
                        cells.extend(native_cells(code).into_iter().map(|n| start + n));
                    }
                    inlining.push(f.clone());
                    let end = self.seq_window(self.funcs[&f], at, saved, inlining, cells);
                    inlining.pop();
                    at = Some(end??);
                }
                Item::Op(Op::Func | Op::EndFunc | Op::While | Op::EndWhile) | Item::Func(..) => return None,
                Item::Op(_) => {}
                Item::Loop(body) => {
                    let depth = saved.len();
                    if self.seq_window(body, at, saved, inlining, cells)? != at || saved.len() != depth {
                        return None;
                    }
                }
            }
        }
        Some(at)
    }

    /// Where a loop's body (that `seq_window` takes) accesses memory through
    /// a pointer in one of the cells near the pointer, the cell and how far
    /// from where it points (in cells): `via` is that, where it's known; and
    /// which cells near the pointer it writes. (Memory a cell the body never
    /// writes points to is always the same memory.)
    fn seq_frames(&self, items: &[Item], mut at: Option<i64>, mut via: Option<(i64, i64)>, saved: &mut Vec<(Option<i64>, Option<(i64, i64)>)>, inlining: &mut Vec<String>, scan: &mut Frames) {
        for (i, item) in items.iter().enumerate() {
            match item {
                Item::Op(Op::Move(n)) => {
                    at = at.map(|a| a + n);
                    via = via.map(|(c, k)| (c, k + n));
                }
                Item::Op(op @ (Op::Load | Op::Store | Op::Add | Op::Deref)) => {
                    match (at, via) {
                        (Some(a), _) if *op == Op::Store => {
                            scan.written.insert(a);
                        }
                        (Some(_), _) => {}
                        (None, Some(cv)) => {
                            scan.slots.insert(cv);
                        }
                        (None, None) => {}
                    }
                    if *op == Op::Deref {
                        saved.push((at, via));
                        via = at.map(|a| (a, 0));
                        at = None;
                    }
                }
                Item::Op(Op::Refer) => {
                    let Some(back) = saved.pop() else { return };
                    (at, via) = back;
                }
                Item::Op(Op::Call) => {
                    if let Some(f) = callee(items, i).filter(|f| self.funcs.contains_key(f) && !inlining.contains(f)) {
                        inlining.push(f.clone());
                        self.seq_frames(self.funcs[&f], at, via, saved, inlining, scan);
                        inlining.pop();
                    }
                }
                Item::Op(_) | Item::Func(..) => {}
                Item::Loop(body) => self.seq_frames(body, at, via, saved, inlining, scan),
            }
        }
    }

    /// A loop, if it can, run with copies of the cells near the pointer that
    /// it uses (as the C compiler's to keep in registers), copied back after
    /// it. Wherever it accesses memory through a pointer, it checks that's
    /// not one of those cells; if it is, it copies them back and carries on,
    /// from there, in code that uses the cells themselves. Gives whether it
    /// did.
    fn seq_loop(&mut self, body: &[Item], after: Option<&[Item]>, out: &mut String, parallel: bool) -> bool {
        if self.seq.is_some() || self.direct.is_some() || self.notes.is_some() || self.gathers.is_some() || self.slots.is_some() || self.scalars.is_some() {
            return false;
        }
        let mut cells = std::collections::BTreeSet::new();
        if self.seq_window(body, Some(0), &mut vec![], &mut self.inlining.clone(), &mut cells) != Some(Some(0)) || cells.is_empty() {
            return false;
        }
        let (lo, hi) = (*cells.first().unwrap(), *cells.last().unwrap());
        if hi - lo > 512 {
            return false;
        }
        // (and copies of the memory that's like them, of a few)
        let mut scan = Frames::default();
        self.seq_frames(body, Some(0), None, &mut vec![], &mut self.inlining.clone(), &mut scan);
        // (all of them at once, unless it uses few of them: those, one by one)
        let (copy_in, copy_out): (std::rc::Rc<str>, std::rc::Rc<str>) = if (cells.len() as i64) * 4 < hi - lo + 1 {
            (cells.iter().map(|c| format!("bf_win[{}] = bf_p0[{c}];\n", c - lo)).collect::<String>().into(), cells.iter().map(|c| format!("bf_p0[{c}] = bf_win[{}];\n", c - lo)).collect::<String>().into())
        } else {
            (format!("memcpy(bf_win, bf_p0 + ({lo}), sizeof bf_win);\n").into(), format!("memcpy(bf_p0 + ({lo}), bf_win, sizeof bf_win);\n").into())
        };
        let mut frames = HashMap::default();
        let mut bases: std::collections::BTreeMap<i64, (i64, i64)> = std::collections::BTreeMap::new();
        for &(c, k) in scan.slots.iter().filter(|(c, _)| cells.contains(c) && !scan.written.contains(c)).take(32) {
            frames.insert((c, k), frames.len());
            let r = bases.entry(c).or_insert((k, k));
            *r = (r.0.min(k), r.1.max(k));
        }
        self.loops += 1;
        let id = self.loops;
        let saved = (self.at, std::mem::take(&mut self.saved_at), self.via.take(), std::mem::take(&mut self.saved_via));
        // the code that uses the copies
        self.seq = Some(Seq { id, lo, fast: true, frames: frames.clone(), bases: bases.clone(), site: 0, depth: 0, most: 0, copy_in: copy_in.clone(), copy_out: copy_out.clone() });
        self.direct = Some(lo);
        self.at = Some(0);
        let mut fast = String::new();
        self.loop_item(body, after, &mut fast, parallel, true);
        let (sites, most) = { let s = self.seq.as_ref().unwrap(); (s.site, s.most) };
        // and the code that doesn't, for if it has to carry on without them
        self.seq = Some(Seq { id, lo, fast: false, frames: HashMap::default(), bases: std::collections::BTreeMap::new(), site: 0, depth: 0, most: 0, copy_in: copy_in.clone(), copy_out: copy_out.clone() });
        self.direct = None;
        self.at = Some(0);
        let mut slow = String::new();
        self.loop_item(body, None, &mut slow, false, true);
        let most = most.max(self.seq.as_ref().unwrap().most);
        self.seq = None;
        (self.at, self.saved_at, self.via, self.saved_via) = saved;
        // (none of it if it doesn't start)
        let _ = write!(out, "/* loop {id}: with copies of the cells near the pointer */\nif (acc) {{\nint64_t *bf_p0 = ptr;\nint64_t bf_win[{}];\n{copy_in}", hi - lo + 1);
        for d in 0..most {
            let _ = writeln!(out, "int64_t *bf_sv{d} = 0;\n(void)bf_sv{d};");
        }
        // (the memory that's like the cells: copied if it's apart from them,
        // and from each other's, and otherwise it's all done without copies)
        let mut back = String::new();
        if !frames.is_empty() {
            for (c, (k0, k1)) in &bases {
                let _ = writeln!(out, "uintptr_t bf_flo{n} = (uintptr_t)((int64_t *)bf_win[{}] + ({k0})), bf_fsz{n} = {};", c - lo, (k1 - k0 + 1) * 8, n = c_name(*c));
            }
            let ranges: Vec<String> = bases.keys().map(|c| format!("bf_flo{n}, bf_flo{n} + bf_fsz{n} - 1", n = c_name(*c))).collect();
            let mut apart = vec![format!("bf_apart((__int128)(uintptr_t)(bf_p0 + ({lo})), (__int128)(uintptr_t)(bf_p0 + ({hi})) + 7, {})", ranges[0])];
            for i in 0..ranges.len() {
                for j in i + 1..ranges.len() {
                    apart.push(format!("bf_apart({}, {})", ranges[i], ranges[j]));
                }
                if i > 0 {
                    apart.push(format!("bf_apart((__int128)(uintptr_t)(bf_p0 + ({lo})), (__int128)(uintptr_t)(bf_p0 + ({hi})) + 7, {})", ranges[i]));
                }
            }
            // (they're read before the loop needs them, which it might not:
            // only if they're on the tape, where reading anything is safe)
            for c in bases.keys() {
                apart.push(format!("bf_flo{n} - (uintptr_t)tape <= BF_CELLS * sizeof(int64_t) - bf_fsz{n}", n = c_name(*c)));
            }
            let _ = writeln!(out, "if (!({})) goto bf_slow{id}_start;", apart.join(" && "));
            let mut sorted: Vec<(&(i64, i64), &usize)> = frames.iter().collect();
            sorted.sort_by_key(|f| f.1);
            for (&(c, k), j) in sorted {
                let at = format!("((int64_t *)bf_win[{}])[{k}]", c - lo);
                let _ = writeln!(out, "int64_t bf_fs{j} = {at};");
                let _ = writeln!(back, "{at} = bf_fs{j};");
            }
        }
        let _ = write!(out, "{fast}{back}{copy_out}ptr = bf_p0;\ngoto bf_done{id};\n");
        for k in 0..sites {
            let _ = writeln!(out, "bf_bail{id}_{k}:\n{back}{copy_out}goto bf_slow{id}_{k};");
        }
        let _ = writeln!(out, "bf_slow{id}_start:;\n{slow}bf_done{id}:;\n}}");
        true
    }

    /// A loop, in parallel where it can be (see `items`).
    fn loop_item(&mut self, body: &[Item], after: Option<&[Item]>, out: &mut String, parallel: bool, inline: bool) {
        self.loops += 1;
        let id = self.loops;
        let plan = if parallel {
            let (funcs, cheap, summaries) = (self.funcs, &self.cheap, &self.summaries);
            Some(self.plans.entry(body.as_ptr()).or_insert_with(|| std::rc::Rc::new(analysis::analyze(body, funcs, cheap, summaries))).clone())
        } else {
            None
        };
        match plan.as_deref() {
            Some(Ok(plan)) => {
                // the loop runs as it would for a few iterations (so that
                // short loops cost almost nothing more), then the rest but the
                // last run in the code for running in parallel: on one thread
                // a part at a time, timed, until the rest is worth starting
                // threads for (see `parallel_loop`). The code that does that
                // is a function of its own, out of the way of the loop's.
                // (Not after 16 iterations, but straight away, if an iteration
                // looks like a lot of work, or `min_time` is tiny, or it took
                // long enough the last time the loop ran.)
                let start = if self.work == 0 { 0 } else if self.work < 1000 || plan.cost > 1000 { 1 } else { 16 };
                // (and if the last time it was found by running what decides
                // it, and ran on one thread, or the checks failed, it just
                // runs, but for one time in 16)
                let _ = writeln!(self.defs, "\nstatic double bf_timed{id} = 0, bf_need{id} = {}.0;\nstatic int bf_small{id} = 0, bf_entered{id} = 0;", self.work);
                // (an innermost loop runs the iterations before that in a copy
                // of its own, and the rest in one that doesn't count them)
                // (loops in it that have none in them are `if`s, mostly)
                let innermost = !body.iter().any(|i| matches!(i, Item::Loop(b) if b.iter().any(|j| matches!(j, Item::Loop(_)))));
                let at = self.at;
                let _ = write!(
                    out,
                    "{{\nint64_t bf_seen = 0, bf_next = {};\n{}while (acc) {{\nif (__builtin_expect(bf_seen++ == bf_next, 0)\n#ifdef _OPENMP\n    && !omp_in_parallel()\n#endif\n) {{\nbf_next = -1;\n",
                    if self.work == 0 { "0".to_string() } else { format!("bf_small{id} && (bf_entered{id}++ & 15) ? -1 : bf_timed{id} * 16 > {}.0 ? 1 : {start}", self.work / 4) },
                    if innermost { "if (bf_next >= 0)\n" } else { "" }
                );
                // the cells it writes that nothing after it reads before
                // writing them (or that the program ends without reading)
                let candidates: Vec<i64> = plan.cells.iter().filter(|(o, r)| **o < SCALAR && matches!(r, Role::Private | Role::Maybe)).map(|(&o, _)| o).collect();
                let dead = match after {
                    Some(after) if !candidates.is_empty() => dead_after(after, &candidates, self.funcs),
                    _ => std::collections::BTreeSet::new(),
                };
                let mut scaffold = String::new();
                self.parallel_loop(id, body, plan, &dead, &mut scaffold);
                let _ = write!(self.defs, "\n/* loop {id}, in parallel */\nstatic __attribute__((noinline)) void bf_loop{id}(int64_t *ptr) {{\ndouble bf_per = bf_timed{id};\n{scaffold}}}\n");
                let then = if innermost { "break;\n" } else { "" };
                match &self.seq {
                    // (the cells as they are, for it)
                    Some(seq) if seq.fast => {
                        let (lo, copy_in, copy_out) = (seq.lo, seq.copy_in.clone(), seq.copy_out.clone());
                        let at = self.at.map_or("ptr".to_string(), |a| format!("bf_p0 + ({a})"));
                        // (and the memory that's like them)
                        let (mut back, mut again) = (String::new(), String::new());
                        let mut copies: Vec<(&(i64, i64), &usize)> = seq.frames.iter().collect();
                        copies.sort_by_key(|f| f.1);
                        for (&(c, k), j) in copies {
                            let _ = writeln!(back, "((int64_t *)bf_win[{}])[{k}] = bf_fs{j};", c - lo);
                            let _ = writeln!(again, "bf_fs{j} = ((int64_t *)bf_win[{}])[{k}];", c - lo);
                        }
                        let _ = writeln!(out, "{back}{copy_out}bf_loop{id}({at});\n{copy_in}{again}{then}}}");
                    }
                    _ => {
                        let _ = writeln!(out, "bf_loop{id}(ptr);\n{then}}}");
                    }
                }
                let site = self.seq.as_ref().map(|s| s.site);
                self.items(body, out, parallel, true);
                *out += "}\n";
                if innermost {
                    // (the same places to carry on from in the code without
                    // copies, as the same ops)
                    self.at = at;
                    if let (Some(seq), Some(site)) = (self.seq.as_mut(), site) {
                        seq.site = site;
                    }
                    *out += "while (acc) {\n";
                    self.items(body, out, parallel, true);
                    *out += "}\n";
                }
                *out += "}\n";
            }
            why => {
                if let Some(Err(why)) = why {
                    let _ = writeln!(out, "/* loop {id}: sequential: {} */", why.replace("*/", "* /"));
                }
                // (the loop's own iterations can have parallel
                // loops in them, unless this is already running
                // in parallel)
                if self.entered.contains(&body.as_ptr()) {
                    // (one the iteration always starts)
                    let entered = std::mem::take(&mut self.entered);
                    *out += "do {\n";
                    self.items(body, out, parallel, inline);
                    *out += "} while (acc);\n";
                    self.entered = entered;
                } else {
                    *out += "while (acc) {\n";
                    self.items(body, out, parallel, inline);
                    *out += "}\n";
                }
            }
        }
    }

    /// The code that runs the iterations of a loop but the last in
    /// parallel, from the start of one (with acc not 0), leaving the cells as
    /// the last finds them, if the checks pass and it's worth it.
    fn parallel_loop(&mut self, id: usize, body: &[Item], plan: &Plan, dead: &std::collections::BTreeSet<i64>, out: &mut String) {
        // (its code is its own: not that of a loop around it)
        let outer = (self.seq.take(), self.direct.take(), self.at, std::mem::take(&mut self.saved_at));
        self.parallel_loop_in(id, body, plan, dead, out);
        (self.seq, self.direct, self.at, self.saved_at) = outer;
    }

    fn parallel_loop_in(&mut self, id: usize, body: &[Item], plan: &Plan, dead: &std::collections::BTreeSet<i64>, out: &mut String) {
        let cells: Vec<(i64, &Role)> = plan.cells.iter().map(|(&o, r)| (o, r)).collect();
        let lo = cells.iter().map(|c| c.0).filter(|&o| o < SCALAR).min().unwrap_or(0).min(0);
        let hi = cells.iter().map(|c| c.0).filter(|&o| o < SCALAR).max().unwrap_or(0).max(0);
        // (the thread's copies of memory that's like a cell come after
        // those of the cells near the pointer: where each copy is, and where
        // what it's a copy of is)
        let width = hi - lo + 1;
        let full = width + plan.scalars.len() as i64;
        let win = |o: i64| if o >= SCALAR { width + o - SCALAR } else { o - lo };
        let home = |o: i64| match plan.scalars.get((o - SCALAR) as usize) {
            Some(sc) if o >= SCALAR => format!("(*(int64_t *)((char *)(intptr_t)bf_p0[{}] + ({})))", sc.cell, sc.off),
            _ => format!("bf_p0[{o}]"),
        };
        let inductions: Vec<(i64, &Lin)> = cells.iter().filter_map(|&(o, r)| if let Role::Induction(s) = r { Some((o, s)) } else { None }).collect();
        let reductions: Vec<i64> = cells.iter().filter(|(_, r)| **r == Role::Reduction).map(|c| c.0).collect();
        let how = match plan.trip {
            Trip::Linear { .. } => "its count solved",
            Trip::Slice(_) => "its count found by running what decides it",
            Trip::Compare { .. } => "its count solved from a comparison",
        };
        let _ = writeln!(
            out,
            "/* loop {id}: in parallel when the checks pass ({how}; {} induction variables, {} reductions, {} cells only some iterations write ({} maximums or minimums), {} cells nothing reads after it, {} stacks, {} memory families; about {} ops an iteration) */",
            inductions.len(),
            reductions.len(),
            cells.iter().filter(|c| *c.1 == Role::Maybe).count(),
            plan.extremes.len(),
            dead.len(),
            plan.private.len(),
            plan.shared.len(),
            plan.cost
        );
        let ex = Exprs { plan };
        *out += "int64_t *bf_p0 = ptr;\nint bf_ok = 1;\nint64_t bf_m = -1;\nint bf_threads = 1;\n(void)bf_threads;\n#ifdef BF_STATS\ndouble bf_ts = bf_now();\n#endif\n";
        // what the induction and reduction variables start with, and the
        // inductions' steps
        for &(o, step) in &inductions {
            let _ = writeln!(out, "int64_t bf_e{} = {};\nint64_t bf_s{} = {};", c_name(o), home(o), c_name(o), ex.entry(step));
        }
        for &o in &reductions {
            let _ = writeln!(out, "int64_t bf_e{} = {};", c_name(o), home(o));
        }
        // a thread's copies of the cells near the pointer, and of stacks,
        // and how each iteration starts
        // (what each thread only reads is its own copy, so that the C compiler
        // knows that nothing the iterations write changes it)
        let mut fp = String::from("bf_p0");
        for &(o, _) in &inductions {
            let _ = write!(fp, ", bf_e{n}, bf_s{n}", n = c_name(o));
        }
        for &o in &reductions {
            let _ = write!(fp, ", bf_e{}", c_name(o));
        }
        // (each thread's own pointer and accumulator, too)
        let mut setup = format!(
            "int64_t *ptr;\nint64_t acc;\nint64_t bf_win[{full}];\nmemcpy(bf_win, bf_p0 + ({lo}), {width} * sizeof(int64_t));\nint64_t *bf_ptrs[1024];\nint64_t **bf_saved = stack;\nstack = bf_ptrs;\n"
        );
        for j in 0..plan.scalars.len() as i64 {
            let _ = writeln!(setup, "bf_win[{}] = {};", width + j, home(SCALAR + j));
        }
        let mut teardown = String::from("stack = bf_saved;\n");
        for (i, &(cell, plo, phi)) in plan.private.iter().enumerate() {
            let size = (phi - plo) / 8 + 1;
            let _ = writeln!(
                setup,
                "int64_t *bf_stack{i} = malloc({size} * sizeof(int64_t));\nbf_win[{}] = (int64_t)(intptr_t)((char *)bf_stack{i} - ({plo}));",
                cell - lo
            );
            let _ = writeln!(teardown, "free(bf_stack{i});");
        }
        let mut start = String::new();
        for &(o, _) in &inductions {
            let n = c_name(o);
            let _ = writeln!(start, "bf_win[{}] = (int64_t)((uint64_t)bf_e{n} + (uint64_t)bf_s{n} * (uint64_t)bf_k);", win(o));
        }
        for &o in &reductions {
            let _ = writeln!(start, "bf_win[{}] = bf_e{};", win(o), c_name(o));
        }
        let _ = writeln!(start, "ptr = bf_win - ({lo});\nacc = 1;");

        // (whether memory is read from a copy of how it was: always, for what
        // later iterations write in memory that's written; and for memory
        // that isn't, if the checks find that's all that writes it)
        let copies: Vec<usize> = (0..plan.shared.len()).filter(|&i| plan.copied.values().any(|&j| j == i)).collect();
        for &i in &copies {
            let _ = writeln!(out, "int bf_cp{i} = {};", u8::from(plan.shared[i].written()));
        }
        // the checks that need no count first, then the count, then all
        *out += &ex.checks(lo, hi, "1");
        *out += "{\n";
        match &plan.trip {
            Trip::Linear { alpha, beta } => {
                let _ = writeln!(
                    out,
                    "if (bf_ok) {{\nint64_t bf_a = {}, bf_b = {};\nif (bf_b == 1 || bf_b == -1) bf_m = bf_b == 1 ? (int64_t)(0 - (uint64_t)bf_a) : bf_a;\nelse if (bf_b != 0 && bf_a % bf_b == 0) bf_m = -(bf_a / bf_b);\nif (bf_m < 0 || bf_m > ((int64_t)1 << 40)) bf_ok = 0;\n}}",
                    ex.entry(alpha),
                    ex.stride(beta)
                );
            }
            Trip::Compare { x, parts } => {
                // what a cell holds as iteration `k` starts, exactly
                let at = |o: i64, k: &str| match plan.cells.get(&o) {
                    Some(Role::Induction(_)) => format!("((__int128)bf_e{n} + (__int128)bf_s{n} * {k})", n = c_name(o)),
                    _ => format!("(__int128){}", home(o)),
                };
                fn value(l: &analysis::CellLin, k: &str, at: &dyn Fn(i64, &str) -> String) -> String {
                    let mut e = format!("((__int128){}", l.c);
                    for &(o, c) in &l.terms {
                        let _ = write!(e, " + (__int128){c} * {}", at(o, k));
                    }
                    for (a, c) in &l.loads {
                        let _ = write!(e, " + (__int128){c} * (__int128)*(int64_t *)(intptr_t)(int64_t){}", value(a, k, at));
                    }
                    e + ")"
                }
                let value = |l: &analysis::CellLin, k: &str| value(l, k, &at);
                // it goes on while x > 0: the first k where it isn't
                let _ = writeln!(
                    out,
                    "if (bf_ok) {{\n__int128 bf_xa = {}, bf_xb = {} - bf_xa;\nif (bf_xa <= 0) bf_m = 0;\nelse if (bf_xb >= 0) bf_ok = 0;\nelse {{\n__int128 bf_n = (bf_xa - bf_xb - 1) / -bf_xb;\nif (bf_n > ((__int128)1 << 40)) bf_ok = 0;\nelse bf_m = (int64_t)bf_n;\n}}\n}}",
                    value(x, "0"),
                    value(x, "1")
                );
                // (and what's compared, and the induction variables in it,
                // don't wrap round over those iterations: they're linear, so
                // it's enough that they don't at the ends)
                *out += "if (bf_ok) {\n";
                let mut checked: Vec<(analysis::CellLin, bool)> = parts.clone();
                for &(o, _) in x.terms.iter().chain(parts.iter().flat_map(|p| p.0.terms.iter())) {
                    if matches!(plan.cells.get(&o), Some(Role::Induction(_))) {
                        checked.push((analysis::CellLin { c: 0, terms: vec![(o, 1)], loads: vec![] }, false));
                    }
                }
                for (p, nonneg) in &checked {
                    for k in ["(__int128)0", "(__int128)bf_m"] {
                        let lo = if *nonneg { "0" } else { "(__int128)INT64_MIN" };
                        let _ = writeln!(out, "{{ __int128 bf_v = {}; if (bf_v < {lo} || bf_v > (__int128)INT64_MAX) bf_ok = 0; }}", value(p, k));
                    }
                }
                *out += "}\n";
            }
            Trip::Slice(include) => {
                let mut slice = String::new();
                for (i, item) in body.iter().enumerate() {
                    if include[i] {
                        self.items(std::slice::from_ref(item), &mut slice, false, true);
                    }
                }
                // in parallel, a block at a time
                let _ = write!(
                    out,
                    "for (int64_t bf_from = 0, bf_block = 64; bf_ok && bf_m < 0; bf_from += bf_block, bf_block = bf_block < (1 << 20) ? 4 * bf_block : bf_block) {{\n\
                     if (bf_from > ((int64_t)1 << 40)) {{ bf_ok = 0; break; }}\n\
                     int64_t bf_found = INT64_MAX;\n{}\
                     #pragma omp parallel num_threads(bf_threads) if(bf_threads > 1) firstprivate({fp})\n{{\n{setup}#pragma omp for reduction(min:bf_found) schedule(guided)\n\
                     for (int64_t bf_k = bf_from; bf_k < bf_from + bf_block; bf_k++) {{\n{start}{slice}if (acc == 0 && bf_k < bf_found) bf_found = bf_k;\n}}\n{teardown}}}\n\
                     if (bf_found != INT64_MAX) bf_m = bf_found;\n}}\n",
                    self.threads("(double)bf_block * bf_per")
                );
            }
        }
        *out += "}\n";
        *out += &ex.checks(lo, hi, "bf_m");
        // (see `Extreme::tainted`)
        if plan.extremes.iter().any(|e| e.tainted) {
            *out += "if (bf_m > 0) bf_m -= 1;\n";
        }
        let _ = writeln!(out, "#ifdef BF_STATS\nfprintf(stderr, \"loop {id}: %s, %lld iterations before the last\\n\", bf_ok ? \"checks pass\" : \"checks fail\", (long long)bf_m);\nfprintf(stderr, \"loop {id}: %.3f ms to check and count, at %.1f ns an iteration so far\\n\", (bf_now() - bf_ts) / 1e6, bf_per);\nbf_ts = bf_now();\n#endif");

        // the iterations before the last, in parallel (noting which cells
        // each writes, if some only some do)
        // (what's left in cells nothing reads afterwards doesn't matter)
        // (a maximum, and what's set along with it, are kept if any of them is)
        let groups: Vec<Vec<i64>> = plan.extremes.iter().map(|e| std::iter::once(e.cell).chain(e.with.iter().copied()).collect()).collect();
        let kept = |o: &i64| !dead.contains(o) || groups.iter().any(|g| g.contains(o) && g.iter().any(|c| !dead.contains(c)));
        let maybes: Vec<i64> = cells.iter().filter(|(o, r)| **r == Role::Maybe && kept(o)).map(|c| c.0).collect();
        let mut code = String::new();
        let saved = (self.notes.take(), self.unnoted, self.at, std::mem::take(&mut self.saved_at));
        self.notes = (!maybes.is_empty()).then(|| (lo, maybes.iter().copied().collect()));
        (self.unnoted, self.at) = (false, Some(0));
        let gathering = !plan.gathers.is_empty();
        let written: Vec<&analysis::Family> = plan.shared.iter().filter(|f| f.written()).collect();
        // (of memory that's like a cell, what iterations write: memory read
        // where only the iteration knows can only be the thread's copy if
        // it's the same, and one range for each cell's)
        let mut scalar_ranges: std::collections::BTreeMap<i64, (i64, i64)> = std::collections::BTreeMap::new();
        for (j, sc) in plan.scalars.iter().enumerate() {
            if !matches!(plan.cells.get(&(SCALAR + j as i64)), Some(Role::Read | Role::Restored)) {
                let r = scalar_ranges.entry(sc.cell).or_insert((sc.off, sc.off));
                *r = (r.0.min(sc.off), r.1.max(sc.off));
            }
        }
        let ng = 1 + plan.private.len() + written.len() + scalar_ranges.len();
        self.gathers = gathering.then(|| (plan.gathers.clone(), ng));
        let slotted = !plan.slots.is_empty();
        self.slots = slotted.then(|| (plan.slots.clone(), plan.private.iter().map(|p| p.1).collect()));
        let direct = !plan.through;
        self.direct = direct.then_some(lo);
        // (the analysis's calls start from the loop's body)
        let chain = std::mem::take(&mut self.call_chain);
        self.entered = plan.entered.clone();
        let scalared = !plan.scalars.is_empty();
        self.scalars = scalared.then(|| (plan.scalar_slots.clone(), width));
        self.copied = (!plan.copied.is_empty()).then(|| plan.copied.clone());
        self.items(body, &mut code, false, true);
        self.scalars = None;
        self.copied = None;
        self.entered.clear();
        self.call_chain = chain;
        self.gathers = None;
        self.slots = None;
        self.direct = None;
        if (self.notes.is_some() || slotted || direct || scalared) && self.unnoted {
            // (a call it couldn't inline would write cells without noting it)
            *out += "bf_ok = 0;\n";
        }
        (self.notes, self.unnoted, self.at, self.saved_at) = saved;
        if maybes.len() > 64 {
            // (each has a bit of a word)
            *out += "bf_ok = 0;\n";
        }
        let nr = reductions.len().max(1);
        let nw = maybes.len().max(1);
        let mut stks = String::new();
        if slotted {
            for (j, &(_, plo, phi)) in plan.private.iter().enumerate() {
                let _ = writeln!(stks, "int64_t bf_stk{j}[{}];", (phi - plo) / 8 + 1);
            }
        }
        let mut bits = String::new();
        for (j, &o) in maybes.iter().enumerate().take(64) {
            let _ = writeln!(bits, "bf_bit[{}] = {}ull;", win(o), 1u64 << j);
        }
        let privates: Vec<i64> = cells.iter().filter(|(o, r)| **r == Role::Private && !dead.contains(o)).map(|c| c.0).collect();
        // what reads where only the iteration knows mustn't read: what
        // iterations write (kept, to put back if one does), the cells near
        // the pointer, and stacks
        let mut guard = String::new();
        let _ = writeln!(guard, "int bf_bad = 0, bf_ng = 0;\nuintptr_t bf_glo[{ng}], bf_ghi[{ng}];\n(void)bf_glo;\n(void)bf_ghi;\n(void)bf_ng;");
        if gathering {
            let _ = writeln!(guard, "bf_glo[bf_ng] = (uintptr_t)(bf_p0 + ({lo}));\nbf_ghi[bf_ng++] = (uintptr_t)(bf_p0 + ({hi} + 1));");
            for &(cell, plo, phi) in &plan.private {
                let _ = writeln!(guard, "bf_glo[bf_ng] = (uintptr_t)bf_p0[{cell}] + ({plo});\nbf_ghi[bf_ng++] = (uintptr_t)bf_p0[{cell}] + ({phi}) + 8;");
            }
            // (memory that's like a cell after the rest, so the rest are
            // where putting back expects them)
            for (i, f) in written.iter().enumerate() {
                let (first, last) = (*f.offsets.keys().next().unwrap(), *f.offsets.keys().last().unwrap());
                let _ = writeln!(
                    guard,
                    "__int128 bf_gb{i} = {}, bf_gs{i} = {};\nbf_glo[bf_ng] = (uintptr_t)(bf_gb{i} + ({first}) + (bf_gs{i} < 0 ? bf_gs{i} * (bf_m - 1) : 0));\nbf_ghi[bf_ng] = (uintptr_t)(bf_gb{i} + ({last}) + 8 + (bf_gs{i} > 0 ? bf_gs{i} * (bf_m - 1) : 0));\nvoid *bf_kept{i} = malloc(bf_ghi[bf_ng] - bf_glo[bf_ng]);\nmemcpy(bf_kept{i}, (void *)bf_glo[bf_ng], bf_ghi[bf_ng] - bf_glo[bf_ng]);\nbf_ng++;",
                    ex.entry(&f.base),
                    ex.stride(&f.base)
                );
            }
            for (c, (first, last)) in &scalar_ranges {
                let _ = writeln!(guard, "bf_glo[bf_ng] = (uintptr_t)bf_p0[{c}] + ({first});\nbf_ghi[bf_ng++] = (uintptr_t)bf_p0[{c}] + ({last}) + 8;");
            }
        }
        // a part at a time: on one thread, timed, until what's left is worth
        // starting threads for (and then all of it)
        // (a part's time only tells how long an iteration takes once it's
        // long enough to be more than starting it: until then each part on
        // one thread is longer than the last)
        let gfp = if gathering { ", bf_ng, bf_glo, bf_ghi" } else { "" };
        let mut granges = String::new();
        if gathering {
            for i in 0..ng {
                let _ = writeln!(granges, "const uintptr_t bf_gl{i} = bf_glo[{i}], bf_gs{i} = bf_ghi[{i}] - bf_glo[{i}];");
            }
        }
        let trust = self.trust();
        // (and how long the rest must be going to take, the least, for this
        // loop: more each time running it in parallel didn't pay)
        let work = self.work;
        let worth = if self.work == 0 { "1".to_string() } else { format!("bf_span >= {trust} && (double)(bf_m - bf_k0) * bf_est >= bf_need{id}") };
        let pick = self.threads("(double)(bf_m - bf_k0) * bf_est");
        // the copies of memory read as it was, where they're needed
        // (only once it runs on more than one thread: in order, on one, it
        // reads what's there, which is the same; and nothing before then has
        // written what it reads since)
        let (mut copying, mut copy_now, mut cfp, mut uncopying) = (String::new(), String::new(), String::new(), String::new());
        for &i in &copies {
            let f = &plan.shared[i];
            let offs: Vec<i64> = f.offsets.iter().filter(|(c, _)| !f.written() || f.later.contains(c)).map(|(&c, _)| c).collect();
            let (first, last) = (offs.iter().min().copied().unwrap_or(0), offs.iter().max().copied().unwrap_or(0));
            let _ = writeln!(copying, "int64_t bf_sd{i} = 0;\nvoid *bf_copy{i} = NULL;");
            let _ = writeln!(
                copy_now,
                "if (bf_cp{i} && !bf_copy{i}) {{\n__int128 bf_cb = {}, bf_cs = {};\nuintptr_t bf_clo = (uintptr_t)(bf_cb + ({first}) + (bf_cs < 0 ? bf_cs * (bf_m - 1) : 0)), bf_chi = (uintptr_t)(bf_cb + ({last}) + 8 + (bf_cs > 0 ? bf_cs * (bf_m - 1) : 0));\nbf_copy{i} = malloc(bf_chi - bf_clo);\nmemcpy(bf_copy{i}, (void *)bf_clo, bf_chi - bf_clo);\nbf_sd{i} = (int64_t)((char *)bf_copy{i} - (char *)bf_clo);\n}}",
                ex.entry(&f.base),
                ex.stride(&f.base)
            );
            let _ = write!(cfp, ", bf_sd{i}");
            let _ = writeln!(uncopying, "free(bf_copy{i});");
        }
        let _ = write!(
            out,
            "if (bf_ok && bf_m >= {}) {{\n{guard}{copying}uint64_t bf_total[{nr}] = {{0}};\ndouble bf_busy = 0;\nint64_t bf_last[{full}];\nint64_t bf_wrote[{nw}], bf_wrote_v[{nw}];\nfor (int bf_j = 0; bf_j < {nw}; bf_j++) bf_wrote[bf_j] = -1;\nint bf_most = 1;\nint64_t bf_k0 = 0, bf_k1 = 0, bf_len = bf_per > 0 && {trust}.0 / bf_per > 16 ? (int64_t)({trust}.0 / bf_per) : 16;\ndouble bf_est = bf_per, bf_span = 0;\nwhile (bf_k0 < bf_m && !bf_bad) {{\nbf_threads = 1;\nif ({worth}) {{\n{pick}}}\nif (bf_threads > 1) {{\nbf_k1 = bf_m;\n}} else {{\nbf_threads = 1;\nbf_k1 = bf_k0 + (bf_span >= {trust} ? (int64_t)({}.0 / bf_est) + 1 : bf_len);\nbf_len *= 4;\nif (bf_k1 > bf_m) bf_k1 = bf_m;\n}}\nif (bf_threads > bf_most) bf_most = bf_threads;\nif (bf_threads > 1) {{\n{copy_now}}}\ndouble bf_c0 = bf_now();\n",
            self.min.max(1),
            2 * self.work.max(5000)
        );
        // (what each thread runs: on one, without starting any, not even
        // the one, which costs about a microsecond)
        let mut region = format!(
            "{{\n{setup}{stks}{granges}uint64_t bf_part[{nr}] = {{0}};\nuint64_t bf_bit[{full}] = {{0}};\n{bits}int64_t bf_my[{nw}], bf_my_v[{nw}];\nfor (int bf_j = 0; bf_j < {nw}; bf_j++) bf_my[bf_j] = -1;\n(void)bf_bit;\nint bf_mybad = 0;\n(void)bf_mybad;\nint64_t bf_klast = -1;\n(void)bf_klast;\ndouble bf_t0 = bf_now();\n#pragma omp for schedule(guided) nowait\nfor (int64_t bf_k = bf_k0; bf_k < bf_k1; bf_k++) {{\nuint64_t bf_wbits = 0;\n(void)bf_wbits;\n{start}{code}"
        );
        for (j, &o) in reductions.iter().enumerate() {
            let _ = writeln!(region, "bf_part[{j}] += (uint64_t)bf_win[{}] - (uint64_t)bf_e{};", win(o), c_name(o));
        }
        // what the iteration before the last leaves in the cells each
        // iteration writes before reading: the last one may not write them
        // (it's the one that doesn't go on)
        // (a thread runs its iterations in order, so the one that runs it
        // ends on it: it copies them once it's done)
        if !privates.is_empty() {
            region += "bf_klast = bf_k;\n";
        }
        // (what the threads leave in those: the last write's, or, for a
        // maximum and what's set with it, the most's)
        let mut combine = String::new();
        let at = |o: i64| maybes.iter().position(|&m| m == o);
        for (j, &o) in maybes.iter().enumerate() {
            if !groups.iter().any(|g| g.contains(&o)) {
                let _ = writeln!(combine, "if (bf_my[{j}] > bf_wrote[{j}]) {{ bf_wrote[{j}] = bf_my[{j}]; bf_wrote_v[{j}] = bf_my_v[{j}]; }}");
            }
        }
        for (e, g) in plan.extremes.iter().zip(&groups) {
            let Some(j) = at(e.cell) else { continue };
            let ty = if e.unsigned { "uint64_t" } else { "int64_t" };
            let (more, tie) = (if e.max { ">" } else { "<" }, if e.strict { "<" } else { ">" });
            let _ = write!(combine, "if (bf_my[{j}] >= 0 && (bf_wrote[{j}] < 0 || ({ty})bf_my_v[{j}] {more} ({ty})bf_wrote_v[{j}] || (bf_my_v[{j}] == bf_wrote_v[{j}] && bf_my[{j}] {tie} bf_wrote[{j}]))) {{");
            for &o in g {
                if let Some(i) = at(o) {
                    let _ = write!(combine, " bf_wrote[{i}] = bf_my[{i}]; bf_wrote_v[{i}] = bf_my_v[{i}];");
                }
            }
            combine += " }\n";
        }
        // and, for those only some write, the last of this thread's
        // iterations that did, and what it left
        for (j, &o) in maybes.iter().enumerate() {
            let _ = writeln!(region, "if ((bf_wbits >> {j} & 1) && bf_k > bf_my[{j}]) {{ bf_my[{j}] = bf_k; bf_my_v[{j}] = bf_win[{}]; }}", win(o));
        }
        let _ = write!(
            region,
            "}}\ndouble bf_mine = bf_now() - bf_t0;\nif (bf_klast == bf_m - 1) memcpy(bf_last, bf_win, sizeof bf_last);\n#pragma omp critical\n{{\nbf_busy += bf_mine;\nbf_bad |= bf_mybad;\nfor (int bf_j = 0; bf_j < {nr}; bf_j++) bf_total[bf_j] += bf_part[bf_j];\n{combine}}}\n{teardown}}}\n"
        );
        let alone = region.replace("#pragma omp for schedule(guided) nowait\n", "").replace("#pragma omp critical\n", "").replace("double bf_t0 = bf_now();\n", "double bf_t0 = 0;\n").replace("double bf_mine = bf_now() - bf_t0;\n", "double bf_mine = 0;\n");
        let _ = write!(out, "if (bf_threads > 1) {{\n#pragma omp parallel num_threads(bf_threads) firstprivate({fp}{gfp}{cfp})\n{region}}} else {alone}");
        let _ = write!(
            out,
            "if (bf_threads == 1) {{\nbf_span = bf_now() - bf_c0;\nbf_est = bf_span / (double)(bf_k1 - bf_k0);\n}} else {{\ndouble bf_took = bf_now() - bf_c0, bf_par = bf_busy / (double)(bf_k1 - bf_k0);\nif (bf_par < bf_timed{id}) bf_timed{id} = bf_par;\nif (bf_took > 0.7 * (double)(bf_k1 - bf_k0) * bf_est) bf_need{id} *= 2;\nelse if (bf_need{id} > {work}.0) bf_need{id} *= 0.8;\n}}\nbf_k0 = bf_k1;\n}}\nif (bf_span >= {trust} && bf_span < 1e9) bf_timed{id} = bf_timed{id} == 0 || bf_est < bf_timed{id} ? bf_est : (bf_timed{id} + bf_est) / 2;\nbf_small{id} = bf_most == 1 && {};\nif (bf_most == 1 && bf_need{id} > {work}.0 && (double)bf_m * bf_est >= {work}.0) bf_need{id} *= 0.99;\n",
            // (on one thread, the code for running in parallel is faster than
            // the loop's own, which checks where the pointer goes as it goes,
            // so it's worth the checks however short the loop; but counting
            // it by running what decides it costs about as much as running
            // it: not worth it, if it then ran on one thread)
            if matches!(plan.trip, Trip::Slice(_)) { "1" } else { "0" }
        );
        // and the cells as the last iteration finds them
        let _ = writeln!(out, "#ifdef BF_STATS\nif (bf_bad) fprintf(stderr, \"loop {id}: read memory an iteration writes: put back, in order\\n\");\nelse fprintf(stderr, \"loop {id}: %.3f ms in parallel on %d threads, %lld iterations\\n\", (bf_now() - bf_ts) / 1e6, bf_most, (long long)bf_m);\n#endif");
        // (if an iteration read what one wrote, it's as if none of them ran)
        if gathering {
            *out += "if (bf_bad) {\n";
            for i in 0..written.len() {
                let j = 1 + plan.private.len() + i;
                let _ = writeln!(out, "memcpy((void *)bf_glo[{j}], bf_kept{i}, bf_ghi[{j}] - bf_glo[{j}]);");
            }
            *out += "} else {\n";
        }
        for &o in &privates {
            let _ = writeln!(out, "{} = bf_last[{}];", home(o), win(o));
        }
        for (j, &o) in maybes.iter().enumerate() {
            let _ = writeln!(out, "if (bf_wrote[{j}] >= 0) {} = bf_wrote_v[{j}];", home(o));
        }
        for &(o, _) in &inductions {
            let n = c_name(o);
            let _ = writeln!(out, "{} = (int64_t)((uint64_t)bf_e{n} + (uint64_t)bf_s{n} * (uint64_t)bf_m);", home(o));
        }
        for (j, &o) in reductions.iter().enumerate() {
            let _ = writeln!(out, "{} = (int64_t)((uint64_t)bf_e{} + bf_total[{j}]);", home(o), c_name(o));
        }
        if gathering {
            *out += "}\n";
            for i in 0..written.len() {
                let _ = writeln!(out, "free(bf_kept{i});");
            }
        }
        // (if the checks failed, or it had too few iterations, it doesn't
        // look again, but for one time in 16)
        *out += &uncopying;
        let _ = writeln!(out, "}}\nelse bf_small{id} = 1;");
    }

    /// The thread's copy of the cell `n` past where the pointer is, if it's
    /// known which that is and those are accessed directly.
    fn window_cell(&self, n: i64) -> Option<String> {
        Some(format!("bf_win[{}]", self.at? + n - self.direct?))
    }

    /// `code` (native code), with the cells it accesses (`ptr[n]`) the
    /// thread's copies, where they're accessed directly.
    fn localized(&self, code: &str) -> String {
        if self.window_cell(0).is_none() {
            return code.to_string();
        }
        let mut out = String::new();
        let mut rest = code;
        while let Some(i) = rest.find("ptr[") {
            out += &rest[..i];
            let after = &rest[i + 4..];
            match after.split_once(']').and_then(|(n, tail)| Some((n.parse::<i64>().ok()?, tail))) {
                Some((n, tail)) => {
                    out += &self.window_cell(n).unwrap();
                    rest = tail;
                }
                None => {
                    out += "ptr[";
                    rest = after;
                }
            }
        }
        out + rest
    }

    /// The variable for the cell of a stack an op accesses, if it's one that
    /// always accesses the same one.
    fn slot(&self, item: &Item) -> Option<String> {
        if let Some((slots, from)) = &self.scalars {
            if let Some(j) = slots.get(&(self.call_chain.clone(), item as *const Item)) {
                return Some(format!("bf_win[{}]", from + *j as i64));
            }
        }
        let (slots, lows) = self.slots.as_ref()?;
        let &(j, off) = slots.get(&(self.call_chain.clone(), item as *const Item))?;
        Some(format!("bf_stk{j}[{}]", (off - lows[j]) / 8))
    }

    /// Which family `item` reads from a copy of, if it might.
    fn copy(&self, item: &Item) -> Option<usize> {
        self.copied.as_ref()?.get(&(self.call_chain.clone(), item as *const Item)).copied()
    }

    /// What notes a write by `item` to memory that's like a cell, if it's
    /// one that only some iterations write.
    fn slot_note(&self, item: &Item) -> String {
        let (Some((slots, _)), Some((_, cells))) = (&self.scalars, &self.notes) else { return String::new() };
        match slots.get(&(self.call_chain.clone(), item as *const Item)).and_then(|&j| cells.iter().position(|&c| c == SCALAR + j as i64)) {
            Some(bit) => format!(" bf_wbits |= {}ull;", 1u64.checked_shl(bit as u32).unwrap_or(0)),
            None => String::new(),
        }
    }

    /// The check before an op that reads where only the iteration knows, if
    /// it's one.
    fn gather(&self, item: &Item) -> String {
        match &self.gathers {
            // (each range the thread's own variables: `bf_gl{i}`, from, and
            // `bf_gs{i}`, how long)
            Some((g, n)) if g.contains(&(item as *const Item)) => {
                let hits: Vec<String> = (0..*n).map(|i| format!("((uintptr_t)ptr - bf_gl{i} < bf_gs{i})")).collect();
                format!("bf_mybad |= {}; ", hits.join(" | "))
            }
            _ => String::new(),
        }
    }

    /// What notes a write to `ptr[n]`, if writes are being noted: nothing
    /// if it's known not to be a cell they're noted for, and a check of
    /// where it is if that isn't known.
    fn note(&self, n: i64) -> String {
        match (&self.notes, self.at) {
            (None, _) => String::new(),
            (Some((_, cells)), Some(a)) if cells.contains(&(a + n)) => format!(" bf_wbits |= {}ull;", 1u64.checked_shl(cells.iter().position(|&c| c == a + n).unwrap() as u32).unwrap_or(0)),
            (Some(_), Some(_)) => String::new(),
            // (nothing through a pointer reaches the copies, when they're
            // accessed directly)
            (Some(_), None) if self.direct.is_some() => String::new(),
            (Some(_), None) => format!(" BF_NOTE(ptr + ({n}));"),
        }
    }

    /// `code` (the native code for a function), noting its writes to cells
    /// (`ptr[n] = ...;`, each on its line) if writes are being noted.
    fn noted(&self, code: &str) -> String {
        if self.notes.is_none() {
            return code.to_string();
        }
        let mut out = String::new();
        for line in code.lines() {
            out += line;
            if let Some(n) = line.strip_prefix("ptr[").and_then(|l| l.split_once("] = ")).and_then(|(n, _)| n.parse::<i64>().ok()) {
                out += &self.note(n);
            }
            out.push('\n');
        }
        out
    }

    /// Code that sets `bf_threads` to how many threads are worth starting for
    /// work that would take `time` (a C expression, in nanoseconds) on one:
    /// one for each eighth of `min_time` of it, as many as there are.
    /// How long a part of a loop, run on one thread, must have taken for how
    /// long its iterations took to be worth going by (in nanoseconds).
    fn trust(&self) -> u64 {
        (self.work / 5).max(2000)
    }

    fn threads(&self, time: &str) -> String {
        let mut out = String::from("#ifdef _OPENMP\nbf_threads = bf_most_threads;\n");
        if self.work > 0 {
            // (`time / T + THREAD_NS T` is least for T = sqrt(time / THREAD_NS))
            let _ = writeln!(
                out,
                "{{\ndouble bf_want = __builtin_sqrt({time} / {THREAD_NS}.0);\nif (bf_want < (double)bf_threads) bf_threads = bf_want < 1 ? 1 : (int)bf_want;\nif (bf_threads > bf_cluster && !({time} / bf_cluster - {time} / bf_threads > {CLUSTER_NS}.0)) bf_threads = bf_cluster;\nif (bf_threads > 1 && !({time} / bf_threads + {THREAD_NS}.0 * bf_threads + {FORK_NS}.0 < {time})) bf_threads = 1;\nif (bf_threads > 1 && !bf_started) {{\nbf_saved += {time} - ({time} / bf_threads + {THREAD_NS}.0 * bf_threads + {FORK_NS}.0);\nif (bf_saved < {START_NS}.0) bf_threads = 1;\nelse bf_started = 1;\n}}\n}}"
            );
        }
        out + "#endif\n"
    }
}

/// Which of `cells` (offsets from where the pointer is when `after` starts)
/// are dead there: on every path through `after`, the rest of the program,
/// written before they're read, or never read. Anything it can't follow (a
/// `*`, a loop that moves the pointer, a call it can't see into) counts as
/// reading them.
fn dead_after(after: &[Item], cells: &[i64], funcs: &HashMap<String, &[Item]>) -> std::collections::BTreeSet<i64> {
    use std::collections::BTreeSet;
    struct Scan<'a> {
        funcs: &'a HashMap<String, &'a [Item]>,
        inlining: Vec<String>,
        /// Not yet read or written for certain, on this path.
        pending: BTreeSet<i64>,
        /// Read while pending (so not dead).
        read: BTreeSet<i64>,
        dead: BTreeSet<i64>,
    }
    impl Scan<'_> {
        /// Follows `items` from `at`; `sure` is whether they run for certain
        /// (not in a loop that might not). Gives where the pointer ends up, or
        /// `None` once it can't follow (when everything pending is read).
        fn items(&mut self, items: &[Item], mut at: i64, sure: bool) -> Option<i64> {
            for (i, item) in items.iter().enumerate() {
                if self.pending.is_empty() {
                    return Some(at);
                }
                match item {
                    Item::Op(Op::Move(n)) => at = at.checked_add(*n)?,
                    Item::Op(Op::Load | Op::Add) => {
                        if self.pending.remove(&at) {
                            self.read.insert(at);
                        }
                    }
                    Item::Op(Op::Store) => {
                        if self.pending.remove(&at) && sure {
                            self.dead.insert(at);
                        }
                    }
                    Item::Op(Op::Call) => {
                        let f = callee(items, i).filter(|f| self.funcs.contains_key(f) && !self.inlining.contains(f))?;
                        self.inlining.push(f.clone());
                        at = self.items(self.funcs[&f], at, sure)?;
                        self.inlining.pop();
                    }
                    Item::Op(Op::Deref | Op::Refer | Op::While | Op::EndWhile | Op::Func | Op::EndFunc) => return None,
                    Item::Op(_) | Item::Func(..) => {}
                    Item::Loop(body) => {
                        // (it may not run: what it reads first is read, but
                        // what it writes is still pending after it)
                        let before = self.pending.clone();
                        if self.items(body, at, false) != Some(at) {
                            return None;
                        }
                        self.pending = before.into_iter().filter(|c| !self.read.contains(c)).collect();
                    }
                }
            }
            Some(at)
        }
    }
    let mut scan = Scan { funcs, inlining: vec![], pending: cells.iter().copied().collect(), read: BTreeSet::new(), dead: BTreeSet::new() };
    // (the program ends after it: what's still pending is never read)
    if scan.items(after, 0, true).is_some() {
        scan.dead.extend(scan.pending.iter().copied());
    }
    scan.dead
}

/// The ops `items` came from.
fn flatten(items: &[Item], out: &mut Vec<Op>) {
    for item in items {
        match item {
            Item::Op(op) => out.push(*op),
            Item::Loop(body) => {
                out.push(Op::While);
                flatten(body, out);
                out.push(Op::EndWhile);
            }
            Item::Func(_, body) => {
                out.push(Op::Func);
                flatten(body, out);
                out.push(Op::EndFunc);
            }
        }
    }
}

/// The function a call at `items[i]` makes, if it's sure to be the one
/// whose label was last put in acc.
fn callee(items: &[Item], i: usize) -> Option<String> {
    for item in items[..i].iter().rev() {
        match item {
            Item::Op(Op::Label(l)) => return Some(label_name(l)),
            Item::Op(Op::Move(_) | Op::Store | Op::Write | Op::Deref | Op::Refer) => {}
            _ => return None,
        }
    }
    None
}

/// The `*`s in `items` (by index) that can save the pointer in a local,
/// with their `&`s: they pair up within the block, and everything between
/// uses the stack evenly (calls only to `even` functions, or ones outside
/// the program).
fn pairs(items: &[Item], even: &crate::asm::fx::HashSet<String>) -> HashMap<usize, usize> {
    let mut out = HashMap::default();
    let mut open: Vec<usize> = vec![];
    for (i, item) in items.iter().enumerate() {
        match item {
            Item::Op(Op::Deref) => open.push(i),
            Item::Op(Op::Refer) => {
                if let Some(j) = open.pop() {
                    if (j + 1..i).all(|k| evenly(items, k, even)) {
                        out.insert(j, i);
                    }
                }
            }
            _ => {}
        }
    }
    out
}

/// Whether `items[i]` uses the stack of saved pointers evenly.
fn evenly(items: &[Item], i: usize, even: &crate::asm::fx::HashSet<String>) -> bool {
    match &items[i] {
        Item::Op(Op::Call) => callee(items, i).is_some_and(|f| even.contains(&f) || is_external(&f, even)),
        Item::Op(_) | Item::Func(..) => true,
        Item::Loop(body) => uses_evenly(body, even),
    }
}

/// Whether a block uses the stack evenly: its `*`s and `&`s pair up, and
/// everything else in it does.
fn uses_evenly(items: &[Item], even: &crate::asm::fx::HashSet<String>) -> bool {
    let mut depth = 0i64;
    for (i, item) in items.iter().enumerate() {
        match item {
            Item::Op(Op::Deref) => depth += 1,
            Item::Op(Op::Refer) => {
                depth -= 1;
                if depth < 0 {
                    return false;
                }
            }
            _ if !evenly(items, i, even) => return false,
            _ => {}
        }
    }
    depth == 0
}

/// Whether a function isn't the program's (the set of even ones names the
/// program's functions it doesn't include with a `\0` in front).
fn is_external(name: &str, even: &crate::asm::fx::HashSet<String>) -> bool {
    !even.contains(&format!("\0{name}"))
}

/// The functions that never return: those that call `bf_exit` (this
/// backend's own, which stops the program: see `PRELUDE_MAIN`), or one of
/// these, outside any loop. (A function only returns at its end, and what's
/// outside its loops is all done on the way there.)
fn stopping(funcs: &HashMap<String, &[Item]>) -> crate::asm::fx::HashSet<String> {
    let mut stops = crate::asm::fx::HashSet::default();
    if !funcs.contains_key(EXIT) {
        stops.insert(EXIT.to_string());
    }
    loop {
        let found: Vec<String> = funcs.iter().filter(|(name, body)| !stops.contains(*name) && (0..body.len()).any(|i| matches!(body[i], Item::Op(Op::Call)) && callee(body, i).is_some_and(|f| stops.contains(&f)))).map(|(name, _)| name.clone()).collect();
        if found.is_empty() {
            return stops;
        }
        stops.extend(found);
    }
}

/// The program's functions that use the stack of saved pointers evenly:
/// assumed of all, then dropped for each that doesn't under that
/// assumption, until what's left holds up. (The set also has each of the
/// program's functions that isn't even, with a `\0` in front, so that
/// `is_external` can tell those from functions outside the program, which
/// can't touch it.)
fn even_functions(funcs: &HashMap<String, &[Item]>) -> crate::asm::fx::HashSet<String> {
    let mut even: crate::asm::fx::HashSet<String> = funcs.keys().cloned().collect();
    loop {
        let mut set = even.clone();
        for name in funcs.keys() {
            if !even.contains(name) {
                set.insert(format!("\0{name}"));
            }
        }
        let next: crate::asm::fx::HashSet<String> = funcs.iter().filter(|(_, body)| uses_evenly(body, &set)).map(|(n, _)| n.clone()).collect();
        if next == even {
            return set;
        }
        even = next;
    }
}

/// C that has a linear effect on `ptr`'s cells and `acc`: works out what
/// each cell it writes ends up holding from what they all held, then writes
/// them.
fn linear_c(e: &analysis::LinearEffect) -> String {
    let expr = |l: &Lin| {
        let mut s = format!("(int64_t)((uint64_t){}ull", l.c as u64);
        for (&sym, &k) in &l.terms {
            let v = if sym == e.p0 {
                "(int64_t)(intptr_t)ptr".to_string()
            } else if sym == e.acc0 {
                "acc".to_string()
            } else {
                format!("ptr[{}]", e.cell_of(sym).expect("a cell's"))
            };
            let _ = write!(s, " + (uint64_t){}ull * (uint64_t){v}", k as u64);
        }
        s + ")"
    };
    let mut out = String::from("{\n");
    for (i, (_, v)) in e.writes.iter().enumerate() {
        let _ = writeln!(out, "int64_t bf_l{i} = {};", expr(v));
    }
    let _ = writeln!(out, "int64_t bf_la = {};", expr(&e.acc));
    for (i, (o, _)) in e.writes.iter().enumerate() {
        let _ = writeln!(out, "ptr[{o}] = bf_l{i};");
    }
    out + "acc = bf_la;\n}\n"
}

/// A C name for a cell's offset (which can be negative).
fn c_name(o: i64) -> String {
    if o < 0 {
        format!("m{}", -o)
    } else {
        o.to_string()
    }
}

/// C expressions for what a plan's symbols are when the loop starts.
struct Exprs<'a> {
    plan: &'a Plan,
}

impl Exprs<'_> {
    /// `l`, with every symbol as it is for the first iteration.
    fn entry(&self, l: &Lin) -> String {
        let mut s = format!("((uint64_t){}ull", l.c as u64);
        for (&sym, &k) in &l.terms {
            let v = match &self.plan.syms.kinds[sym as usize] {
                SymKind::Init(_) if self.plan.cell_of(sym).is_some() => format!("bf_p0[{}]", self.plan.cell_of(sym).unwrap()),
                SymKind::Init(a) => format!("(*(int64_t *)(intptr_t){})", self.entry(a)),
                SymKind::P0 => "(int64_t)(intptr_t)bf_p0".to_string(),
                // (the analysis never leaves these in what's worked out)
                SymKind::Acc0 | SymKind::Fresh(_) => "0".to_string(),
            };
            let _ = write!(s, " + (uint64_t){}ull * (uint64_t){v}", k as u64);
        }
        s.push(')');
        format!("((int64_t){s})")
    }

    /// How much `l` grows every time round, if that's known as the code is
    /// emitted (the induction variables in it have constant steps).
    fn const_stride(&self, l: &Lin) -> Option<i64> {
        let mut st = 0i64;
        for (&sym, &k) in &l.terms {
            if let Some(step) = self.plan.step(sym) {
                st = st.wrapping_add(k.wrapping_mul(step.terms.is_empty().then_some(step.c)?));
            }
        }
        Some(st)
    }

    /// How much `l` grows every time round.
    fn stride(&self, l: &Lin) -> String {
        let mut s = String::from("((uint64_t)0");
        for (&sym, &k) in &l.terms {
            if self.plan.step(sym).is_some() {
                let _ = write!(s, " + (uint64_t){}ull * (uint64_t)bf_s{}", k as u64, c_name(self.plan.var_of(sym).unwrap()));
            }
        }
        s.push(')');
        format!("((int64_t){s})")
    }

    /// Code that clears `bf_ok` unless, over the first `m` iterations, the
    /// memory each part of the iteration accesses is apart from every other
    /// part's (where one of them is written), and no iteration writes what
    /// another accesses.
    fn checks(&self, lo: i64, hi: i64, m: &str) -> String {
        // each part: its lowest and highest byte, and whether it's written
        // (and which family it is, if it's one)
        let mut parts: Vec<(String, String, bool, Option<usize>)> = vec![];
        parts.push((format!("(__int128)(intptr_t)(bf_p0 + ({lo}))"), format!("(__int128)(intptr_t)(bf_p0 + ({hi})) + 7"), true, None));
        for &(cell, plo, phi) in &self.plan.private {
            parts.push((format!("(__int128)bf_p0[{cell}] + ({plo})"), format!("(__int128)bf_p0[{cell}] + ({phi}) + 7"), true, None));
        }
        for sc in &self.plan.scalars {
            parts.push((format!("(__int128)bf_p0[{}] + ({})", sc.cell, sc.off), format!("(__int128)bf_p0[{}] + ({}) + 7", sc.cell, sc.off), true, None));
        }
        let mut out = format!("if (bf_ok) {{\nint64_t bf_mm = {m};\n(void)bf_mm;\n");
        // how many times the loops in the body that are summed up run (but
        // for the last time round, which only leaves), each the same every
        // time, and that what they compare doesn't wrap round
        for (n, t) in self.plan.inners.iter().enumerate() {
            let _ = writeln!(out, "__int128 bf_ix{n} = {}, bf_is{n} = {};\nint64_t bf_im{n} = 0;", self.entry(&t.x0), self.entry(&t.xs));
            if t.exact {
                let _ = writeln!(out, "if (bf_is{n} == 0 || (-bf_ix{n}) % bf_is{n} != 0 || (-bf_ix{n}) / bf_is{n} < 0 || (-bf_ix{n}) / bf_is{n} > ((__int128)1 << 40)) bf_ok = 0;\nelse bf_im{n} = (int64_t)((-bf_ix{n}) / bf_is{n});");
            } else {
                let _ = writeln!(out, "if (bf_ix{n} > 0) {{\nif (bf_is{n} >= 0 || (bf_ix{n} - bf_is{n} - 1) / -bf_is{n} > ((__int128)1 << 40)) bf_ok = 0;\nelse bf_im{n} = (int64_t)((bf_ix{n} - bf_is{n} - 1) / -bf_is{n});\n}}");
            }
            for (p0, ps, unsigned) in &t.parts {
                let lo = if *unsigned { "0" } else { "(__int128)INT64_MIN" };
                for k in ["0", &format!("bf_im{n}")] {
                    let _ = writeln!(out, "{{ __int128 bf_v = (__int128){} + (__int128){} * (__int128){k}; if (bf_v < {lo} || bf_v > (__int128)INT64_MAX) bf_ok = 0; }}", self.entry(p0), self.entry(ps));
                }
            }
        }
        for (i, f) in self.plan.shared.iter().enumerate() {
            let (first, last) = (*f.offsets.keys().next().unwrap(), *f.offsets.keys().last().unwrap());
            // (and over the range a loop in the body accesses)
            let (ilo, ihi) = match &f.inner {
                Some((st, n)) => {
                    let _ = writeln!(out, "__int128 bf_in{i} = (__int128){} * (__int128)bf_im{n};", self.entry(st));
                    (format!(" + (bf_in{i} < 0 ? bf_in{i} : 0)"), format!(" + (bf_in{i} > 0 ? bf_in{i} : 0)"))
                }
                None => (String::new(), String::new()),
            };
            let _ = writeln!(
                out,
                "__int128 bf_b{i} = {}, bf_st{i} = {};\n__int128 bf_lo{i} = bf_b{i} + ({first}) + (bf_st{i} < 0 ? bf_st{i} * (bf_mm - 1) : 0){ilo};\n__int128 bf_hi{i} = bf_b{i} + ({last}) + 7 + (bf_st{i} > 0 ? bf_st{i} * (bf_mm - 1) : 0){ihi};",
                self.entry(&f.base),
                self.stride(&f.base)
            );
            parts.push((format!("bf_lo{i}"), format!("bf_hi{i}"), f.written(), Some(i)));
            // (what an iteration writes over a range is apart from what any
            // other accesses: the iterations' ranges are further apart than
            // they're long)
            if f.written() && f.inner.is_some() {
                let _ = writeln!(out, "if (bf_mm >= 2 && (bf_st{i} < 0 ? -bf_st{i} : bf_st{i}) < ({last}) - ({first}) + 8 + (bf_in{i} < 0 ? -bf_in{i} : bf_in{i})) bf_ok = 0;");
                continue;
            }
            // no iteration writes what another accesses
            if f.written() {
                let _ = writeln!(out, "if (bf_st{i} == 0 && bf_mm >= 2) bf_ok = 0;");
                match self.const_stride(&f.base) {
                    // (with the stride known, how many iterations apart the
                    // nearest two that would are)
                    Some(st) if st != 0 => {
                        // (but for what's only read, that only later iterations
                        // write, which is read from a copy)
                        let nearest = f
                            .offsets
                            .iter()
                            .filter(|(_, w)| **w)
                            .flat_map(|(&c1, _)| f.offsets.iter().map(move |(&c2, &w2)| (c1, c2, w2)))
                            .filter(|&(c1, c2, w2)| c1 != c2 && (c1 - c2) % st == 0 && !(!w2 && (c2 - c1) / st >= 1 && f.later.contains(&c2)))
                            .map(|(c1, c2, _)| ((c1 - c2) / st).abs())
                            .min();
                        if let Some(n) = nearest {
                            let _ = writeln!(out, "if (bf_mm > {n}) bf_ok = 0;");
                        }
                    }
                    _ => {
                        let offsets: Vec<String> = f.offsets.keys().map(|c| c.to_string()).collect();
                        let written: Vec<String> = f.offsets.values().map(|w| (*w as u8).to_string()).collect();
                        let _ = writeln!(
                            out,
                            "{{\nstatic const int64_t bf_off[] = {{{}}};\nstatic const char bf_wr[] = {{{}}};\nfor (int bf_a = 0; bf_a < {n}; bf_a++) if (bf_wr[bf_a]) for (int bf_b = 0; bf_b < {n}; bf_b++) {{\nint64_t bf_d = bf_off[bf_a] - bf_off[bf_b];\nif (bf_d != 0 && bf_st{i} != 0 && bf_d % bf_st{i} == 0 && bf_d / bf_st{i} < bf_mm && bf_d / bf_st{i} > -bf_mm) bf_ok = 0;\n}}\n}}",
                            offsets.join(", "),
                            written.join(", "),
                            n = offsets.len()
                        );
                    }
                }
            }
        }
        for i in 0..parts.len() {
            for j in i + 1..parts.len() {
                if !(parts[i].2 || parts[j].2) {
                    continue;
                }
                // (memory only read that overlaps memory that's written, if
                // only later iterations write what it reads, is read from a
                // copy)
                let copy = match (parts[i].3, parts[j].3) {
                    (Some(a), Some(b)) if !parts[i].2 && self.plan.shared[a].copyable => Some((a, b)),
                    (Some(a), Some(b)) if !parts[j].2 && self.plan.shared[b].copyable => Some((b, a)),
                    _ => None,
                };
                match copy {
                    Some((r, w)) => {
                        let list = |f: &analysis::Family, written: bool| f.offsets.iter().filter(|o| !written || *o.1).map(|o| o.0.to_string()).collect::<Vec<_>>();
                        let (ro, wo) = (list(&self.plan.shared[r], false), list(&self.plan.shared[w], true));
                        let _ = writeln!(
                            out,
                            "if (!bf_apart({}, {}, {}, {})) {{\nstatic const int64_t bf_ro[] = {{{}}}, bf_wo[] = {{{}}};\nif (bf_later(bf_b{r}, bf_st{r}, bf_ro, {}, bf_b{w}, bf_st{w}, bf_wo, {}, bf_mm)) bf_cp{r} = 1;\nelse bf_ok = 0;\n}}",
                            parts[i].0,
                            parts[i].1,
                            parts[j].0,
                            parts[j].1,
                            ro.join(", "),
                            wo.join(", "),
                            ro.len(),
                            wo.len()
                        );
                    }
                    None => {
                        let _ = writeln!(out, "if (!bf_apart({}, {}, {}, {})) bf_ok = 0;", parts[i].0, parts[i].1, parts[j].0, parts[j].1);
                    }
                }
            }
        }
        out += "}\n";
        out
    }
}
