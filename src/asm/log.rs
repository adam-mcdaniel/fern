//! What the compilers are doing, and how long it takes, on stderr: in
//! levels, from nothing (0, the default) up.
//!
//! - 1, info: each phase, with how long it took, as a tree.
//! - 2, debug: what the phases worked on and made (functions, ops), and
//!   where the optimizers spent their time.
//! - 3, trace: each function, as it goes through.
//!
//! The level comes from `set_level`, or else the `BF_LOG` environment
//! variable (a number, or `info`, `debug` or `trace`).
//!
//! ```ignore
//! let _p = log::phase(log::INFO, "optimize");   // timed until it's dropped
//! bf::log!(log::DEBUG, "{} functions", n);
//! ```

use std::cell::Cell;
use std::sync::atomic::{AtomicU8, Ordering};
use std::time::{Duration, Instant};

pub const INFO: u8 = 1;
pub const DEBUG: u8 = 2;
pub const TRACE: u8 = 3;

/// 255: not decided yet (see `level`).
static LEVEL: AtomicU8 = AtomicU8::new(255);

thread_local! {
    /// How many phases are open, for indenting.
    static DEPTH: Cell<usize> = const { Cell::new(0) };
}

pub fn set_level(level: u8) {
    LEVEL.store(level, Ordering::Relaxed);
}

/// The level: what `set_level` said, or `BF_LOG`, or 0.
pub fn level() -> u8 {
    let l = LEVEL.load(Ordering::Relaxed);
    if l != 255 {
        return l;
    }
    let l = match std::env::var("BF_LOG").as_deref() {
        Ok("info") => INFO,
        Ok("debug") => DEBUG,
        Ok("trace") => TRACE,
        Ok(n) => n.parse().unwrap_or(0),
        Err(_) => 0,
    };
    set_level(l);
    l
}

pub fn enabled(level: u8) -> bool {
    self::level() >= level
}

/// A line, indented under the phases open, if the level's at least `level`.
pub fn line(level: u8, msg: std::fmt::Arguments) {
    if enabled(level) {
        let indent = DEPTH.with(|d| d.get());
        eprintln!("{}{msg}", "  ".repeat(indent));
    }
}

/// A line of the log (see the module's comment).
#[macro_export]
macro_rules! log {
    ($level:expr, $($arg:tt)*) => {
        if $crate::asm::log::enabled($level) {
            $crate::asm::log::line($level, format_args!($($arg)*))
        }
    };
}

/// A phase: what's logged inside it is indented under it, and when it's
/// dropped, how long it took is logged.
pub struct Phase {
    level: u8,
    name: String,
    start: Instant,
    on: bool,
    /// What it made, to say at the end (see `done`).
    result: Option<String>,
}

pub fn phase(level: u8, name: impl Into<String>) -> Phase {
    let on = enabled(level);
    let name = name.into();
    if on {
        let indent = DEPTH.with(|d| {
            let n = d.get();
            d.set(n + 1);
            n
        });
        if enabled(DEBUG) {
            eprintln!("{}{name} ...", "  ".repeat(indent));
        }
    }
    Phase { level, name, start: Instant::now(), on, result: None }
}

impl Phase {
    /// Says, when the phase ends, what it made ("1234 ops").
    pub fn done(&mut self, what: impl Into<String>) {
        self.result = Some(what.into());
    }

    pub fn elapsed(&self) -> Duration {
        self.start.elapsed()
    }
}

impl Drop for Phase {
    fn drop(&mut self) {
        if self.on {
            let indent = DEPTH.with(|d| {
                let n = d.get() - 1;
                d.set(n);
                n
            });
            let what = self.result.as_ref().map(|r| format!(", {r}")).unwrap_or_default();
            let _ = self.level;
            eprintln!("{}{}: {}{what}", "  ".repeat(indent), self.name, show(self.start.elapsed()));
        }
    }
}

/// A duration, to a sensible precision.
pub fn show(d: Duration) -> String {
    let s = d.as_secs_f64();
    if s >= 1.0 {
        format!("{s:.2}s")
    } else if s >= 0.001 {
        format!("{:.1}ms", s * 1000.0)
    } else {
        format!("{:.0}µs", s * 1e6)
    }
}

/// Time per name, summed over many short stretches (an optimizer's
/// passes, say), for one summary line each at the end.
#[derive(Default)]
pub struct Tally {
    times: Vec<(&'static str, Duration, usize)>,
}

impl Tally {
    /// Runs `f`, adding how long it took to `name`'s total (when logging
    /// at `DEBUG` or more; else just runs it).
    pub fn time<T>(&mut self, name: &'static str, f: impl FnOnce() -> T) -> T {
        if !enabled(DEBUG) {
            return f();
        }
        let start = Instant::now();
        let r = f();
        let d = start.elapsed();
        match self.times.iter_mut().find(|(n, _, _)| *n == name) {
            Some(t) => {
                t.1 += d;
                t.2 += 1;
            }
            None => self.times.push((name, d, 1)),
        }
        r
    }

    /// The totals, largest first, at level `DEBUG`.
    pub fn report(&self, what: &str) {
        if !enabled(DEBUG) || self.times.is_empty() {
            return;
        }
        let mut times = self.times.clone();
        times.sort_by(|a, b| b.1.cmp(&a.1));
        let total: Duration = times.iter().map(|t| t.1).sum();
        line(DEBUG, format_args!("{what}: {} in all", show(total)));
        for (name, d, n) in times {
            let share = if total.as_secs_f64() > 0.0 { d.as_secs_f64() / total.as_secs_f64() * 100.0 } else { 0.0 };
            line(DEBUG, format_args!("  {name:<16} {:>9} {share:>5.1}%  ({n} runs)", show(d)));
        }
    }
}

thread_local! {
    /// The optimizer's passes' times, summed over a whole `optimize`.
    pub static PASSES: std::cell::RefCell<Tally> = std::cell::RefCell::new(Tally::default());
}
