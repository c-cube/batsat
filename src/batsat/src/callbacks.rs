
use {std::fmt, super::clause::{self, lbool, Lit}, super::ClauseKind};

/// Basic callbacks to the solver
///
/// Typically intended for printing/statistics
pub trait Callbacks : Sized {
    /// Called before starting to solve
    fn on_start(&mut self) {}

    /// Called whenever the solver simplifies its set of clauses
    fn on_simplify(&mut self) {}

    /// Called whenever the SAT solver restarts
    fn on_restart(&mut self) {}

    /// Called after a clause GC
    fn on_gc(&mut self, _old_size: usize, _new_size: usize) {}

    /// Called whenever a new clause is learnt.
    ///
    /// ## Params
    /// - c: list of literals of the clause
    /// - src: specifies where the clause comes from
    fn on_new_clause(&mut self, _c: &[Lit], _src: clause::Kind) {}

    /// Called when a clause is deleted.
    fn on_delete_clause(&mut self, _c: &[Lit]) {}

    /// called regularly to indicate progress
    fn on_progress<F>(&mut self, _f: F) where F: FnOnce() -> ProgressStatus {}

    /// Called when a result is computed
    fn on_result(&mut self, _s: lbool) {}

    /// Should we stop? called regularly for asynchronous interrupts and such
    fn stop(&self) -> bool { false }
}

/// Progress indicator from the SAT solver.
///
/// This is given to `Callbacks` regularly so it can log it somehow.
#[derive(Debug,Clone,Copy)]
pub struct ProgressStatus {
    pub conflicts: i32,
    pub dec_vars: i32,
    pub n_clauses: u64,
    pub n_clause_lits: i32,
    pub max_learnt: i32,
    pub n_learnt: u64,
    pub n_learnt_lits: f64,
    pub progress_estimate: f64
}

/// Basic set of callbacks
///
/// This doesn't do anything except storing a function to `stop`
pub struct Basic {
    stop: Option<Box<dyn Fn() -> bool>>, // to stop
}

impl Callbacks for Basic {
    fn stop(&self) -> bool {
        match self.stop {
            None => false,
            Some(ref f) => f(),
        }
    }
}

impl Basic {
    /// Allocate a new set of callbacks
    pub fn new() -> Self { Basic {stop:None} }

    /// Set the `stop` function
    pub fn set_stop<F>(&mut self, f: F) where F : 'static + Fn() -> bool {
        self.stop = Some(Box::new(f));
    }
}

impl Default for Basic {
    fn default() -> Self { Self::new() }
}

/// Basic set of callbacks, maintaining some statistics and a "stop" predicate.
pub struct Stats {
    basic: Basic,
    pub n_restarts: usize,
    pub n_clauses: u64,
    pub n_theory: u64,
    pub n_learnt: u64,
    pub n_gc: usize,
}

impl Callbacks for Stats {
    #[inline]
    fn stop(&self) -> bool { self.basic.stop() }

    fn on_restart(&mut self) { self.n_restarts += 1 }
    #[inline(always)]
    fn on_gc(&mut self, _: usize, _: usize) { self.n_gc += 1 }
    fn on_new_clause(&mut self, _: &[Lit], k: ClauseKind) {
        self.n_clauses += 1;
        match k {
            ClauseKind::Learnt => self.n_learnt += 1,
            ClauseKind::Theory => self.n_theory += 1,
            ClauseKind::Axiom => (),
        }
    }
}

impl Stats {
    /// Allocate a new set of callbacks.
    pub fn new() -> Self {
        Self {
            basic: Basic::new(), 
            n_restarts: 0,
            n_clauses: 0,
            n_theory: 0,
            n_learnt: 0,
            n_gc: 0,
        }
    }

    /// Cast the statistics CB into a basic CB.
    #[inline(always)]
    pub fn basic_mut(&mut self) -> &mut Basic { &mut self.basic }
}

impl fmt::Display for Stats {
    fn fmt(&self, out: &mut fmt::Formatter) -> fmt::Result {
        write!(out, "restarts: {}, clauses: {} (th: {}, learnt: {}), gc: {}",
               self.n_restarts, self.n_clauses,
               self.n_theory, self.n_learnt, self.n_gc)
    }
}

impl Default for Stats {
    fn default() -> Self { Self::new() }
}
