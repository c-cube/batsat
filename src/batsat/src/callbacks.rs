
use super::clause::{lbool};

/// Basic callbacks to the solver
///
/// Typically intended for printing/statistics
pub trait Callbacks {
    /// Called before starting to solve
    fn on_start(&mut self) {}

    /// Called whenever the solver simplifies its set of clauses
    fn on_simplify(&mut self) {}

    /// Called after a clause GC
    fn on_gc(&mut self, _old_size: usize, _new_size: usize) {}

    /// called regularly to indicate progress
    fn on_progress(&mut self, _f: &ProgressStatus) {}

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
    pub n_clauses: u32,
    pub n_clause_lits: i32,
    pub max_learnt: i32,
    pub n_learnt: u32,
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
    fn default() -> Self { Basic::new() }
}
