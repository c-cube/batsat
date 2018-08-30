
/* Main Interface */

use clause::{Var,Lit,lbool};

/// Main interface for a solver: it makes it possible to add clauses,
/// allocate variables, and check for satisfiability
pub trait SolverInterface {
    fn set_verbosity(&mut self, verbosity: i32);
    fn verbosity(&self) -> i32;

    fn num_vars(&self) -> u32;

    /// Creates a new SAT variable in the solver. If 'decision' is cleared, variable will not be
    /// used as a decision variable (NOTE! This has effects on the meaning of a SATISFIABLE result).
    fn new_var(&mut self, upol: lbool, dvar: bool) -> Var;

    /// Create a new variable with the default polarity
    fn new_var_default(&mut self) -> Var;

    /// Add a clause to the solver. Returns `false` if the solver is in
    /// an `UNSAT` state.
    fn add_clause_reuse(&mut self, clause: &mut Vec<Lit>) -> bool;

    /// Search for a model that respects a given set of assumptions (With resource constraints).
    fn solve_limited(&mut self, assumps: &[Lit]) -> lbool;

    /// Query model for var
    fn value_var(&self, Var) -> lbool;

    /// Query model for lit
    fn value_lit(&self, Lit) -> lbool;
}

/// Trait for solvers able to provide an unsat core if `unsat` was found
pub trait HasUnsatCore : SolverInterface {
    /// Return unsat core (as a subset of assumptions)
    fn unsat_core(&self) -> Vec<Lit>;

    /// Does this literal occur in the unsat-core?
    fn unsat_core_contains_lit(&self, lit: Lit) -> bool;

    /// Does this variable occur in the unsat-core?
    fn unsat_core_contains_var(&self, v: Var) -> bool;
}

pub trait HasStats : SolverInterface {
    fn num_clauses(&self) -> u32;

    /// Print some current statistics to standard output.
    fn print_stats(&self);
}
