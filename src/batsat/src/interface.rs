
/* Main Interface */

use std::fmt::Debug;
use clause::{Var,Lit,lbool};

/// Result returned by the `final_check` call.
///
/// A theory can validate the model (returning `Done`)
/// or signal a conflict (`Conflict`). If the theory also pushed clauses
/// upon `Done` then the model search will resume.
#[derive(Debug,PartialEq,Eq,Clone,Copy)]
pub enum FinalCheckRes {
    Done,
    Conflict,
}

/// Theory that parametrizes the solver and can react on events
pub trait Theory<S : TheoryArgument> : Debug {
    /// Check the model candidate `model` thoroughly.
    ///
    /// If the partial model isn't satisfiable in the theory then
    /// this *must* return `FinalCheckRes::Conflict` and push a conflict
    /// clause.
    fn final_check(&mut self, &mut S, model: &[Lit]) -> FinalCheckRes;

    /// Push a new backtracking level
    fn create_level(&mut self);

    /// Pop `n` levels from the stack
    fn pop_level(&mut self, n: u32);

    /// Called whenever the solver gets a new clause
    fn on_add_clause(&mut self, c: &S::Clause, learnt: bool);
}

/// Interface provided to the theory
pub trait TheoryArgument {
    /// The public representation of clauses from a theory's perspective
    type Clause : Debug+PartialEq+Eq;

    /// Access the literals of a clause
    fn clause_lits(&self, c: &Self::Clause) -> &[Lit];

    /// Is this a learnt clause?
    fn clause_learnt(&self, c: &Self::Clause) -> bool;

    /// Allocate a new literal
    fn new_lit(&mut self) -> Lit;

    /// Push a theory lemma into the solver
    fn add_theory_lemma(&mut self, &[Lit]);
}

/// Main interface for a solver: it makes it possible to add clauses,
/// allocate variables, and check for satisfiability
pub trait SolverInterface {
    fn num_vars(&self) -> u32;
    fn num_clauses(&self) -> u32;
    fn num_conflicts(&self) -> u32;

    fn is_ok(&self) -> bool;

    /// Print some current statistics to standard output.
    fn print_stats(&self);

    /// Creates a new SAT variable in the solver. If 'decision' is cleared, variable will not be
    /// used as a decision variable (NOTE! This has effects on the meaning of a SATISFIABLE result).
    fn new_var(&mut self, upol: lbool, dvar: bool) -> Var;

    /// Create a new variable with the default polarity
    fn new_var_default(&mut self) -> Var;

    /// Add a clause to the solver. Returns `false` if the solver is in
    /// an `UNSAT` state.
    fn add_clause_reuse(&mut self, clause: &mut Vec<Lit>) -> bool;

    /// Simplify the clause database according to the current top-level assigment. Currently, the only
    /// thing done here is the removal of satisfied clauses, but more things can be put here.
    fn simplify(&mut self) -> bool;

    /// Search for a model that respects a given set of assumptions (With resource constraints).
    fn solve_limited(&mut self, assumps: &[Lit]) -> lbool;

    /// Obtain the slice of literals that are proved at level 0.
    ///
    /// These literals will keep this value from now on.
    fn proved_at_lvl_0(&self) -> &[Lit];

    /// Query whole model
    ///
    /// Precondition: last result was `Sat` (ie `lbool::TRUE`)
    fn get_model(&self) -> &[lbool];

    /// Query model for var
    ///
    /// Precondition: last result was `Sat` (ie `lbool::TRUE`)
    fn value_var(&self, Var) -> lbool;

    /// Query model for lit
    fn value_lit(&self, Lit) -> lbool;

    /// Value of this literal if it's assigned at level 0, or `UNDEF` otherwise
    fn value_lvl_0(&self, Lit) -> lbool;

    /// Return unsat core (as a subset of assumptions).
    ///
    /// Precondition: last result was `Unsat`
    fn unsat_core(&self) -> &[Lit];

    /// Does this literal occur in the unsat-core?
    ///
    /// Precondition: last result was `Unsat`
    fn unsat_core_contains_lit(&self, lit: Lit) -> bool;

    /// Does this variable occur in the unsat-core?
    ///
    /// Precondition: last result was `Unsat`
    fn unsat_core_contains_var(&self, v: Var) -> bool;
}

