/* Main Interface */

use crate::{
    clause::{lbool, Lit, Var},
    theory::{self, Theory},
};

/// Main interface for a solver: it makes it possible to add clauses,
/// allocate variables, and check for satisfiability
///
/// Some functions take a parameter `Th:Theory`, for SMT solving.
pub trait SolverInterface {
    fn num_vars(&self) -> u32;
    fn num_clauses(&self) -> u64;
    fn num_conflicts(&self) -> u64;
    fn num_propagations(&self) -> u64;
    fn num_decisions(&self) -> u64;
    fn num_restarts(&self) -> u64;

    /// Is the solver in a state that can still be satisfiable?
    fn is_ok(&self) -> bool;

    /// Print some current statistics to standard output.
    fn print_stats(&self);

    /// Creates a new SAT variable in the solver. If 'decision' is cleared, variable will not be
    /// used as a decision variable (NOTE! This has effects on the meaning of a SATISFIABLE result).
    fn new_var(&mut self, upol: lbool, dvar: bool) -> Var;

    /// Create a new variable with the default polarity.
    ///
    /// The default polarity is not specified.
    fn new_var_default(&mut self) -> Var;

    /// Get the `i`-th variable, possibly creating it if it doesn't already exist.
    fn var_of_int(&mut self, i: u32) -> Var;

    /// Add a clause to the solver. Returns `false` if the solver is in
    /// an `UNSAT` state.
    fn add_clause_reuse(&mut self, clause: &mut Vec<Lit>) -> bool;

    /// Simplify the clause database according to the current top-level assigment. Currently, the only
    /// thing done here is the removal of satisfied clauses, but more things can be put here.
    #[inline(always)]
    fn simplify(&mut self) -> bool {
        self.simplify_th(&mut theory::EmptyTheory::new())
    }

    /// Simplify using the given theory.
    fn simplify_th<Th: Theory>(&mut self, th: &mut Th) -> bool;

    /// Search for a model that respects a given set of assumptions (with resource constraints).
    ///
    /// - `assumps` is the list of assumptions to use (the literals that can be part of the unsat core)
    fn solve_limited(&mut self, assumps: &[Lit]) -> lbool {
        self.solve_limited_th(&mut theory::EmptyTheory::new(), assumps)
    }

    /// Solve using the given theory.
    ///
    /// - `th` is the theory.
    fn solve_limited_th<Th: Theory>(&mut self, th: &mut Th, assumps: &[Lit]) -> lbool;

    /// Obtain the slice of literals that are proved at level 0.
    ///
    /// These literals will keep this value from now on.
    fn proved_at_lvl_0(&self) -> &[Lit];

    /// Query whole model, as a mapping from `Var` to `lbool`.
    ///
    /// Precondition: last result was `Sat` (ie `lbool::TRUE`)
    fn get_model(&self) -> &[lbool];

    /// Query model for var.
    ///
    /// Precondition: last result was `Sat` (ie `lbool::TRUE`)
    fn value_var(&self, v: Var) -> lbool;

    /// Query model for lit.
    fn value_lit(&self, lit: Lit) -> lbool;

    /// Value of this literal if it's assigned at level 0, or `UNDEF` otherwise
    fn value_lvl_0(&self, lit: Lit) -> lbool;

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

#[cfg(test)]
mod test {
    use crate::*;
    #[test]
    fn test_reg7() {
        let mut solver: Solver<callbacks::Basic> =
            Solver::new(Default::default(), Default::default());
        let a = Lit::new(solver.new_var_default(), false);
        let b = Lit::new(solver.new_var_default(), false);
        assert!(solver.add_clause_reuse(&mut vec![a, b]));
        assert_eq!(solver.solve_limited(&[!b]), lbool::TRUE);
        assert!(solver.add_clause_reuse(&mut vec![!a, b]));
        assert!(solver.add_clause_reuse(&mut vec![!a, !b]));
        // panics in #7
        assert_eq!(solver.solve_limited(&[]), lbool::TRUE);
        assert_eq!(solver.solve_limited(&[a]), lbool::FALSE);
    }
}
