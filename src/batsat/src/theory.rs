
use std::default::Default;
use crate::clause::{Var,Lit,lbool};

/// Theory that parametrizes the solver and can react on events.
pub trait Theory {
    /// Check the model candidate `model` thoroughly.
    ///
    /// Call `acts.model()` to obtain the model.
    /// If the partial model isn't satisfiable in the theory then
    /// this *must* call `acts.raise_conflict` with a valid lemma that is
    /// the negation of a subset of the `model`.
    fn final_check<'a, S>(&mut self, acts: &mut S) where S: TheoryArgument;

    /// Push a new backtracking level
    fn create_level(&mut self);

    /// Pop `n` levels from the stack
    fn pop_levels(&mut self, n: usize);

    /// Number of levels
    fn n_levels(&self) -> usize;

    /// Check partial model (best effort).
    ///
    /// The whole partial model so far is `acts.model()`,
    /// but the theory may remember the length of the previous slice and use
    /// `acts.model()[prev_len..]` to get only the new literals.
    ///
    /// This is allowed to not raise a conflict even if the partial
    /// model is invalid, if the theory deems it too costly to verify.
    /// The model will be checked again in `final_check`.
    ///
    /// The default implementation just returns without doing anything.
    fn partial_check<S>(&mut self, _acts: &mut S) where S: TheoryArgument {}


    /// If the theory uses `TheoryArgument::propagate`, it must implement
    /// this function to explain the propagations.
    ///
    /// `p` is the literal that has been propagated by the theory in a prefix
    /// of the current trail.
    fn explain_propagation(&mut self, _p: Lit) -> &[Lit];
}

/// Interface provided to the theory.
///
/// This is where the theory can perform actions such as adding clauses.
pub trait TheoryArgument {
    /// Current (possibly partial) model
    fn model(&self) -> &[Lit];

    /// Allocate a new literal
    fn mk_new_lit(&mut self) -> Lit;

    /// Push a theory lemma into the solver.
    ///
    /// This is useful for lemma-on-demand or theory splitting, but can
    /// be relatively costly.
    ///
    /// NOTE: This is not fully supported yet.
    fn add_theory_lemma(&mut self, c: &[Lit]);

    /// Propagate the literal `p`, which is theory-implied by the current trail.
    ///
    /// This will add `p` on the trail. The theory must be ready to
    /// provide an explanation via `Theory::explain_prop(p)` if asked to
    /// during conflict resolution.
    fn propagate(&mut self, p: Lit);

    /// Add a conflict clause.
    ///
    /// This should be used in the theory when the current partial model
    /// is unsatisfiable. It will force the SAT solver to backtrack.
    /// All propagations added with `propagate` during this session
    /// will be discarded.
    ///
    /// ## Params
    /// - `lits` a clause that is a tautology of the theory (ie a lemma)
    ///     and that is false in the current (partial) model.
    /// - `costly` if true, indicates that the conflict `c` was costly to produce.
    ///     This is a hint for the SAT solver to keep the theory lemma that corresponds
    ///     to `c` along with the actual learnt clause.
    fn raise_conflict(&mut self, lits: &[Lit], costly: bool);

    /// Value of given var in current model
    #[inline(always)]
    fn value(&self, v: Var) -> lbool;

    /// Value of given literal in current model
    #[inline(always)]
    fn value_lit(&self, lit: Lit) -> lbool;
}

/// Trivial theory that does nothing
pub struct EmptyTheory(usize);

impl EmptyTheory {
    /// New empty theory.
    pub fn new() -> Self { EmptyTheory(0) }
}

impl Default for EmptyTheory {
    fn default() -> Self { EmptyTheory::new() }
}

// theory for any context.
impl Theory for EmptyTheory {
    fn final_check<S>(&mut self, _: &mut S) where S: TheoryArgument { }
    fn create_level(&mut self) { self.0 += 1 }
    fn pop_levels(&mut self, n: usize) {
        debug_assert!(self.0 >= n);
        self.0 -= n
    }
    fn n_levels(&self) -> usize { self.0 }
    fn explain_propagation(&mut self, _p: Lit) -> &[Lit] { unreachable!() }
}
