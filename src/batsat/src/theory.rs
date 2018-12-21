
use std::default::Default;
use crate::clause::{Var,Lit,lbool};

/// Result returned by the `final_check` call.
///
/// A theory can validate the model (returning `Done`)
/// or signal a conflict (`Conflict`). If the theory also pushed clauses
/// upon `Done` then the model search will resume.
/// If the theory returns `Conflict(c)` then `c` must be a clause false
/// in the current model.
#[derive(Debug,PartialEq,Eq,Clone,Copy)]
pub enum CheckRes<C> {
    Done,
    Conflict(C),
}

/// Theory that parametrizes the solver and can react on events
pub trait Theory {
    /// Check the model candidate `model` thoroughly.
    ///
    /// Call `TheoryArgument.model()` to obtain the model.
    /// If the partial model isn't satisfiable in the theory then
    /// this *must* return `CheckRes::Conflict` and push a conflict
    /// clause.
    fn final_check<'a, S>(&mut self, acts: &mut S)
        -> CheckRes<S::Conflict>
        where S: TheoryArgument;

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
    /// This can return `Done` even if the partial model is invalid,
    /// if the theory deems it too costly to verify.
    /// The model will be checked again in `final_check`.
    ///
    /// The default implementation just returns `Done` without doing anything.
    fn partial_check<S>(&mut self, _acts: &mut S) -> CheckRes<S::Conflict>
        where S: TheoryArgument
    { CheckRes::Done }


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
    /// A conflict clause, which can only be created by `mk_conflict`
    type Conflict;

    /// Current (possibly partial) model
    fn model(&self) -> &[Lit];

    /// Allocate a new literal
    fn mk_new_lit(&mut self) -> Lit;

    /// Push a theory lemma into the solver.
    ///
    /// This is useful for lemma-on-demand or theory splitting, but can
    /// be relatively costly.
    fn add_theory_lemma(&mut self, c: &[Lit]);

    /// Propagate the literal `p`, which is theory-implied by the current trail.
    ///
    /// This will add `p` on the trail. The theory must be ready to
    /// provide an explanation via `Theory::explain_prop(p)` if asked to
    /// during conflict resolution.
    fn propagate(&mut self, p: Lit);

    /// Make a conflict clause.
    ///
    /// This should be used in the theory to returns `FinalCheckRes::Conflict`.
    ///
    /// ## Params
    /// - `costly` if true, indicates that the conflict `c` was costly to produce.
    ///     This is a hint for the SAT solver to keep the theory lemma that corresponds
    ///     to `c` along with the actual learnt clause.
    fn mk_conflict(&mut self, lits: &[Lit], costly: bool) -> Self::Conflict;

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
    fn new() -> Self { EmptyTheory(0) }
}

impl Default for EmptyTheory {
    fn default() -> Self { EmptyTheory::new() }
}

impl Theory for EmptyTheory {
    fn final_check<S>(&mut self, _: &mut S)
        -> CheckRes<S::Conflict> where S: TheoryArgument { CheckRes::Done }
    fn create_level(&mut self) { self.0 += 1 }
    fn pop_levels(&mut self, n: usize) {
        debug_assert!(self.0 >= n);
        self.0 -= n
    }
    fn n_levels(&self) -> usize { self.0 }
    fn explain_propagation(&mut self, _p: Lit) -> &[Lit] { unreachable!() }
}
