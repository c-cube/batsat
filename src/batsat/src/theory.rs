use {crate::clause::Lit, std::default::Default};

/// Argument passed to the Theory
pub use crate::core::TheoryArg;

/// Theory that parametrizes the solver and can react on events.
pub trait Theory {
    /// Check the model candidate `model` thoroughly.
    ///
    /// Call `acts.model()` to obtain the model.
    /// If the partial model isn't satisfiable in the theory then
    /// this *must* call `acts.raise_conflict` with a valid lemma that is
    /// the negation of a subset of the `model`.
    fn final_check(&mut self, acts: &mut TheoryArg);

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
    fn partial_check(&mut self, _acts: &mut TheoryArg) {}

    /// If the theory uses `TheoryArgument::propagate`, it must implement
    /// this function to explain the propagations.
    ///
    /// `p` is the literal that has been propagated by the theory in a prefix
    /// of the current trail.
    fn explain_propagation(&mut self, _p: Lit) -> &[Lit];
}

/// Trivial theory that does nothing
pub struct EmptyTheory(usize);

impl EmptyTheory {
    /// New empty theory.
    pub fn new() -> Self {
        EmptyTheory(0)
    }
}

impl Default for EmptyTheory {
    fn default() -> Self {
        EmptyTheory::new()
    }
}

// theory for any context.
impl Theory for EmptyTheory {
    fn final_check(&mut self, _: &mut TheoryArg) {}
    fn create_level(&mut self) {
        self.0 += 1
    }
    fn pop_levels(&mut self, n: usize) {
        debug_assert!(self.0 >= n);
        self.0 -= n
    }
    fn n_levels(&self) -> usize {
        self.0
    }
    fn explain_propagation(&mut self, _p: Lit) -> &[Lit] {
        unreachable!()
    }
}
