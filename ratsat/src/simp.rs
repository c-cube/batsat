use std::ops;

use {Solver, Lit, Var};
use core::CoreSolver;

#[derive(Debug, Default)]
pub struct SimpSolver {
    base: CoreSolver,
}

impl ops::Deref for SimpSolver {
    type Target = CoreSolver;
    fn deref(&self) -> &Self::Target {
        &self.base
    }
}
impl ops::DerefMut for SimpSolver {
    fn deref_mut(&mut self) -> &mut Self::Target {
        &mut self.base
    }
}

impl SimpSolver {
    pub fn num_clauses(&self) -> u32 {
        CoreSolver::num_clauses(self)
    }
}

impl Solver for SimpSolver {
    fn verbosity(&self) -> i32 {
        CoreSolver::verbosity(self)
    }
    fn num_vars(&self) -> u32 {
        CoreSolver::num_vars(self)
    }
    fn new_var(&mut self) -> Var {
        CoreSolver::new_var(self)
    }
    fn add_clause_owned(&mut self, clause: Vec<Lit>) {
        CoreSolver::add_clause_owned(self, clause)
    }
}
