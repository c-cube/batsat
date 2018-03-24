use {Solver, Lit, Var};

#[derive(Debug, Default)]
pub struct CoreSolver {
    verbosity: i32,
    clauses: Vec<Vec<Lit>>,
    num_vars: u32,
}

impl CoreSolver {
    pub fn set_verbosity(&mut self, verbosity: i32) {
        debug_assert!(0 <= verbosity && verbosity <= 2);
        self.verbosity = verbosity;
    }
    pub fn num_clauses(&self) -> u32 {
        self.clauses.len() as u32
    }
}

impl Solver for CoreSolver {
    fn verbosity(&self) -> i32 {
        self.verbosity
    }
    fn num_vars(&self) -> u32 {
        self.num_vars
    }
    fn new_var(&mut self) -> Var {
        let var = self.num_vars;
        self.num_vars += 1;
        Var::from_idx(var as u32)
    }
    fn add_clause_owned(&mut self, clause: Vec<Lit>) {
        eprintln!("add_clause({:?})", clause);
        self.clauses.push(clause);
    }
}

