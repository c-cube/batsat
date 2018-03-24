use {Lit, Var};

#[derive(Debug, Default)]
pub struct Solver {
    verbosity: i32,
    clauses: Vec<Vec<Lit>>,
    num_vars: u32,
}

impl Solver {
    pub fn set_verbosity(&mut self, verbosity: i32) {
        debug_assert!(0 <= verbosity && verbosity <= 2);
        self.verbosity = verbosity;
    }
    pub fn num_clauses(&self) -> u32 {
        self.clauses.len() as u32
    }
    pub fn verbosity(&self) -> i32 {
        self.verbosity
    }
    pub fn num_vars(&self) -> u32 {
        self.num_vars
    }
    pub fn new_var(&mut self) -> Var {
        let var = self.num_vars;
        self.num_vars += 1;
        Var::from_idx(var as u32)
    }
    pub fn add_clause_owned(&mut self, clause: Vec<Lit>) {
        eprintln!("add_clause({:?})", clause);
        self.clauses.push(clause);
    }
}
