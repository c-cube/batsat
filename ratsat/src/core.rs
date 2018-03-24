use {Lit, Var, lbool};

#[derive(Debug)]
pub struct Solver {
    verbosity: i32,
    clauses: Vec<Vec<Lit>>,
    num_vars: u32,
    trail_lim: Vec<i32>,
    ok: bool,
}

impl Default for Solver {
    fn default() -> Self {
        Self {
            verbosity: 0,
            clauses: vec![],
            num_vars: 0,
            trail_lim: vec![],
            ok: true,
        }
    }
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
    pub fn add_clause_reuse(&mut self, clause: &mut Vec<Lit>) -> bool {
        eprintln!("add_clause({:?})", clause);
        debug_assert_eq!(self.decision_level(), 0);
        if !self.ok {
            return false;
        }
        clause.sort();
        let mut last_lit = Lit::UNDEF;
        let mut j = 0;
        for i in 0..clause.len() {
            let val = lbool::UNDEF; // TODO
            if val == lbool::TRUE || clause[i] == !last_lit {
            } else if val != lbool::FALSE && clause[i] != last_lit {
                last_lit = clause[i];
                clause[j] = clause[i];
                j += 1;
            }
        }
        clause.resize(j, Lit::UNDEF);
        self.clauses.push(clause.to_vec());
        true
    }
    pub fn decision_level(&self) -> u32 {
        self.trail_lim.len() as u32
    }
}
