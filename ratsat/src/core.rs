use {lbool, Lit, Var};
use clause::VMap;

#[derive(Debug)]
pub struct Solver {
    verbosity: i32,
    clauses: Vec<Vec<Lit>>,
    num_vars: u32,
    trail_lim: Vec<i32>,
    assigns: VMap<lbool>,
    ok: bool,
}

impl Default for Solver {
    fn default() -> Self {
        Self {
            verbosity: 0,
            clauses: vec![],
            num_vars: 0,
            trail_lim: vec![],
            assigns: VMap::new(),
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
        let var = Var::from_idx(self.num_vars as u32);
        self.num_vars += 1;
        self.assigns.insert_default(var, lbool::UNDEF);
        var
    }
    pub fn value(&self, x: Var) -> lbool {
        self.assigns[x]
    }
    pub fn value_lit(&self, x: Lit) -> lbool {
        self.assigns[x.var()] ^ x.sign()
    }
    pub fn add_clause_reuse(&mut self, clause: &mut Vec<Lit>) -> bool {
        // eprintln!("add_clause({:?})", clause);
        debug_assert_eq!(self.decision_level(), 0);
        if !self.ok {
            return false;
        }
        clause.sort();
        let mut last_lit = Lit::UNDEF;
        let mut j = 0;
        for i in 0..clause.len() {
            let value = self.value_lit(clause[i]);
            if value == lbool::TRUE || clause[i] == !last_lit {
            } else if value != lbool::FALSE && clause[i] != last_lit {
                last_lit = clause[i];
                clause[j] = clause[i];
                j += 1;
            }
        }
        clause.resize(j, Lit::UNDEF);
        if clause.len() == 0 {
            self.ok = false;
            return false;
        } else if clause.len() == 1 {
            // self.unchecked_enqueue(clause[0]);
        } else {
            // ca alloc
            self.clauses.push(clause.to_vec());
            // self.attach_clause(clause);
        }

        true
    }
    pub fn decision_level(&self) -> u32 {
        self.trail_lim.len() as u32
    }
}
