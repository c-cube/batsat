extern crate batsat;

#[link(name="batsat")]

use std::mem;
use std::ops;
use std::os::raw::{c_int,c_void};

use batsat::{Solver as InnerSolver,Var,Lit,lbool,SolverInterface,HasStats,HasUnsatCore};

pub struct Solver {
    s: InnerSolver,
    vars: Vec<Var>, // int->var
    cur_clause: Vec<Lit>,
    assumptions: Vec<Lit>,
}

impl Solver {
    fn new() -> Self {
        Solver {
            s: InnerSolver::default(), vars: Vec::new(),
            cur_clause: vec![], assumptions: vec![],
        }
    }
}

impl Solver {
    fn decompose(&mut self) -> (&mut InnerSolver, &mut Vec<Lit>, &mut Vec<Lit>) {
        (&mut self.s, &mut self.cur_clause, &mut self.assumptions)
    }

    /// Allocate variables until we get the one corresponding to `x`
    fn get_var(&mut self, x: usize) -> Var {
        while x >= self.vars.len() {
            self.vars.push(self.s.new_var_default());
        }
        self.vars[x]
    }

    #[inline]
    fn get_lit(&mut self, lit: c_int) -> Lit {
        assert!(lit != 0);
        let v = self.get_var(lit.abs() as usize);
        Lit::new(v, lit>0)
    }
}

impl ops::Deref for Solver {
    type Target = InnerSolver;
    fn deref(&self) -> &Self::Target { &self.s }
}

impl ops::DerefMut for Solver {
    fn deref_mut(&mut self) -> &mut Self::Target { &mut self.s }
}

#[inline]
fn get_solver(ptr: * mut c_void) -> Box<Solver> {
    unsafe{ Box::from_raw(ptr as *mut Solver) }
}

#[no_mangle]
pub extern "C" fn batsat_delete(ptr: *mut c_void) {
    let s = get_solver(ptr);
    mem::drop(s);
}

#[no_mangle]
pub extern "C" fn batsat_new() -> *mut c_void {
    let solver = Box::new(Solver::new());
    let ptr = Box::into_raw(solver) as *mut Solver as *mut c_void;
    return ptr
}

#[no_mangle]
pub extern "C" fn batsat_simplify(ptr: *mut c_void) -> bool {
    let mut solver = get_solver(ptr);
    let res = solver.simplify();
    mem::forget(solver);
    return res
}

/// Add literal, or add clause if the lit is 0
#[no_mangle]
pub extern "C" fn batsat_addlit(ptr: *mut c_void, lit: c_int) -> bool {
    let mut solver = get_solver(ptr);

    let mut res = true;
    if lit == 0 {
        // push current clause into vector `clauses`, reset it
        let (solver, cur, _) = solver.decompose();
        res = solver.add_clause_reuse(cur);
        cur.clear();
    } else {
        // push literal into clause
        let lit = solver.get_lit(lit);
        solver.cur_clause.push(lit);
    }

    mem::forget(solver);
    res
}

/// Add assumption into the solver
#[no_mangle]
pub extern "C" fn batsat_assume(ptr: *mut c_void, lit: c_int) {
    let mut solver = get_solver(ptr);

    assert!(lit != 0);
    let lit = solver.get_lit(lit);
    solver.assumptions.push(lit);

    mem::forget(solver);
}

#[no_mangle]
pub extern "C" fn batsat_solve(ptr: *mut c_void) -> bool {
    let mut solver = get_solver(ptr);

    let r = {
        let (s, _, assumptions) = solver.decompose();
        let lb = s.solve_limited(&assumptions);
        assumptions.clear(); // reset assumptions
        assert_ne!(lb, lbool::UNDEF); // can't express that in a bool
        lb != lbool::FALSE
    };
    mem::forget(solver);
    r
}

#[no_mangle]
pub extern "C" fn batsat_getmodel(ptr: *mut c_void, lit: c_int) -> c_int {
    let mut solver = get_solver(ptr);

    let lit = solver.get_lit(lit);
    let r = solver.s.value_lit(lit);
    mem::forget(solver);
    r.to_u8() as c_int
}

#[no_mangle]
pub extern "C" fn batsat_check_assumption(ptr: *mut c_void, lit: c_int) -> bool {
    let mut solver = get_solver(ptr);

    // check unsat-core
    let lit = solver.get_lit(lit);
    let res = solver.s.unsat_core_contains_var(lit.var());

    mem::forget(solver);
    res
}

#[no_mangle]
pub extern "C" fn batsat_nvars(ptr: *mut c_void) -> c_int {
    let solver = get_solver(ptr);
    let r = solver.s.num_vars() as c_int;
    mem::forget(solver);
    r
}

#[no_mangle]
pub extern "C" fn batsat_nclauses(ptr: *mut c_void) -> c_int {
    let solver = get_solver(ptr);
    let r = solver.s.num_clauses() as c_int;
    mem::forget(solver);
    r
}

#[no_mangle]
pub extern "C" fn batsat_nconflicts(_ptr: *mut c_void) -> c_int {
    unimplemented!();
}


