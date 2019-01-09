
/// # IPASIR
///
/// API for batsat following the [IPASIR](https://github.com/biotomas/ipasir) convention.
/// See `ipasir` directory at the root of the project

extern crate batsat;

use batsat::{self as sat, Var, Lit, lbool, SolverInterface};
use std::mem;
use std::boxed::Box;
use std::os::raw::{c_char,c_void,c_int};

static NAME : &'static str = "batsat-0.2\0";

/// The wrapper around a solver. It contains partial clauses, assumptions, etc.
struct IpasirSolver {
    solver: SAT,
    vars: Vec<Var>, // int->var
    cur: Vec<Lit>, // current clause
    assumptions: Vec<Lit>,
}

type SAT = sat::Solver<CB>;

type LearntCB = *const extern "C" fn(*mut c_void, *const c_int) -> c_void;

/// Callbacks
struct CB {
    basic: sat::BasicCallbacks,
    lits: Vec<c_int>, // temporary
    lit_to_int: sat::VMap<c_int>, // reverse mapping lit->int
    learn_cb: Option<(c_int, *mut c_void, LearntCB)>,
}

impl IpasirSolver {
    fn new() -> IpasirSolver {
        IpasirSolver {
            vars: Vec::new(),
            solver: SAT::new(sat::SolverOpts::default(), CB::new()),
            cur: Vec::new(),
            assumptions: Vec::new() }
    }

    fn decompose(&mut self) -> (&mut SAT, &mut Vec<Lit>, &mut Vec<Lit>) {
        (&mut self.solver, &mut self.cur, &mut self.assumptions)
    }

    /// Allocate variables until we get the one corresponding to `x`
    fn get_var(&mut self, x: usize) -> Var {
        while x >= self.vars.len() {
            let i = self.vars.len();
            let v = self.solver.new_var_default();
            self.vars[i] = v;
            // reverse mapping
            self.solver.cb_mut().lit_to_int.insert(v, x as c_int, 0);
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

impl CB {
    fn new() -> Self {
        CB {
            basic: sat::BasicCallbacks::new(),
            lits: vec!(),
            lit_to_int: sat::VMap::new(),
            learn_cb: None,
        }
    }
}

impl batsat::Callbacks for CB {
    fn on_new_clause(&mut self, lits: &[Lit], kind: sat::ClauseKind) {
        if self.learn_cb.is_none() { return }
        if kind != sat::ClauseKind::Learnt { return }

        let learn = &mut self.learn_cb.unwrap();
        if lits.len() > learn.0 as usize { return } // max len

        self.lits.clear();
        for lit in lits {
            let mut i = self.lit_to_int[lit.var()];
            if !lit.sign() { i = -i }
            self.lits.push(i);
        }
        self.lits.push(0);
        unsafe {
            (*learn.2)(learn.1, self.lits.as_ptr());
        }
    }
}

#[no_mangle]
pub extern "C" fn ipasir_signature() -> * const c_char {
    let ptr : *const c_char = NAME.as_bytes().as_ptr() as *const u8 as *const i8;
    ptr
}

#[no_mangle]
pub extern "C" fn ipasir_init() -> * const c_void {
    let s = Box::new(IpasirSolver::new());
    let ptr = Box::into_raw(s) as *const IpasirSolver as *const c_void;
    ptr
}

#[inline]
fn get_solver(ptr: * mut c_void) -> Box<IpasirSolver> {
    unsafe{ Box::from_raw(ptr as *mut IpasirSolver) }
}

#[no_mangle]
pub extern "C" fn ipasir_release(ptr: *mut c_void) {
    let s = get_solver(ptr); // drop
    mem::drop(s)
}

#[no_mangle]
pub extern "C" fn ipasir_add(ptr: *mut c_void, lit: c_int) {
    let mut s = get_solver(ptr);
    if lit == 0 {
        // push current clause into vector `clauses`, reset it
        let (solver, cur, _) = s.decompose();
        solver.add_clause_reuse(cur);
        cur.clear();
    } else {
        // push literal into clause
        let lit = s.get_lit(lit);
        s.cur.push(lit);
    }

    mem::forget(s)
}

#[no_mangle]
pub extern "C" fn ipasir_assume(ptr: *mut c_void, lit: c_int) {
    let mut s = get_solver(ptr);
    assert!(lit != 0);
    let lit = s.get_lit(lit);
    s.assumptions.push(lit);

    mem::forget(s)
}

fn lbool_to_int(x: lbool) -> c_int {
    match x {
        x if x == lbool::UNDEF => 0,
        x if x == lbool::TRUE => 10,
        x if x == lbool::FALSE => 20,
        _ => unreachable!()
    }
}

#[no_mangle]
pub extern "C" fn ipasir_solve(ptr: *mut c_void) -> c_int {
    let mut s = get_solver(ptr);

    let res = {
        let (solver, _, assumptions) = s.decompose();

        // solve under assumptions
        let res = solver.solve_limited(&assumptions);

        // reset assumptions
        assumptions.clear();
        res
    };

    mem::forget(s);
    lbool_to_int(res)
}

#[no_mangle]
pub extern "C" fn ipasir_val(ptr: *mut c_void, lit: c_int) -> c_int {
    let mut s = get_solver(ptr);

    let var = s.get_var(lit.abs() as usize);
    let val = {
        let v = s.solver.get_model()[var.idx() as usize];
        if lit > 0 { v } else { -v }
    };

    mem::forget(s);
    match val {
        x if x == lbool::UNDEF => 0,
        x if x == lbool::TRUE => lit,
        x if x == lbool::FALSE => -lit,
        _ => unreachable!()
    }
}

#[no_mangle]
pub extern "C" fn ipasir_failed(ptr: *mut c_void, lit: c_int) -> c_int {
    let mut s = get_solver(ptr);

    // check unsat-core
    let lit = s.get_lit(lit);
    let res = s.solver.unsat_core_contains_var(lit.var());

    mem::forget(s);
    res as c_int
}

#[no_mangle]
pub extern "C" fn ipasir_set_terminate(
    ptr: *mut c_void,
    state: *mut c_void,
    terminate: extern "C" fn(*mut c_void) -> c_int
) {
    let mut s = get_solver(ptr);

    // set handler using the given C function
    let f = move || {
        let should_stop = terminate(state) != 0;
        should_stop
    };
    s.solver.cb_mut().basic.set_stop(f);

    mem::forget(s)
}

#[no_mangle]
pub extern "C" fn ipasir_set_learn(
    ptr: *mut c_void,
    state: *mut c_void,
    max_len: c_int,
    learn: LearntCB
) {
    let mut s = get_solver(ptr);

    {
        let cb = s.solver.cb_mut();
        cb.learn_cb = Some ((max_len, state, learn));
    }

    mem::forget(s)
}
