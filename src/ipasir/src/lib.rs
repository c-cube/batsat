
/// # IPASIR
///
/// API for ratsat following the [IPASIR](https://github.com/biotomas/ipasir) convention.
/// See `ipasir` directory at the root of the project

extern crate ratsat;

use ratsat::{Solver,Var,Lit,lbool};
use std::mem;
use std::boxed::Box;
use std::os::raw::{c_char,c_void,c_int};

static NAME : &'static str = "ratsat-0.2\0";

/// The wrapper around a solver. It contains partial clauses, assumptions, etc.
struct IpasirSolver {
    solver: Solver,
    vars: Vec<Var>, // int->var
    cur: Vec<Lit>, // current clause
    clauses: Vec<Vec<Lit>>,
    assumptions: Vec<Lit>,
}

impl IpasirSolver {
    fn new() -> IpasirSolver {
        IpasirSolver {
            vars: Vec::new(),
            solver: Solver::default(),
            cur: Vec::new(),
            clauses: Vec::new(), assumptions: Vec::new() }
    }

    /// Allocate variables until we get the one corresponding to `x`
    fn get_var(&mut self, x: usize) -> Var {
        while x >= self.vars.len() {
            let i = self.vars.len();
            self.vars[i] = self.solver.new_var_default();
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
        // push current clause into vector `clauses`, make another one
        let mut cur = Vec::new();
        mem::swap(&mut cur, &mut s.cur);
        s.clauses.push(cur)
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

    // get assumptions in a local var, reset the ones in `s`
    let mut assumptions = Vec::new();
    mem::swap(&mut s.assumptions, &mut assumptions);

    // add clauses
    while let Some(mut c) = s.clauses.pop() {
        s.solver.add_clause_reuse(&mut c);
    }
    s.clauses.clear();

    // solve under assumptions
    let res = s.solver.solve_limited(&assumptions);

    mem::forget(s);
    lbool_to_int(res)
}

#[no_mangle]
pub extern "C" fn ipasir_val(ptr: *mut c_void, lit: c_int) -> c_int {
    let mut s = get_solver(ptr);

    let var = s.get_var(lit.abs() as usize);
    let val = {
        let v = s.solver.model[var.idx() as usize];
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
    return 0 // FIXME
}

#[no_mangle]
pub extern "C" fn ipasir_set_terminate(
    ptr: *mut c_void,
    state: *mut c_void,
    terminate: extern "C" fn(*mut c_void) -> c_int
) {
    // FIXME
}

#[no_mangle]
pub extern "C" fn ipasir_set_learn(
    ptr: *mut c_void,
    state: *mut c_void,
    max_len: c_int,
    learn: extern "C" fn(*mut c_void, *mut c_int) -> c_void
) {
    // FIXME
}
