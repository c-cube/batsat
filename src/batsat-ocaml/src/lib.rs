extern crate batsat;
#[macro_use]
extern crate ocaml;

#[link(name="batsat")]

use ocaml::{Value,value};

use std::mem;
use std::ops;

use batsat::{Solver as InnerSolver,Var,Lit,lbool,SolverInterface};

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
    fn get_lit(&mut self, lit: i32) -> Lit {
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
fn get_solver(v: Value) -> Box<Solver> {
    let ptr : *mut Solver = v.custom_ptr_val_mut();
    unsafe{ Box::from_raw(ptr as *mut Solver) }
}

// finalizer for values
extern "C" fn batsat_finalizer(v: ocaml::core::Value) {
    let v = Value::new(v);
    let s = get_solver(v);
    mem::drop(s); // delete!
}

caml!(ml_batsat_new, |_params|, <res>, {
    let solver = Box::new(Solver::new());
    let ptr = Box::into_raw(solver) as *mut Solver;
    res = Value::alloc_custom(ptr, batsat_finalizer);
} -> res);

caml!(ml_batsat_delete, |param|, <res>, {
    // FIXME:
    // already cleaned?
    // if (*((solver**)(Data_custom_val(block)))==0) {
    //     goto exit;
    // }
    let s = get_solver(param);
    mem::drop(s);
    res = value::UNIT;
} -> res);

caml!(ml_batsat_simplify, |ptr|, <res>, {
    let mut solver = get_solver(ptr);
    let r = solver.simplify().into();
    mem::forget(solver);
    res = Value::bool(r);
} -> res);

/// Add literal, or add clause if the lit is 0
caml!(ml_batsat_addlit, |ptr, lit|, <res>, {
    let mut solver = get_solver(ptr);
    let lit = lit.i32_val();

    let mut r = true;
    if lit == 0 {
        // push current clause into vector `clauses`, reset it
        //println!("add-lit {:?}", 0);
        let (solver, cur, _) = solver.decompose();
        r = solver.add_clause_reuse(cur);
        cur.clear();
    } else {
        // push literal into clause
        let lit = solver.get_lit(lit);
        //println!("add-lit {:?}", lit);
        solver.cur_clause.push(lit);
    }

    mem::forget(solver);
    res = Value::bool(r);
} -> res);

/// Add assumption into the solver
caml!(ml_batsat_assume, |ptr, lit|, <res>, {
    let mut solver = get_solver(ptr);
    let lit = lit.i32_val();

    assert!(lit != 0);
    let lit = solver.get_lit(lit);
    solver.assumptions.push(lit);

    mem::forget(solver);
    res = value::UNIT;
} -> res);

caml!(ml_batsat_solve, |ptr|, <res>, {
    let mut solver = get_solver(ptr);

    let r = {
        let (s, _, assumptions) = solver.decompose();
        let lb = s.solve_limited(&assumptions);
        assumptions.clear(); // reset assumptions
        assert_ne!(lb, lbool::UNDEF); // can't express that in a bool
        lb != lbool::FALSE
    };
    //println!("res: {:?}, model: {:?}", r, solver.get_model());
    mem::forget(solver);
    res = Value::bool(r);
} -> res);

caml!(ml_batsat_value, |ptr, lit|, <res>, {
    let mut solver = get_solver(ptr);
    let lit = lit.i32_val();
    let r =
        if lit.abs() >= solver.num_vars() as i32 {
            lbool::UNDEF
        } else {
            let lit = solver.get_lit(lit as i32);
            solver.s.value_lit(lit)
        };
    //println!("val for {:?}: {:?}", lit, r);
    mem::forget(solver);
    res = Value::i32(r.to_u8() as i32);
} -> res);

caml!(ml_batsat_check_assumption, |ptr, lit|, <res>, {
    let mut solver = get_solver(ptr);
    let lit = lit.i32_val();

    // check unsat-core
    let lit = solver.get_lit(lit);
    let r = solver.s.unsat_core_contains_var(lit.var());

    mem::forget(solver);
    res = Value::bool(r);
} -> res);

caml!(ml_batsat_set_verbose, |ptr, level|, <res>, {
    let mut solver = get_solver(ptr);
    let level = level.i32_val();

    solver.s.set_verbosity(level);

    mem::forget(solver);
    res = value::UNIT;
} -> res);

caml!(ml_batsat_nvars, |ptr|, <res>, {
    let solver = get_solver(ptr);
    let r = solver.s.num_vars() as i64;
    mem::forget(solver);
    res = Value::i64(r);
} -> res);

caml!(ml_batsat_nclauses, |ptr|, <res>, {
    let solver = get_solver(ptr);
    let r = solver.s.num_clauses();
    mem::forget(solver);
    res = Value::i64(r as i64);
} -> res);

caml!(ml_batsat_nconflicts, |ptr|, <res>, {
    let solver = get_solver(ptr);
    let r = solver.s.num_conflicts();
    mem::forget(solver);
    res = Value::i64(r as i64);
} -> res);


