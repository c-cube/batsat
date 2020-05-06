/*****************************************************************************************[core.rs]
Copyright (c) 2003-2006, Niklas Een, Niklas Sorensson (MiniSat)
Copyright (c) 2007-2010, Niklas Sorensson (MiniSat)
Copyright (c) 2018-2018, Masaki Hara

Permission is hereby granted, free of charge, to any person obtaining a copy of this software and
associated documentation files (the "Software"), to deal in the Software without restriction,
including without limitation the rights to use, copy, modify, merge, publish, distribute,
sublicense, and/or sell copies of the Software, and to permit persons to whom the Software is
furnished to do so, subject to the following conditions:

The above copyright notice and this permission notice shall be included in all copies or
substantial portions of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR IMPLIED, INCLUDING BUT
NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND
NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM,
DAMAGES OR OTHER LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT
OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.
**************************************************************************************************/

use {
    crate::callbacks::{Callbacks, ProgressStatus},
    crate::clause::{
        self, lbool, CRef, ClauseAllocator, ClauseRef, DeletePred, LSet, Lit, OccLists,
        OccListsData, VMap, Var,
    },
    crate::interface::SolverInterface,
    crate::intmap::{Comparator, Heap, HeapData},
    crate::theory::Theory,
    std::{
        cmp, f64, fmt, i32, mem,
        sync::atomic::{AtomicBool, Ordering},
    },
};

#[cfg(feature = "logging")]
use crate::clause::display::Print;

/// The main solver structure
///
/// A `Solver` object contains the whole state of the SAT solver, including
/// a clause allocator, literals, clauses, and statistics.
///
/// It is parametrized by `Callbacks`
pub struct Solver<Cb: Callbacks> {
    // Extra results: (read-only member variable)
    /// If problem is satisfiable, this vector contains the model (if any).
    model: Vec<lbool>,
    /// If problem is unsatisfiable (possibly under assumptions),
    /// this vector represent the final conflict clause expressed in the assumptions.
    conflict: LSet,

    cb: Cb, // the callbacks
    asynch_interrupt: AtomicBool,

    /// List of problem clauses.
    clauses: Vec<CRef>,
    /// List of learnt clauses.
    learnts: Vec<CRef>,

    v: SolverV,
    tmp_c_th: Vec<Lit>,     // used for theory conflict
    tmp_c_add_cl: Vec<Lit>, // used for adding clauses during search
}

/// The current assignments.
struct VarState {
    /// A heuristic measurement of the activity of a variable.
    activity: VMap<f64>,
    /// Current assignment for each variable.
    ass: VMap<lbool>,
    /// Stores reason and level for each variable.
    vardata: VMap<VarData>,
    /// Amount to bump next variable with.
    var_inc: f64,
    var_decay: f64,

    /// Assignment stack; stores all assigments made in the order they were made.
    trail: Vec<Lit>,
    /// Separator indices for different decision levels in `trail`.
    trail_lim: Vec<i32>,
}

struct SolverV {
    vars: VarState,

    learntsize_adjust_start_confl: i32,
    learntsize_adjust_inc: f64,
    max_learnts: f64,
    learntsize_adjust_confl: f64,
    learntsize_adjust_cnt: i32,

    remove_satisfied: bool,

    // Statistics: (read-only member variable)
    solves: u64,
    starts: u64,
    decisions: u64,
    rnd_decisions: u64,
    propagations: u64,
    conflicts: u64,
    dec_vars: u64,
    // v.num_clauses: u64,
    // v.num_learnts: u64,
    // v.clauses_literals: u64,
    // v.learnts_literals: u64,
    max_literals: u64,
    tot_literals: u64,

    num_clauses: u64,
    num_learnts: u64,
    clauses_literals: u64,
    learnts_literals: u64,

    // Mode of operation:
    clause_decay: f64,
    random_var_freq: f64,
    random_seed: f64,
    luby_restart: bool,
    /// Controls conflict clause minimization (0=none, 1=basic, 2=deep).
    ccmin_mode: i32,
    /// Controls the level of phase saving (0=none, 1=limited, 2=full).
    phase_saving: i32,
    /// Use random polarities for branching heuristics.
    rnd_pol: bool,
    /// Initialize variable activities with a small random value.
    rnd_init_act: bool,
    /// The fraction of wasted memory allowed before a garbage collection is triggered.
    garbage_frac: f64,
    /// Minimum number to set the learnts limit to.
    min_learnts_lim: i32,

    /// The initial restart limit. (default 100)
    restart_first: i32,
    /// The factor with which the restart limit is multiplied in each restart. (default 1.5)
    restart_inc: f64,
    /// The intitial limit for learnt clauses is a factor of the original clauses. (default 1 / 3)
    learntsize_factor: f64,
    /// The limit for learnt clauses is multiplied with this factor each restart. (default 1.1)
    learntsize_inc: f64,

    // /// A heuristic measurement of the activity of a variable.
    // v.activity: VMap<f64>,
    // /// The current assignments.
    // v.assigns: VMap<lbool>,
    /// The preferred polarity of each variable.
    polarity: VMap<bool>,
    /// The users preferred polarity of each variable.
    user_pol: VMap<lbool>,
    /// Declares if a variable is eligible for selection in the decision heuristic.
    decision: VMap<bool>,
    // /// Stores reason and level for each variable.
    /// `watches[lit]` is a list of constraints watching 'lit' (will go there if literal becomes true).
    watches_data: OccListsData<Lit, Watcher>,
    /// A priority queue of variables ordered with respect to the variable activity.
    order_heap_data: HeapData<Var>,
    /// If `false`, the constraints are already unsatisfiable. No part of the solver state may be used!
    ok: bool,
    /// Amount to bump next clause with.
    cla_inc: f64,
    // /// Amount to bump next variable with.
    // v.var_inc: f64,
    /// Head of queue (as index into the trail -- no more explicit propagation queue in MiniSat).
    qhead: i32,
    /// Number of top-level assignments since last execution of 'simplify()'.
    simp_db_assigns: i32,
    /// Remaining number of propagations that must be made before next execution of 'simplify()'.
    simp_db_props: i64,
    /// Set by `search()`.
    progress_estimate: f64,
    /// Indicates whether possibly inefficient linear scan for satisfied clauses should be performed in 'simplify'.

    /// Next variable to be created.
    next_var: Var,
    ca: ClauseAllocator,

    free_vars: Vec<Var>,

    // /// Assignment stack; stores all assigments made in the order they were made.
    // v.trail: Vec<Lit>,
    // /// Separator indices for different decision levels in 'trail'.
    // v.trail_lim: Vec<i32>,
    /// Current set of assumptions provided to solve by the user.
    assumptions: Vec<Lit>,

    // Temporaries (to reduce allocation overhead). Each variable is prefixed by the method in which it is
    // used, except `seen` wich is used in several places.
    seen: VMap<Seen>,
    minimize_stack: Vec<Lit>,
    analyze_toclear: Vec<Lit>,

    // Resource contraints:
    conflict_budget: i64,
    propagation_budget: i64,

    th_st: TheoryState,
}

/// State used to store theory lemmas, propagations, etc.
struct TheoryState {
    lemma_lits: Vec<Lit>,
    lemma_offsets: Vec<(usize, usize)>, // slices in `lemma_lits`
}

impl TheoryState {
    // new state
    fn new() -> Self {
        TheoryState {
            lemma_lits: vec![],
            lemma_offsets: vec![],
        }
    }

    fn clear(&mut self) {
        self.lemma_lits.clear();
        self.lemma_offsets.clear();
    }

    fn push_lemma(&mut self, lits: &[Lit]) {
        let idx = self.lemma_lits.len();
        self.lemma_offsets.push((idx, lits.len()));
        self.lemma_lits.extend_from_slice(lits);
    }

    /// Iterate over the clauses contained in this theory state
    fn iter_lemmas<'a>(&'a mut self) -> impl Iterator<Item = &'a [Lit]> + 'a {
        theory_st::LIter(self, 0)
    }
}

mod theory_st {
    use super::*;

    // state + offset
    pub(super) struct LIter<'a>(pub &'a TheoryState, pub usize);

    impl<'a> Iterator for LIter<'a> {
        type Item = &'a [Lit];
        fn next(&mut self) -> Option<Self::Item> {
            if self.1 >= self.0.lemma_offsets.len() {
                None
            } else {
                let (offset, len) = self.0.lemma_offsets[self.1];
                self.1 += 1;
                let c = &self.0.lemma_lits[offset..offset + len];
                Some(c)
            }
        }
    }
}
///
/// Print the model/proof as DIMACS
pub struct SolverPrintDimacs<'a, Cb: Callbacks + 'a> {
    s: &'a Solver<Cb>,
    model: bool, // model or proof
}

mod dimacs {
    use super::*;

    impl<'a, Cb: Callbacks> fmt::Display for SolverPrintDimacs<'a, Cb> {
        fn fmt(&self, out: &mut fmt::Formatter) -> fmt::Result {
            if self.model {
                write!(out, "v ")?;
                for (i, &val) in self.s.model.iter().enumerate() {
                    if val == lbool::TRUE && i > 0 {
                        write!(out, "{} ", i + 1)?
                    } else if val == lbool::FALSE && i > 0 {
                        write!(out, "-{} ", i + 1)?
                    }
                }
                writeln!(out, "0")
            } else {
                Ok(())
            }
        }
    }
}

// public API
impl<Cb: Callbacks> SolverInterface for Solver<Cb> {
    fn new_var(&mut self, upol: lbool, dvar: bool) -> Var {
        self.v.new_var(upol, dvar)
    }

    fn new_var_default(&mut self) -> Var {
        self.new_var(lbool::UNDEF, true)
    }

    fn var_of_int(&mut self, v_idx: u32) -> Var {
        while v_idx >= self.num_vars() {
            self.new_var_default();
        }
        let var = Var::from_idx(v_idx);
        debug_assert_eq!(var.idx(), v_idx);
        var
    }

    // in the API, we can only add clauses at level 0
    fn add_clause_reuse(&mut self, clause: &mut Vec<Lit>) -> bool {
        debug!("add toplevel clause {:?}", clause);
        debug_assert_eq!(
            self.v.decision_level(),
            0,
            "add clause at non-zero decision level"
        );
        clause.sort_unstable();
        self.add_clause_(clause)
    }

    fn solve_limited_th<Th: Theory>(&mut self, th: &mut Th, assumps: &[Lit]) -> lbool {
        self.asynch_interrupt.store(false, Ordering::SeqCst);
        self.v.assumptions.clear();
        self.v.assumptions.extend_from_slice(assumps);
        self.solve_internal(th)
    }

    #[inline(always)]
    fn simplify_th<Th: Theory>(&mut self, th: &mut Th) -> bool {
        self.simplify_internal(th)
    }

    fn value_var(&self, v: Var) -> lbool {
        self.model
            .get(v.idx() as usize)
            .map_or(lbool::UNDEF, |&v| v)
    }
    fn value_lit(&self, v: Lit) -> lbool {
        self.value_var(v.var()) ^ !v.sign()
    }
    fn get_model(&self) -> &[lbool] {
        &self.model
    }
    fn is_ok(&self) -> bool {
        self.v.ok
    }

    fn num_vars(&self) -> u32 {
        self.v.num_vars()
    }
    fn num_clauses(&self) -> u64 {
        self.v.num_clauses()
    }
    fn num_conflicts(&self) -> u64 {
        self.v.num_conflicts()
    }
    fn num_propagations(&self) -> u64 {
        self.v.num_props()
    }
    fn num_decisions(&self) -> u64 {
        self.v.decisions
    }
    fn num_restarts(&self) -> u64 {
        self.v.starts
    }

    fn value_lvl_0(&self, lit: Lit) -> lbool {
        let mut res = self.v.value_lit(lit);
        if self.v.level(lit.var()) != 0 {
            res = lbool::UNDEF;
        }
        res
    }

    fn print_stats(&self) {
        println!("c restarts              : {}", self.v.starts);
        println!("c conflicts             : {:<12}", self.v.conflicts);
        println!(
            "c decisions             : {:<12}   ({:4.2} % random)",
            self.v.decisions,
            self.v.rnd_decisions as f32 * 100.0 / self.v.decisions as f32
        );
        println!("c propagations          : {:<12}", self.v.propagations);
        println!(
            "c conflict literals     : {:<12}   ({:4.2} % deleted)",
            self.v.tot_literals,
            (self.v.max_literals - self.v.tot_literals) as f64 * 100.0 / self.v.max_literals as f64
        );
    }

    fn unsat_core(&self) -> &[Lit] {
        self.conflict.as_slice()
    }

    fn unsat_core_contains_lit(&self, lit: Lit) -> bool {
        self.conflict.has(lit)
    }

    fn unsat_core_contains_var(&self, v: Var) -> bool {
        let lit = Lit::new(v, true);
        self.unsat_core_contains_lit(lit) || self.unsat_core_contains_lit(!lit)
    }

    fn proved_at_lvl_0(&self) -> &[Lit] {
        self.v.vars.proved_at_lvl_0()
    }
}

impl<Cb: Callbacks + Default> Default for Solver<Cb> {
    fn default() -> Self {
        Solver::new(SolverOpts::default(), Default::default())
    }
}

impl<Cb: Callbacks> Solver<Cb> {
    /// Create a new solver with the given options and default callbacks
    pub fn new(opts: SolverOpts, cb: Cb) -> Self {
        Solver::new_with(opts, cb)
    }
}

// partial check, or final check?
enum TheoryCall {
    Partial,
    Final,
}

// main algorithm
impl<Cb: Callbacks> Solver<Cb> {
    /// Create a new solver with the given options and callbacks.
    pub fn new_with(opts: SolverOpts, cb: Cb) -> Self {
        assert!(opts.check());
        Self {
            // Parameters (user settable):
            model: vec![],
            conflict: LSet::new(),
            cb,
            clauses: vec![],
            learnts: vec![],
            asynch_interrupt: AtomicBool::new(false),
            v: SolverV::new(&opts),
            tmp_c_th: vec![],
            tmp_c_add_cl: vec![],
        }
    }

    /// Begins a new decision level.
    fn new_decision_level<Th: Theory>(&mut self, th: &mut Th) {
        trace!("new decision level {}", 1 + self.v.decision_level());
        self.v.vars.new_decision_level();
        th.create_level();
        debug_assert_eq!(
            self.v.decision_level() as usize,
            th.n_levels(),
            "same number of levels for theory and trail"
        );
    }

    fn simplify_internal<Th>(&mut self, _: &mut Th) -> bool {
        debug_assert_eq!(self.v.decision_level(), 0);

        if !self.v.ok || self.v.propagate().is_some() {
            self.v.ok = false;
            return false;
        }

        if self.v.num_assigns() as i32 == self.v.simp_db_assigns || self.v.simp_db_props > 0 {
            return true;
        }

        self.remove_satisfied(ClauseSetSelect::Learnt); // Remove satisfied learnt clauses
        if self.v.remove_satisfied {
            self.remove_satisfied(ClauseSetSelect::Original); // remove satisfied normal clauses
        }
        self.check_garbage();
        self.v.rebuild_order_heap();

        self.v.simp_db_assigns = self.v.num_assigns() as i32;
        // (shouldn't depend on stats really, but it will do for now)
        self.v.simp_db_props = (self.v.clauses_literals + self.v.learnts_literals) as i64;

        true
    }

    /// Search for a model the specified number of conflicts.
    ///
    /// Use negative value for `nof_conflicts` indicate infinity.
    ///
    /// # Output:
    ///
    /// - `lbool::TRUE` if a partial assigment that is consistent with respect to the clauseset is found. If
    ///    all variables are decision variables, this means that the clause set is satisfiable.
    /// - `lbool::FALSE` if the clause set is unsatisfiable.
    /// - 'lbool::UNDEF` if the bound on number of conflicts is reached.
    fn search<Th: Theory>(
        &mut self,
        th: &mut Th,
        nof_conflicts: i32,
        tmp_learnt: &mut Vec<Lit>,
    ) -> lbool {
        debug_assert!(self.v.ok);
        let mut conflict_c = 0;
        self.v.starts += 1;

        'main: loop {
            // boolean propagation
            let confl = self.v.propagate();

            if let Some(confl) = confl {
                // conflict analysis
                self.v.conflicts += 1;
                conflict_c += 1;
                if self.v.decision_level() == 0 {
                    return lbool::FALSE;
                }

                let learnt = self
                    .v
                    .analyze(Conflict::BCP(confl), &self.learnts, tmp_learnt, th);
                self.add_learnt_and_backtrack(th, learnt, clause::Kind::Learnt);

                self.v.vars.var_decay_activity();
                self.v.cla_decay_activity();

                self.v.learntsize_adjust_cnt -= 1;
                if self.v.learntsize_adjust_cnt == 0 {
                    self.v.learntsize_adjust_confl *= self.v.learntsize_adjust_inc;
                    self.v.learntsize_adjust_cnt = self.v.learntsize_adjust_confl as i32;
                    self.v.max_learnts *= self.v.learntsize_inc;

                    let trail_lim_head = self
                        .v
                        .vars
                        .trail_lim
                        .first()
                        .cloned()
                        .unwrap_or(self.v.vars.trail.len() as i32);
                    let v = &self.v;
                    self.cb.on_progress(|| ProgressStatus {
                        conflicts: v.conflicts as i32,
                        dec_vars: v.dec_vars as i32 - trail_lim_head,
                        n_clauses: v.num_clauses(),
                        n_clause_lits: v.clauses_literals as i32,
                        max_learnt: v.max_learnts as i32,
                        n_learnt: v.num_learnts(),
                        n_learnt_lits: v.learnts_literals as f64 / v.num_learnts as f64,
                        progress_estimate: v.progress_estimate() * 100.0,
                    });
                }
            } else {
                // no boolean conflict
                if (nof_conflicts >= 0 && conflict_c >= nof_conflicts) || !self.within_budget() {
                    // Reached bound on number of conflicts:
                    self.v.progress_estimate = self.v.progress_estimate();
                    self.cancel_until(th, 0);
                    return lbool::UNDEF;
                }

                // Simplify the set of problem clauses:
                if self.v.decision_level() == 0 && !self.simplify_th(th) {
                    return lbool::FALSE;
                }

                if self.learnts.len() as f64 - self.v.num_assigns() as f64 >= self.v.max_learnts {
                    // Reduce the set of learnt clauses:
                    self.reduce_db();
                }

                // do a partial theory check
                {
                    let th_res = self.call_theory(th, TheoryCall::Partial, tmp_learnt);

                    if th_res == lbool::UNDEF {
                        // some theory propagations, do not decide yet
                        continue 'main;
                    } else if th_res == lbool::FALSE {
                        // conflict, we backtracked and propagated a SAT literal
                        self.v.conflicts += 1;
                        conflict_c += 1;
                        continue 'main;
                    }
                }

                // select the next decision (using assumptions, or variable heap)
                let mut next = Lit::UNDEF;
                while (self.v.decision_level() as usize) < self.v.assumptions.len() {
                    // Perform user provided assumption:
                    let p = self.v.assumptions[self.v.decision_level() as usize];
                    if self.v.value_lit(p) == lbool::TRUE {
                        // Dummy decision level, since `p` is true already:
                        self.new_decision_level(th);
                    } else if self.v.value_lit(p) == lbool::FALSE {
                        // conflict at level 0 because of `p`, unsat
                        let mut conflict = mem::replace(&mut self.conflict, LSet::new());
                        self.v.analyze_final(th, !p, &mut conflict);
                        self.cb.on_new_clause(&conflict, clause::Kind::Learnt);
                        self.conflict = conflict;
                        return lbool::FALSE;
                    } else {
                        next = p;
                        break;
                    }
                }

                if next == Lit::UNDEF {
                    // new variable decision:
                    next = self.v.pick_branch_lit();

                    if next == Lit::UNDEF {
                        // no decision? time for a theory final-check
                        let th_res = self.call_theory(th, TheoryCall::Final, tmp_learnt);

                        if th_res == lbool::TRUE {
                            // Model found and validated by the theory
                            return lbool::TRUE;
                        } else if th_res == lbool::UNDEF {
                            // some propagations in final-check
                            continue 'main;
                        } else {
                            assert_eq!(th_res, lbool::FALSE);
                            // conflict, we backtracked and propagated a SAT literal
                            self.v.conflicts += 1;
                            conflict_c += 1;
                            continue 'main;
                        }
                    } else {
                        // proper decision, keep `next`
                        self.v.decisions += 1;
                    }
                }

                debug_assert_ne!(next, Lit::UNDEF);

                // Increase decision level and enqueue `next`
                // with no justification since it's a decision
                self.new_decision_level(th);
                debug!("pick-next {:?}", next);
                self.v.vars.unchecked_enqueue(next, CRef::UNDEF);
            }
        }
    }

    /// Add a learnt clause and backtrack/propagate as necessary
    fn add_learnt_and_backtrack<Th: Theory>(
        &mut self,
        th: &mut Th,
        learnt: LearntClause,
        k: clause::Kind,
    ) {
        self.cb.on_new_clause(&learnt.clause, k);
        self.cancel_until(th, learnt.backtrack_lvl as u32);

        // propagate the only lit of `learnt_clause` that isn't false
        if learnt.clause.len() == 1 {
            // directly propagate the unit clause at level 0
            self.v.vars.unchecked_enqueue(learnt.clause[0], CRef::UNDEF);
        } else if learnt.clause.len() == 0 {
            self.v.ok = false;
        } else {
            // propagate the lit, justified by `cr`
            let cr = self.v.ca.alloc_with_learnt(&learnt.clause, true);
            self.learnts.push(cr);
            self.v.attach_clause(cr);
            self.v.cla_bump_activity(&self.learnts, cr);
            self.v.vars.unchecked_enqueue(learnt.clause[0], cr);
        }

        if learnt.add_orig {
            debug!("add original lemma {:?}", learnt.orig_lits);
            // add theory lemma too, it was deemed costly to produce
            let mut c = vec![];
            mem::swap(&mut c, &mut self.tmp_c_add_cl);
            c.clear();
            c.extend_from_slice(learnt.orig_lits);
            self.add_clause_during_search(th, &mut c);
            mem::swap(&mut c, &mut self.tmp_c_add_cl);
        }
    }

    /// Call theory to check the current (possibly partial) model
    ///
    /// Returns `UNDEF` if the theory propagated something, `TRUE` if
    /// the theory accepted the model without propagations, and `FALSE` if
    /// the theory rejected the model.
    fn call_theory<Th: Theory>(
        &mut self,
        th: &mut Th,
        k: TheoryCall,
        tmp_learnt: &mut Vec<Lit>,
    ) -> lbool {
        let mut th_arg = {
            let confl_cl = &mut self.tmp_c_th;
            confl_cl.clear();
            TheoryArg {
                v: &mut self.v,
                lits: confl_cl,
                has_propagated: false,
                conflict: TheoryConflict::Nil,
            }
        };
        // call theory
        match k {
            TheoryCall::Partial => th.partial_check(&mut th_arg),
            TheoryCall::Final => th.final_check(&mut th_arg),
        }
        if let TheoryConflict::Clause { costly } = th_arg.conflict {
            // borrow magic
            let mut local_confl_cl = vec![];
            mem::swap(&mut local_confl_cl, th_arg.lits);
            drop(th_arg);

            debug!("theory conflict {:?} (costly: {})", local_confl_cl, costly);
            self.v.sort_clause_lits(&mut local_confl_cl); // as if it were a normal clause
            local_confl_cl.dedup();
            let learnt = {
                let r = Conflict::ThLemma {
                    lits: &local_confl_cl,
                    add: costly,
                };
                self.v.analyze(r, &self.learnts, tmp_learnt, th)
            };
            self.add_learnt_and_backtrack(th, learnt, clause::Kind::Theory);
            mem::swap(&mut local_confl_cl, &mut self.tmp_c_th); // re-use lits
            lbool::FALSE
        } else if let TheoryConflict::Prop(p) = th_arg.conflict {
            // conflict: propagation of a lit known to be false
            debug!("inconsistent theory propagation {:?}", p);
            let learnt = {
                let r = Conflict::ThProp(p);
                self.v.analyze(r, &self.learnts, tmp_learnt, th)
            };
            self.add_learnt_and_backtrack(th, learnt, clause::Kind::Theory);
            lbool::FALSE
        } else {
            debug_assert!(match th_arg.conflict {
                TheoryConflict::Nil => true,
                _ => false,
            });

            let mut has_propagated = th_arg.has_propagated;

            let mut lemmas = vec![];
            for c in self.v.th_st.iter_lemmas() {
                trace!("add theory lemma {}", c.pp_dimacs());
                has_propagated = true;
                lemmas.push(c.into());
            }
            // now add lemmas
            for mut c in lemmas {
                self.add_clause_during_search(th, &mut c);
            }

            if has_propagated {
                self.v.th_st.clear(); // be sure to cleanup
                lbool::UNDEF
            } else {
                lbool::TRUE // Model validated without further work needed
            }
        }
    }

    /// Main solve method (assumptions given in `self.assumptions`).
    fn solve_internal<Th: Theory>(&mut self, th: &mut Th) -> lbool {
        assert!(self.v.decision_level() == 0);
        self.model.clear();
        self.conflict.clear();
        if !self.v.ok {
            return lbool::FALSE;
        }

        self.v.solves += 1;
        let mut tmp_learnt: Vec<Lit> = vec![];

        self.v.max_learnts = self.num_clauses() as f64 * self.v.learntsize_factor;
        if self.v.max_learnts < self.v.min_learnts_lim as f64 {
            self.v.max_learnts = self.v.min_learnts_lim as f64;
        }

        self.v.learntsize_adjust_confl = self.v.learntsize_adjust_start_confl as f64;
        self.v.learntsize_adjust_cnt = self.v.learntsize_adjust_confl as i32;
        let mut status;

        info!("search.start");
        self.cb.on_start();

        // Search:
        let mut curr_restarts: i32 = 0;
        loop {
            let rest_base = if self.v.luby_restart {
                utils::luby(self.v.restart_inc, curr_restarts)
            } else {
                f64::powi(self.v.restart_inc, curr_restarts)
            };
            let nof_clauses = (rest_base * self.v.restart_first as f64) as i32;
            status = self.search(th, nof_clauses, &mut tmp_learnt);
            if !self.within_budget() {
                break;
            }

            if status != lbool::UNDEF {
                break;
            } else {
                info!("search.restart({})", curr_restarts);
                curr_restarts += 1;
                self.cb.on_restart();
            }
        }

        self.cb.on_result(status);

        if status == lbool::TRUE {
            // Extend & copy model:
            let num_vars = self.num_vars();
            self.model.resize(num_vars as usize, lbool::UNDEF);
            for i in 0..num_vars {
                self.model[i as usize] = self.v.value(Var::from_idx(i));
            }
        } else if status == lbool::FALSE && self.conflict.len() == 0 {
            // NOTE: we may return `false` without an empty conflict in case we had assumptions. In
            // this case `self.conflict` contains the unsat-core but adding new clauses might
            // succeed in the absence of these assumptions.
            self.v.ok = false;
        }

        self.cancel_until(th, 0);
        debug!("res: {:?}", status);
        trace!(
            "proved at lvl 0: {:?}",
            self.v.vars.iter_trail().collect::<Vec<_>>()
        );
        status
    }

    /// Remove half of the learnt clauses, minus the clauses locked by the current assignment. Locked
    /// clauses are clauses that are reason to some assignment. Binary clauses are never removed.
    fn reduce_db(&mut self) {
        let extra_lim = self.v.cla_inc / self.learnts.len() as f64; // Remove any clause below this activity

        debug!("reduce_db.start");

        {
            let ca = &self.v.ca;
            self.learnts.sort_unstable_by(|&x, &y| {
                let x = ca.get_ref(x);
                let y = ca.get_ref(y);
                debug_assert!(x.learnt());
                debug_assert!(y.learnt());
                Ord::cmp(&(x.size() <= 2), &(y.size() <= 2)).then(
                    PartialOrd::partial_cmp(&x.activity(), &y.activity()).expect("NaN activity"),
                )
            });
        }
        // Don't delete binary or locked clauses. From the rest, delete clauses from the first half
        // and clauses with activity smaller than `extra_lim`:
        let mut j = 0;
        for i in 0..self.learnts.len() {
            let cr = self.learnts[i];
            let cond = {
                let c = self.v.ca.get_ref(cr);
                c.size() > 2
                    && !self.v.locked(c)
                    && (i < self.learnts.len() / 2 || (c.activity() as f64) < extra_lim)
            };
            if cond {
                self.v.remove_clause(cr);
                self.cb.on_delete_clause(self.v.ca.get_ref(cr).lits());
            } else {
                self.learnts[j] = cr;
                j += 1;
            }
        }

        // self.learnts.resize_default(j);
        let _deleted = self.learnts.len() - j;
        self.learnts.resize(j, CRef::UNDEF);

        debug!("reduce_db.done (deleted {})", _deleted);

        self.check_garbage();
    }

    /// Shrink the given set to contain only non-satisfied clauses.
    fn remove_satisfied(&mut self, which: ClauseSetSelect) {
        assert_eq!(self.v.decision_level(), 0);
        let cs: &mut Vec<CRef> = match which {
            ClauseSetSelect::Learnt => &mut self.learnts,
            ClauseSetSelect::Original => &mut self.clauses,
        };
        let self_v = &mut self.v;
        cs.retain(|&cr| {
            let satisfied = self_v.satisfied(self_v.ca.get_ref(cr));
            if satisfied {
                self_v.remove_clause(cr);
                debug!("remove satisfied clause {:?}", self_v.ca.get_ref(cr).lits());
            // we should not need to tell the proof checker to remove the clause
            } else {
                let amount_shaved = {
                    let mut c = self_v.ca.get_mut(cr);
                    // Trim clause (but keep the 2 first lits as they are watching):
                    debug_assert_eq!(self_v.vars.value_lit(c[0]), lbool::UNDEF);
                    debug_assert_eq!(self_v.vars.value_lit(c[1]), lbool::UNDEF);
                    let mut k = 2;
                    let orig_size = c.size();
                    let mut end = c.size();
                    while k < end {
                        if self_v.vars.value_lit(c[k]) == lbool::FALSE {
                            // this lit is false at level 0, remove it from `c`
                            debug_assert!(self_v.vars.level(c[k].var()) == 0);
                            end -= 1;
                            c[k] = c[end];
                        } else {
                            k += 1;
                        }
                    }
                    c.shrink(end);
                    orig_size - end
                };
                // It was not in MiniSAT, but it is needed for correct wasted calculation.
                self_v.ca.free_amount(amount_shaved);
            }
            !satisfied
        });
    }

    /// Revert to the state at given level (keeping all assignment at `level` but not beyond).
    fn cancel_until<Th: Theory>(&mut self, th: &mut Th, level: u32) {
        let dl = self.v.decision_level();
        if dl > level {
            let n_th_levels = (dl - level) as usize;
            trace!(
                "solver.cancel-until {} (pop {} theory levels)",
                level,
                n_th_levels
            );
            self.v.cancel_until(level);
            th.pop_levels(n_th_levels); // backtrack theory state
        }
    }

    /// Garbage collect the clause allocator by moving alive clauses into
    /// another allocator.
    fn garbage_collect(&mut self) {
        // Initialize the next region to a size corresponding to the estimated utilization degree. This
        // is not precise but should avoid some unnecessary reallocations for the new region:
        let mut to = ClauseAllocator::with_start_cap(self.v.ca.len() - self.v.ca.wasted());

        self.v
            .reloc_all(&mut self.learnts, &mut self.clauses, &mut to);

        self.cb.on_gc(
            (self.v.ca.len() * ClauseAllocator::UNIT_SIZE) as usize,
            (to.len() * ClauseAllocator::UNIT_SIZE) as usize,
        );
        self.v.ca = to;
    }

    /// Check whether the space wasted by dead clauses in the clause allocator exceeds
    /// the threshold
    fn check_garbage(&mut self) {
        if self.v.ca.wasted() as f64 > self.v.ca.len() as f64 * self.v.garbage_frac {
            self.garbage_collect();
        }
    }

    /// Temporary access to the callbacks
    pub fn cb_mut(&mut self) -> &mut Cb {
        &mut self.cb
    }

    /// Temporary access to the callbacks
    pub fn cb(&self) -> &Cb {
        &self.cb
    }

    pub fn dimacs_model(&self) -> SolverPrintDimacs<Cb> {
        SolverPrintDimacs {
            s: self,
            model: true,
        }
    }

    /// Interrupt search asynchronously
    pub fn interrupt_async(&self) {
        self.asynch_interrupt.store(true, Ordering::Relaxed);
    }

    fn has_been_interrupted(&self) -> bool {
        self.asynch_interrupt.load(Ordering::Relaxed)
    }

    fn within_budget(&self) -> bool {
        !self.has_been_interrupted()
            && (self.v.conflict_budget < 0 || self.v.conflicts < self.v.conflict_budget as u64)
            && (self.v.propagation_budget < 0
                || self.v.propagations < self.v.propagation_budget as u64)
            && !self.cb.stop()
    }

    /// Add clause.
    ///
    /// Precondition: `clause` is sorted for some ordering on `Lit`
    fn add_clause_(&mut self, clause: &mut Vec<Lit>) -> bool {
        if !self.v.ok {
            return false;
        }

        let mut last_lit = Lit::UNDEF;
        let mut j = 0;
        // remove duplicates, true literals, etc.
        for i in 0..clause.len() {
            let lit_i = clause[i];
            let value = self.v.value_lit(lit_i);
            let lvl = self.v.level_lit(lit_i);
            if (value == lbool::TRUE && lvl == 0) || lit_i == !last_lit {
                return true; // tauto or satisfied already at level 0
            } else if !(value == lbool::FALSE && lvl == 0) && lit_i != last_lit {
                // not a duplicate
                last_lit = lit_i;
                clause[j] = lit_i;
                j += 1;
            }
        }

        clause.resize(j, Lit::UNDEF);
        if clause.len() == 0 {
            self.v.ok = false;
            return false;
        } else if clause.len() == 1 {
            self.v.vars.unchecked_enqueue(clause[0], CRef::UNDEF);
        } else {
            let cr = self.v.ca.alloc_with_learnt(&clause, false);
            self.clauses.push(cr);
            self.v.attach_clause(cr);
        }

        true
    }

    /// Add clause during search
    fn add_clause_during_search<Th: Theory>(&mut self, th: &mut Th, clause: &mut Vec<Lit>) -> bool {
        debug!("add internal clause {:?}", clause);
        if !self.v.ok {
            return false;
        }
        if clause.len() == 1 {
            self.cancel_until(th, 0); // only at level 0
        }

        self.v.sort_clause_lits(clause);
        self.add_clause_(clause)
    }
}

/// Theory-triggered conflict.
enum TheoryConflict {
    Nil,
    Clause { costly: bool },
    Prop(Lit),
}

/// The temporary theory argument, passed to the theory.
///
/// This is where the theory can perform actions such as adding clauses.
pub struct TheoryArg<'a> {
    v: &'a mut SolverV,
    lits: &'a mut Vec<Lit>,
    has_propagated: bool,
    conflict: TheoryConflict,
}

/// Temporary representation of a learnt clause, produced in `analyze`.
struct LearntClause<'a> {
    orig_lits: &'a [Lit], // original clause
    add_orig: bool,       // should we also add `orig_lits`?
    clause: &'a [Lit],    // the clause
    backtrack_lvl: i32,   // where to backtrack?
}

#[derive(Clone, Copy, Debug)]
enum Conflict<'a> {
    BCP(CRef), // boolean propagation conflict
    ThLemma { lits: &'a [Lit], add: bool },
    ThProp(Lit), // literal was propagated, but is false
}

#[derive(Clone, Copy, Debug)]
enum ResolveWith<'a> {
    Init(Conflict<'a>), // initial conflict
    Resolve(Lit, CRef), // propagation of lit because of clause
}

impl SolverV {
    #[inline(always)]
    pub fn num_assigns(&self) -> u32 {
        self.vars.num_assigns()
    }

    #[inline(always)]
    fn num_vars(&self) -> u32 {
        self.next_var.idx()
    }
    fn num_clauses(&self) -> u64 {
        self.num_clauses
    }
    fn num_conflicts(&self) -> u64 {
        self.conflicts
    }
    fn num_props(&self) -> u64 {
        self.propagations
    }
    fn num_learnts(&self) -> u64 {
        self.num_learnts
    }

    #[inline(always)]
    pub fn level(&self, x: Var) -> i32 {
        self.vars.level(x)
    }

    #[inline(always)]
    pub fn level_lit(&self, x: Lit) -> i32 {
        self.level(x.var())
    }

    #[inline(always)]
    pub fn value(&self, x: Var) -> lbool {
        self.vars.value(x)
    }

    #[inline(always)]
    pub fn value_lit(&self, x: Lit) -> lbool {
        self.vars.value_lit(x)
    }

    fn order_heap(&mut self) -> Heap<Var, VarOrder> {
        self.order_heap_data.promote(VarOrder {
            activity: &self.vars.activity,
        })
    }

    fn set_decision_var(&mut self, v: Var, b: bool) {
        if b && !self.decision[v] {
            self.dec_vars += 1;
        } else if !b && self.decision[v] {
            self.dec_vars -= 1;
        }
        self.decision[v] = b;
        self.insert_var_order(v);
    }

    fn insert_var_order(&mut self, x: Var) {
        if !self.order_heap().in_heap(x) && self.decision[x] {
            self.order_heap().insert(x);
        }
    }

    fn cla_decay_activity(&mut self) {
        self.cla_inc *= 1.0 / self.clause_decay;
    }

    fn cla_bump_activity(&mut self, learnts: &[CRef], cr: CRef) {
        let new_activity = {
            let mut c = self.ca.get_mut(cr);
            let r = c.activity() + self.cla_inc as f32;
            c.set_activity(r);
            r
        };
        if new_activity > 1e20 {
            // Rescale:
            for &learnt in learnts.iter() {
                let mut c = self.ca.get_mut(learnt);
                let r = c.activity() * 1e-20;
                c.set_activity(r);
            }
            self.cla_inc *= 1e-20;
        }
    }

    /// Pick a literal to make a decision with
    fn pick_branch_lit(&mut self) -> Lit {
        let mut next = Var::UNDEF;

        // Random decision:
        if utils::drand(&mut self.random_seed) < self.random_var_freq
            && !self.order_heap().is_empty()
        {
            let idx_tmp =
                utils::irand(&mut self.random_seed, self.order_heap_data.len() as i32) as usize;
            next = self.order_heap_data[idx_tmp];
            if self.value(next) == lbool::UNDEF && self.decision[next] {
                self.rnd_decisions += 1;
            }
        }

        // Activity based decision:
        while next == Var::UNDEF || self.value(next) != lbool::UNDEF || !self.decision[next] {
            let mut order_heap = self.order_heap();
            if order_heap.is_empty() {
                next = Var::UNDEF;
                break;
            } else {
                next = order_heap.remove_min();
            }
        }

        // Choose polarity based on different polarity modes (global or per-variable):
        if next == Var::UNDEF {
            Lit::UNDEF
        } else if self.user_pol[next] != lbool::UNDEF {
            Lit::new(next, self.user_pol[next] == lbool::TRUE)
        } else if self.rnd_pol {
            Lit::new(next, utils::drand(&mut self.random_seed) < 0.5)
        } else {
            Lit::new(next, self.polarity[next])
        }
    }

    fn watches(&mut self) -> OccLists<Lit, Watcher, WatcherDeleted> {
        self.watches_data.promote(WatcherDeleted { ca: &self.ca })
    }

    fn new_var(&mut self, upol: lbool, dvar: bool) -> Var {
        let v = self.free_vars.pop().unwrap_or_else(|| {
            let v = self.next_var;
            self.next_var = Var::from_idx(self.next_var.idx() + 1);
            v
        });
        self.watches().init(Lit::new(v, false));
        self.watches().init(Lit::new(v, true));
        self.vars.ass.insert_default(v, lbool::UNDEF);
        self.vars
            .vardata
            .insert_default(v, VarData::new(CRef::UNDEF, 0));
        if self.rnd_init_act {
            self.vars
                .activity
                .insert_default(v, utils::drand(&mut self.random_seed) * 0.00001);
        } else {
            self.vars.activity.insert_default(v, 0.0);
        }
        self.seen.insert_default(v, Seen::UNDEF);
        self.polarity.insert_default(v, false);
        self.user_pol.insert_default(v, upol);
        self.decision.reserve_default(v);
        let len = self.vars.trail.len();
        if v.idx() as usize > len {
            self.vars.trail.reserve(v.idx() as usize + 1 - len);
        }
        self.set_decision_var(v, dvar);
        v
    }

    /// Analyze conflict and produce a reason clause.
    ///
    /// # Pre-conditions:
    ///
    /// - current decision level must be greater than root level.
    /// - `orig` is false in the current trail
    ///
    /// # Post-conditions:
    ///
    /// - `btlevel` is returned.
    /// - `out_learnt[0]` is the asserting literal at level `btlevel`.
    /// - if `out_learnt.size() > 1` then `out_learnt[1]` has the greatest decision level of the
    ///   rest of literals. There may be others from the same level though.
    fn analyze<'a, Th: Theory>(
        &mut self,
        orig: Conflict<'a>,
        learnts: &[CRef],
        out_learnt: &'a mut Vec<Lit>,
        th: &mut Th,
    ) -> LearntClause<'a> {
        out_learnt.clear();

        debug!("analyze.start {:?}", orig);

        // at what level did the conflict happen?
        let conflict_level = match orig {
            Conflict::BCP(_) | Conflict::ThProp(_) => {
                self.decision_level() as i32 // current level
            }
            Conflict::ThLemma { lits, .. } => {
                // check it's a proper conflict clause
                debug_assert!(lits.iter().all(|&p| self.value_lit(p) == lbool::FALSE));
                debug_assert!(lits.len() >= 1, "theory lemma should have at least 1 lit");

                let lvl = lits
                    .iter()
                    .map(|&lit| self.level_lit(lit))
                    .max()
                    .unwrap_or(0);

                if lits.len() == 1 {
                    // unit clause: learn the clause itself at level 0
                    trace!("analyze: learn unit clause {:?} itself", lits);
                    out_learnt.extend_from_slice(lits);
                    return LearntClause {
                        clause: lits,
                        backtrack_lvl: 0,
                        orig_lits: lits,
                        add_orig: false,
                    };
                } else if lvl == 0 {
                    // all at level 0: empty clause
                    trace!("analyze: conflict level 0, learn empty clause");
                    return LearntClause {
                        clause: &[],
                        backtrack_lvl: 0,
                        orig_lits: lits,
                        add_orig: false,
                    };
                }

                lvl
            }
        };

        let mut cur_clause = ResolveWith::Init(orig);
        let mut path_c = 0;
        #[allow(unused)]
        let mut p = Lit::UNDEF;

        out_learnt.push(Lit::UNDEF); // leave room for the UIP

        let mut index = self.vars.trail.len();

        loop {
            // obtain literals to resolve with, as well as a flag indicating
            // whether they should be true or false in the trail
            let mut lits_are_true = false;
            let lits = match cur_clause {
                ResolveWith::Init(Conflict::ThLemma { lits, .. }) => lits,
                ResolveWith::Init(Conflict::ThProp(lit)) => {
                    // theory propagation, ask the theory to justify `lit` with Γ.
                    // The initial conflict is `Γ => lit`, which is false in current trail.
                    let lits = &mut self.th_st.lemma_lits;
                    lits.clear();
                    lits.push(lit);
                    lits.extend(th.explain_propagation(lit).iter().map(|&a| !a));
                    debug_assert!({
                        let vars = &self.vars;
                        lits.iter().all(|&q| vars.value_lit(q) == lbool::FALSE)
                    });
                    &self.th_st.lemma_lits
                }
                ResolveWith::Init(Conflict::BCP(cr)) => {
                    // bump activity if `cr` is a learnt clause
                    let mut c = self.ca.get_ref(cr);
                    if c.learnt() {
                        self.cla_bump_activity(learnts, cr);
                        c = self.ca.get_ref(cr); // re-borrow
                    }

                    let lits = c.lits();
                    lits
                }
                ResolveWith::Resolve(lit, cr) if cr == CRef::SPECIAL => {
                    // theory propagation, ask the theory to justify `lit`
                    lits_are_true = true;
                    let lits = th.explain_propagation(lit);
                    debug_assert!(lits.iter().all(|&q| self.value_lit(q) == lbool::TRUE));
                    lits
                }
                ResolveWith::Resolve(_lit, cr) if cr == CRef::UNDEF => {
                    // should have `path_c==0`
                    panic!(
                        "analyze: reached a decision literal {:?}, path_c={}",
                        _lit, path_c
                    );
                }
                ResolveWith::Resolve(lit, cr) => {
                    // bump activity if `cr` is a learnt clause
                    let mut c = self.ca.get_ref(cr);
                    if c.learnt() {
                        self.cla_bump_activity(learnts, cr);
                        c = self.ca.get_ref(cr); // re-borrow
                    }

                    let lits = c.lits();

                    // we are resolving the initial conflict against `c`,
                    // which should be the clause which propagated `p`,
                    // so we skip its first literal (`p`) since
                    // it can't appear in the learnt clause
                    debug_assert_eq!(lit.var(), lits[0].var());
                    &lits[1..]
                }
            };
            trace!(
                "analyze.resolve-with {:?} ((p: {:?}, path_c: {}, from {:?})",
                lits,
                p,
                path_c,
                cur_clause
            );

            for &q in lits {
                let q = if lits_are_true { !q } else { q }; // be sure that `q` is false
                let lvl = self.vars.level(q.var());
                assert!(lvl <= conflict_level);
                if !self.seen[q.var()].is_seen() && lvl > 0 {
                    self.vars
                        .var_bump_activity(&mut self.order_heap_data, q.var());
                    self.seen[q.var()] = Seen::SOURCE;
                    if lvl == conflict_level {
                        // at conflict level: need to eliminate this lit by resolution
                        path_c += 1;
                    } else {
                        out_learnt.push(q); // part of the learnt clause
                    }
                } else if self.seen[q.var()] == Seen::REMOVABLE {
                    // the resolution goes back "up" the trail to `q`, which was
                    // resolved again. This is wrong.
                    panic!(
                        "possible cycle in conflict graph between {:?} and {:?}",
                        p, q
                    );
                }
            }
            // Select next literal in the trail to look at:
            while !self.seen[self.vars.trail[index - 1].var()].is_seen() {
                debug_assert_eq!(
                    self.vars.level(self.vars.trail[index - 1].var()),
                    conflict_level
                );
                index -= 1;
            }

            p = self.vars.trail[index - 1];
            index -= 1;
            cur_clause = ResolveWith::Resolve(p, self.vars.reason(p.var()));
            self.seen[p.var()] = Seen::REMOVABLE;
            path_c -= 1;

            if path_c <= 0 {
                break;
            }
        }

        // cleanup literals flagged `REMOVABLE`
        index = self.vars.trail.len() - 1;
        loop {
            let q = self.vars.trail[index];
            if self.seen[q.var()] == Seen::REMOVABLE {
                self.seen[q.var()] = Seen::UNDEF;
            }
            if q == p {
                break;
            }
            // avoid overflow by decreasing index only if we keep looping (#7)
            index -= 1;
        }

        // check that the first literal is a decision lit at conflict_level
        assert_ne!(p, Lit::UNDEF);
        debug_assert!(self.value_lit(p) == lbool::TRUE);
        out_learnt[0] = !p;
        // FIXME debug_assert_eq!(self.vars.reason(p.var()), CRef::UNDEF);

        /* NOTE:
        // invariant on `seen`: all literals of `out_learnt` but the first
        // are marked; nothing else is marked.
        assert!(self.vars.trail.iter().all(|p|
            !self.seen[p.var()].is_seen() ||
            (self.vars.level(p.var()) < conflict_level && out_learnt.iter().any(|q| q.var()==p.var()))
        ));
        assert!(out_learnt[1..].iter().all(|p| self.seen[p.var()].is_seen()));
        assert!({
            let mut c = out_learnt.clone();
            c.sort_unstable();
            c.dedup();
            c.len() == out_learnt.len()
        });
        */

        trace!("analyze-learnt: {:?} (before minimization)", &out_learnt);
        self.max_literals += out_learnt.len() as u64;

        self.minimize_conflict(out_learnt);

        // Find correct backtrack level:
        let btlevel = if out_learnt.len() == 1 {
            0
        } else {
            let mut max_i = 1;
            let mut max_level = self.level(out_learnt[max_i].var());
            // Find the first literal assigned at the next-highest level:
            for i in 2..out_learnt.len() {
                let level = self.level(out_learnt[i].var());
                if level > max_level {
                    max_i = i;
                    max_level = level;
                }
            }
            // Swap-in this literal at index 1:
            out_learnt.swap(max_i, 1);
            self.level_lit(out_learnt[1])
        };

        for &lit in &self.analyze_toclear {
            self.seen[lit.var()] = Seen::UNDEF; // (`seen[]` is now cleared)
        }
        debug_assert!(out_learnt
            .iter()
            .all(|&l| self.value_lit(l) == lbool::FALSE));
        let (orig_lits, add_orig) = match orig {
            Conflict::ThLemma { lits, add } => {
                // add original lemma only if it's not the same as the clause
                let not_eq = lits != out_learnt.as_slice();
                (lits, add && not_eq)
            }
            Conflict::ThProp(_) | Conflict::BCP(_) => (&[][..], false),
        };
        LearntClause {
            orig_lits,
            add_orig,
            backtrack_lvl: btlevel,
            clause: out_learnt,
        }
    }

    /// An abstraction of the level of a variable
    #[inline]
    fn abstract_level(&self, v: Var) -> u32 {
        1 << (self.level(v) & 31)
    }

    fn minimize_conflict(&mut self, out_learnt: &mut Vec<Lit>) {
        // Simplify conflict clause:
        self.analyze_toclear.clear();
        self.analyze_toclear.extend_from_slice(&out_learnt);
        let new_size = if self.ccmin_mode == 2 {
            let mut abstract_levels = 0;
            for a in out_learnt[1..].iter() {
                abstract_levels |= self.abstract_level(a.var())
            }

            let mut j = 1;
            for i in 1..out_learnt.len() {
                let lit = out_learnt[i];
                // can eliminate `lit` only if it's redundant *and* not a decision
                if self.reason(lit.var()) == CRef::UNDEF
                    || !self.lit_redundant(lit, abstract_levels)
                {
                    out_learnt[j] = lit;
                    j += 1;
                }
            }
            j
        } else if self.ccmin_mode == 1 {
            let mut j = 1;
            for i in 1..out_learnt.len() {
                let lit = out_learnt[i];
                let x = lit.var();
                let reason = self.reason(x);

                let mut retain = true;
                if reason == CRef::UNDEF || reason == CRef::SPECIAL {
                    debug_assert!(self.level(x) > 0);
                    retain = true;
                } else {
                    let c = self.ca.get_ref(reason);
                    for k in 1..c.size() {
                        let v = c[k].var();
                        if !self.seen[v].is_seen() && self.level(v) > 0 {
                            retain = true;
                            break;
                        }
                    }
                }
                if retain {
                    out_learnt[j] = lit;
                    j += 1;
                }
            }
            j
        } else {
            out_learnt.len()
        };

        self.tot_literals += new_size as u64;
        debug_assert!(new_size <= out_learnt.len());
        out_learnt.truncate(new_size);
    }

    /// Specialized analysis procedure to express the final conflict in terms of assumptions.
    /// Calculates the (possibly empty) set of assumptions that led to the assignment of `p`, and
    /// stores the result in `out_conflict`.
    fn analyze_final<Th: Theory>(&mut self, th: &mut Th, p: Lit, out_conflict: &mut LSet) {
        out_conflict.clear();
        out_conflict.insert(p);
        debug!("analyze_final lit={:?}", p);

        if self.decision_level() == 0 {
            return; // no assumptions
        }

        self.seen[p.var()] = Seen::SOURCE;

        // FIXME: use a stack here too, to be more robust wrt. theory propagations
        for &lit in self.vars.trail[self.vars.trail_lim[0] as usize..]
            .iter()
            .rev()
        {
            let x = lit.var();
            if self.seen[x].is_seen() {
                let reason = self.reason(x);
                if reason == CRef::UNDEF {
                    debug_assert!(self.level(x) > 0);
                    out_conflict.insert(!lit);
                } else if reason == CRef::SPECIAL {
                    // resolution with propagation reason
                    let lits = th.explain_propagation(lit);
                    for &p in lits {
                        if self.vars.level(p.var()) > 0 {
                            self.seen[p.var()] = Seen::SOURCE;
                        }
                    }
                } else {
                    let c = self.ca.get_mut(reason);
                    for j in 1..c.size() {
                        if self.vars.level(c[j].var()) > 0 {
                            self.seen[c[j].var()] = Seen::SOURCE;
                        }
                    }
                }
                self.seen[x] = Seen::UNDEF;
            }
        }

        self.seen[p.var()] = Seen::UNDEF;
        debug_assert!(self.seen.iter().all(|(_, &s)| s == Seen::UNDEF));
    }

    /// Check if `p` can be removed from a conflict clause `C`.
    ///
    /// It can be removed from `C` if it is propagation-implied
    /// by literals of level 0 exclusively or if `C x p.reason` subsumes `C`.
    fn lit_redundant(&mut self, p: Lit, abstract_levels: u32) -> bool {
        self.minimize_stack.clear();
        self.minimize_stack.push(p);

        let top = self.analyze_toclear.len();

        while self.minimize_stack.len() > 0 {
            let q = *self.minimize_stack.last().unwrap();
            let cr = self.reason(q.var());
            debug_assert_ne!(cr, CRef::UNDEF);
            self.minimize_stack.pop();

            // special case: theory propagation
            if cr == CRef::SPECIAL {
                if self.vars.level(q.var()) == 0 {
                    continue; // level 0, just continue
                } else {
                    // we just bail out here, even though the theory propagation
                    // could be caused by propagations that ultimately
                    // come from level 0
                    // TODO: actually perform resolution here

                    for a in self.analyze_toclear[top..].iter() {
                        self.seen[a.var()] = Seen::UNDEF;
                    }
                    self.analyze_toclear.resize(top, Lit::UNDEF);
                    return false;
                }
            }

            let c = self.ca.get_ref(cr);
            // `q` comes from some propagation with `c`, check if these lits can
            // also be eliminated or are already in the learnt clause
            for &l in c.lits()[1..].iter() {
                // Variable at level 0 or previously removable: just skip
                if self.vars.level(l.var()) == 0 || self.seen[l.var()] == Seen::SOURCE {
                    continue;
                }

                if self.reason(l.var()) != CRef::UNDEF
                    && (self.abstract_level(l.var()) & abstract_levels) != 0
                {
                    // keep this literal.
                    // NOTE: if the level of `l` isn't in `abstract_levels`, it
                    // means it comes from propagations at a decision level
                    // unrelated to the learnt clause, and therefore is
                    // somehow implied by an unrelated decision, so there's no
                    // chance to eliminate `l` via resolutions from the learnt clause.
                    self.seen[l.var()] = Seen::SOURCE;
                    self.minimize_stack.push(l);
                    self.analyze_toclear.push(l);
                } else {
                    // cannot remove `l`, cancel
                    for a in self.analyze_toclear[top..].iter() {
                        self.seen[a.var()] = Seen::UNDEF;
                    }
                    self.analyze_toclear.resize(top, Lit::UNDEF);
                    return false;
                }
            }
        }

        true
    }

    /// Propagates all enqueued facts.
    ///
    /// If a conflict arises, the conflicting clause and literal is returned,
    /// otherwise `None`.
    ///
    /// # Post-conditions:
    ///
    /// - the propagation queue is empty, even if there was a conflict.
    fn propagate(&mut self) -> Option<CRef> {
        let mut confl = None;
        let mut num_props: u32 = 0;

        while (self.qhead as usize) < self.vars.trail.len() {
            // `p` is the next enqueued fact to propagate.
            let p = self.vars.trail[self.qhead as usize];

            // eprintln!("propagating trail[{}] = {:?}", self.qhead, p);
            self.qhead += 1;
            let watches_data_ptr: *mut OccListsData<_, _> = &mut self.watches_data;
            // let ws = self.watches().lookup_mut(p);
            let ws = self
                .watches_data
                .lookup_mut_pred(p, &WatcherDeleted { ca: &self.ca });
            // eprintln!("watcher of {:?} = {:?}", p, ws);
            let mut i: usize = 0;
            let mut j: usize = 0;
            let end: usize = ws.len();
            num_props += 1;
            'clauses: while i < end {
                // Try to avoid inspecting the clause:
                let blocker = ws[i].blocker;
                if self.vars.value_lit(blocker) == lbool::TRUE {
                    ws[j] = ws[i];
                    j += 1;
                    i += 1;
                    continue;
                }

                // Make sure the false literal is data[1]:
                let cr = ws[i].cref;
                let mut c = self.ca.get_mut(cr);
                let false_lit = !p;
                if c[0] == false_lit {
                    c[0] = c[1];
                    c[1] = false_lit;
                }
                debug_assert_eq!(c[1], false_lit);
                i += 1;

                // If 0th watch is true, then clause is already satisfied.
                let first = c[0];
                let w = Watcher::new(cr, first);
                if first != blocker && self.vars.value_lit(first) == lbool::TRUE {
                    ws[j] = w;
                    j += 1;
                    continue;
                }

                // Look for new watch:
                for k in 2..c.size() {
                    if self.vars.value_lit(c[k]) != lbool::FALSE {
                        c[1] = c[k];
                        c[k] = false_lit;

                        // self.watches()[!c[1]].push(w);
                        // safe because `!c[1]!=p`, so watches are not aliased
                        debug_assert_ne!(!c[1], p);
                        unsafe { &mut (*watches_data_ptr)[!c[1]] }.push(w);
                        continue 'clauses;
                    }
                }

                // Did not find watch -- clause is unit under assignment:
                ws[j] = w;
                j += 1;
                if self.vars.value_lit(first) == lbool::FALSE {
                    // eprintln!("propagation: conflict at {:?}", first);
                    confl = Some(cr);
                    self.qhead = self.vars.trail.len() as i32;
                    // Copy the remaining watches:
                    while i < end {
                        ws[j] = ws[i];
                        j += 1;
                        i += 1;
                    }
                } else {
                    // eprintln!("propagation: got {:?}", first);
                    self.vars.unchecked_enqueue(first, cr);
                }
            }
            let dummy = Watcher::DUMMY;
            ws.resize(j, dummy);
        }
        self.propagations += num_props as u64;
        self.simp_db_props -= num_props as i64;

        confl
    }

    fn rebuild_order_heap(&mut self) {
        let mut vs = vec![];
        for v in (0..self.num_vars()).map(Var::from_idx) {
            if self.decision[v] && self.value(v) == lbool::UNDEF {
                vs.push(v);
            }
        }
        self.order_heap().build(&vs);
    }

    /// Sort literals of `clause` so that unassigned literals are first,
    /// followed by literals in decreasing assignment level
    fn sort_clause_lits(&self, clause: &mut [Lit]) {
        // sort clause to put unassigned/high level lits first
        clause.sort_unstable_by(|&lit1, &lit2| {
            let has_val1 = self.value_lit(lit1) != lbool::UNDEF;
            let has_val2 = self.value_lit(lit2) != lbool::UNDEF;

            // unassigned variables come first
            if has_val1 && !has_val2 {
                return cmp::Ordering::Greater;
            }
            if !has_val1 && has_val2 {
                return cmp::Ordering::Less;
            }

            let lvl1 = self.level_lit(lit1);
            let lvl2 = self.level_lit(lit2);
            if lvl1 != lvl2 {
                lvl2.cmp(&lvl1) // higher level come first
            } else {
                lit1.cmp(&lit2) // otherwise default comparison
            }
        });

        // check that the first literal is a proper watch
        debug_assert!(
            self.value_lit(clause[0]) == lbool::UNDEF || {
                let lvl0 = self.level_lit(clause[0]);
                clause[1..].iter().all(|&lit2| self.level_lit(lit2) <= lvl0)
            }
        );
    }

    /// Move to the given clause allocator, where clause indices might differ
    fn reloc_all(
        &mut self,
        learnts: &mut Vec<CRef>,
        clauses: &mut Vec<CRef>,
        to: &mut ClauseAllocator,
    ) {
        macro_rules! is_removed {
            ($ca:expr, $cr:expr) => {
                $ca.get_ref($cr).mark() == 1
            };
        }
        // All watchers:
        self.watches().clean_all();
        for v in (0..self.num_vars()).map(Var::from_idx) {
            for s in 0..2 {
                let p = Lit::new(v, s != 0);
                for watch in &mut self.watches_data[p] {
                    self.ca.reloc(&mut watch.cref, to);
                }
            }
        }

        // All reasons:
        for &lit in &self.vars.trail {
            let v = lit.var();

            // Note: it is not safe to call `locked()` on a relocated clause. This is why we keep
            // `dangling` reasons here. It is safe and does not hurt.
            let reason = self.reason(v);
            if reason != CRef::UNDEF && reason != CRef::SPECIAL {
                let cond = {
                    let c = self.ca.get_ref(reason);
                    c.reloced() || self.locked(c)
                };
                if cond {
                    debug_assert!(!is_removed!(self.ca, reason));
                    self.ca.reloc(&mut self.vars.vardata[v].reason, to);
                }
            }
        }

        // All learnt:
        {
            let mut j = 0;
            for i in 0..learnts.len() {
                let mut cr = learnts[i];
                if !is_removed!(self.ca, cr) {
                    self.ca.reloc(&mut cr, to);
                    learnts[j] = cr;
                    j += 1;
                }
            }
            learnts.resize(j, CRef::UNDEF);
        }

        // All original:
        {
            let mut j = 0;
            for i in 0..clauses.len() {
                let mut cr = clauses[i];
                if !is_removed!(self.ca, cr) {
                    self.ca.reloc(&mut cr, to);
                    clauses[j] = cr;
                    j += 1;
                }
            }
            clauses.resize(j, CRef::UNDEF);
        }
    }

    /// Attach a clause to watcher lists
    fn attach_clause(&mut self, cr: CRef) {
        let (c0, c1, learnt, size) = {
            let c = self.ca.get_ref(cr);
            debug_assert!(c.size() > 1);
            (c[0], c[1], c.learnt(), c.size())
        };
        self.watches()[!c0].push(Watcher::new(cr, c1));
        self.watches()[!c1].push(Watcher::new(cr, c0));
        if learnt {
            self.num_learnts += 1;
            self.learnts_literals += size as u64;
        } else {
            self.num_clauses += 1;
            self.clauses_literals += size as u64;
        }
    }

    /// Revert to the state at given level (keeping all assignment at `level` but not beyond).
    fn cancel_until(&mut self, level: u32) {
        debug_assert!(self.decision_level() > level);
        let trail_lim_last = *self.vars.trail_lim.last().expect("trail_lim is empty") as usize;
        let trail_lim_level = self.vars.trail_lim[level as usize] as usize;
        for c in (trail_lim_level..self.vars.trail.len()).rev() {
            let x = self.vars.trail[c].var();
            self.vars.ass[x] = lbool::UNDEF;
            if self.phase_saving > 1 || (self.phase_saving == 1 && c > trail_lim_last) {
                self.polarity[x] = self.vars.trail[c].sign();
            }
            self.insert_var_order(x);
        }
        self.qhead = trail_lim_level as i32;
        self.vars.trail.resize(trail_lim_level, Lit::UNDEF);
        // eprintln!("decision_level {} -> {}", self.trail_lim.len(), level);
        self.th_st.clear();
        self.vars.trail_lim.resize(level as usize, 0);
    }

    /// Detach a clause from watcher lists.
    ///
    /// param `strict` means we remove the clause from watchers eagerly, instead
    /// of just marking the watchlist as "dirty"
    fn detach_clause(&mut self, cr: CRef, strict: bool) {
        let (c0, c1, csize, clearnt) = {
            let c = self.ca.get_ref(cr);
            (c[0], c[1], c.size(), c.learnt())
        };
        debug_assert!(csize > 1);

        let mut watches = self.watches_data.promote(WatcherDeleted { ca: &self.ca });

        // Strict or lazy detaching:
        if strict {
            // watches[!c0].remove_item(&Watcher::new(cr, c1));
            // watches[!c1].remove_item(&Watcher::new(cr, c0));
            let pos = watches[!c0]
                .iter()
                .position(|x| x == &Watcher::new(cr, c1))
                .expect("Watcher not found");
            watches[!c0].remove(pos);
            let pos = watches[!c1]
                .iter()
                .position(|x| x == &Watcher::new(cr, c0))
                .expect("Watcher not found");
            watches[!c1].remove(pos);
        } else {
            watches.smudge(!c0);
            watches.smudge(!c1);
        }

        if clearnt {
            self.num_learnts -= 1;
            self.learnts_literals -= csize as u64;
        } else {
            self.num_clauses -= 1;
            self.clauses_literals -= csize as u64;
        }
    }

    /// Detach and free a clause.
    fn remove_clause(&mut self, cr: CRef) {
        self.detach_clause(cr, false);
        {
            let c = self.ca.get_ref(cr);
            // Don't leave pointers to free'd memory!
            if self.locked(c) {
                self.vars.vardata[c[0].var()].reason = CRef::UNDEF;
            }
        }
        self.ca.get_mut(cr).set_mark(1); // used in reloc
        self.ca.free(cr);
    }

    pub fn satisfied(&self, c: ClauseRef) -> bool {
        c.iter().any(|&lit| self.value_lit(lit) == lbool::TRUE)
    }

    #[inline(always)]
    pub fn decision_level(&self) -> u32 {
        self.vars.decision_level()
    }

    #[inline(always)]
    fn reason(&self, x: Var) -> CRef {
        self.vars.reason(x)
    }

    /// Returns `true` if a clause is a reason for some implication in the current state.
    fn locked(&self, c: ClauseRef) -> bool {
        let reason = self.reason(c[0].var());
        self.value_lit(c[0]) == lbool::TRUE
            && reason != CRef::UNDEF
            && reason != CRef::SPECIAL
            && self.ca.get_ref(reason) == c
    }
    // inline bool     Solver::locked          (const Clause& c) const { return value(c[0]) == l_True && reason(var(c[0])) != CRef_Undef && ca.lea(reason(var(c[0]))) == &c; }

    fn progress_estimate(&self) -> f64 {
        let mut progress = 0.0;
        let f = 1.0 / self.num_vars() as f64;

        for i in 0..self.decision_level() + 1 {
            let beg: i32 = if i == 0 {
                0
            } else {
                self.vars.trail_lim[i as usize - 1]
            };
            let end: i32 = if i == self.decision_level() {
                self.vars.trail.len() as i32
            } else {
                self.vars.trail_lim[i as usize]
            };
            progress += f64::powi(f, i as i32) * (end - beg) as f64;
        }

        progress / self.num_vars() as f64
    }
    fn new(opts: &SolverOpts) -> Self {
        Self {
            vars: VarState::new(opts),
            num_clauses: 0,
            num_learnts: 0,
            clauses_literals: 0,
            learnts_literals: 0,

            clause_decay: opts.clause_decay,
            random_var_freq: opts.random_var_freq,
            random_seed: opts.random_seed,
            luby_restart: opts.luby_restart,
            ccmin_mode: opts.ccmin_mode,
            phase_saving: opts.phase_saving,
            rnd_pol: false,
            rnd_init_act: opts.rnd_init_act,
            garbage_frac: opts.garbage_frac,
            min_learnts_lim: opts.min_learnts_lim,
            restart_first: opts.restart_first,
            restart_inc: opts.restart_inc,

            // Parameters (experimental):
            learntsize_adjust_start_confl: 100,
            learntsize_adjust_inc: 1.5,

            // Statistics: (formerly in 'SolverStats')
            solves: 0,
            starts: 0,
            decisions: 0,
            rnd_decisions: 0,
            propagations: 0,
            conflicts: 0,
            dec_vars: 0,
            // v.num_clauses: 0,
            // v.num_learnts: 0,
            // v.clauses_literals: 0,
            // v.learnts_literals: 0,
            max_literals: 0,
            tot_literals: 0,

            // Parameters (the rest):
            learntsize_factor: 1.0 / 3.0,
            learntsize_inc: 1.1,

            polarity: VMap::new(),
            user_pol: VMap::new(),
            decision: VMap::new(),
            // v.vardata: VMap::new(),
            watches_data: OccListsData::new(),
            order_heap_data: HeapData::new(),
            ok: true,
            cla_inc: 1.0,
            // v.var_inc: 1.0,
            qhead: 0,
            simp_db_assigns: -1,
            simp_db_props: 0,
            progress_estimate: 0.0,
            remove_satisfied: false, // revert b5464ec81f76db9315dac3276b64614dd59cfe49
            next_var: Var::from_idx(0),

            ca: ClauseAllocator::new(),
            free_vars: vec![],
            assumptions: vec![],

            seen: VMap::new(),
            minimize_stack: vec![],
            analyze_toclear: vec![],
            max_learnts: 0.0,
            learntsize_adjust_confl: 0.0,
            learntsize_adjust_cnt: 0,

            // Resource constraints:
            conflict_budget: -1,
            propagation_budget: -1,

            th_st: TheoryState::new(),
        }
    }
}

impl VarState {
    fn new(opts: &SolverOpts) -> Self {
        Self {
            ass: VMap::new(),
            vardata: VMap::new(),
            activity: VMap::new(),
            var_inc: 1.0,
            var_decay: opts.var_decay,
            trail: vec![],
            trail_lim: vec![],
        }
    }

    #[inline(always)]
    pub fn num_assigns(&self) -> u32 {
        self.trail.len() as u32
    }

    /// Begins a new decision level.
    fn new_decision_level(&mut self) {
        let lvl = self.trail.len() as i32;
        self.trail_lim.push(lvl);
    }

    fn proved_at_lvl_0(&self) -> &[Lit] {
        // find where the end of the level-0 part of the trail is
        let end = self
            .trail_lim
            .get(0)
            .map_or(self.trail.len(), |&x| x as usize);
        &self.trail[..end]
    }

    #[inline(always)]
    pub fn value(&self, x: Var) -> lbool {
        self.ass[x]
    }

    #[inline(always)]
    fn value_lit(&self, x: Lit) -> lbool {
        self.ass[x.var()] ^ !x.sign()
    }

    #[inline(always)]
    fn level(&self, x: Var) -> i32 {
        self.vardata[x].level
    }

    #[inline(always)]
    fn reason(&self, x: Var) -> CRef {
        self.vardata[x].reason
    }

    fn var_decay_activity(&mut self) {
        self.var_inc *= 1.0 / self.var_decay;
    }

    #[inline(always)]
    pub fn decision_level(&self) -> u32 {
        self.trail_lim.len() as u32
    }

    fn unchecked_enqueue(&mut self, p: Lit, from: CRef) {
        debug_assert_eq!(
            self.value_lit(p),
            lbool::UNDEF,
            "lit {:?} should be undef",
            p
        );
        self.ass[p.var()] = lbool::new(p.sign());
        self.vardata[p.var()] = VarData::new(from, self.decision_level() as i32);
        self.trail.push(p);
    }

    /// Increase a variable with the current 'bump' value.
    fn var_bump_activity(&mut self, order_heap_data: &mut HeapData<Var>, v: Var) {
        self.activity[v] += self.var_inc;
        if self.activity[v] > 1e100 {
            // Rescale:
            for (_, x) in self.activity.iter_mut() {
                *x *= 1e-100;
            }
            self.var_inc *= 1e-100;
        }

        // Update order_heap with respect to new activity:
        let mut order_heap = order_heap_data.promote(VarOrder {
            activity: &self.activity,
        });
        if order_heap.in_heap(v) {
            order_heap.decrease(v);
        }
    }

    #[allow(dead_code)]
    fn iter_trail<'a>(&'a self) -> impl Iterator<Item = Lit> + 'a {
        self.trail.iter().map(|l| *l)
    }
}

impl<'a> TheoryArg<'a> {
    #[inline]
    pub fn is_ok(&self) -> bool {
        match self.conflict {
            TheoryConflict::Nil => true,
            TheoryConflict::Prop(_) | TheoryConflict::Clause { .. } => false,
        }
    }

    /// Value of given var in current model.
    #[inline(always)]
    pub fn value(&self, v: Var) -> lbool {
        self.v.vars.value(v)
    }

    /// Current (possibly partial) model.
    #[inline(always)]
    pub fn model(&self) -> &[Lit] {
        &self.v.vars.trail
    }

    /// Allocate a new literal.
    pub fn mk_new_lit(&mut self) -> Lit {
        let v = self.v.new_var(lbool::FALSE, true);
        Lit::new(v, true)
    }

    /// Push a theory lemma into the solver.
    ///
    /// This is useful for lemma-on-demand or theory splitting, but can
    /// be relatively costly.
    ///
    /// NOTE: This is not fully supported yet.
    pub fn add_theory_lemma(&mut self, c: &[Lit]) {
        if self.is_ok() {
            self.v.th_st.push_lemma(c)
        }
    }

    /// Propagate the literal `p`, which is theory-implied by the current trail.
    ///
    /// This will add `p` on the trail. The theory must be ready to
    /// provide an explanation via `Theory::explain_prop(p)` if asked to
    /// during conflict resolution.
    ///
    /// Returns `true` if propagation succeeded (or did nothing), `false`
    /// if the propagation results in an immediate conflict.
    /// If this returns `false`, the theory should avoid doing more work and
    /// return as early as reasonably possible.
    pub fn propagate(&mut self, p: Lit) -> bool {
        if !self.is_ok() {
            return false;
        }
        let v_p = self.v.vars.value_lit(p);
        if v_p == lbool::TRUE {
            true
        } else if v_p == lbool::UNDEF {
            // propagate on the fly
            self.has_propagated = true;
            let cr = CRef::SPECIAL; // indicates a theory propagation
            self.v.vars.unchecked_enqueue(p, cr);
            true
        } else {
            assert_eq!(v_p, lbool::FALSE);
            // conflict
            self.conflict = TheoryConflict::Prop(p);
            false
        }
    }

    /// Add a conflict clause.
    ///
    /// This should be used in the theory when the current partial model
    /// is unsatisfiable. It will force the SAT solver to backtrack.
    /// All propagations added with `propagate` during this session
    /// will be discarded.
    ///
    /// ## Params
    /// - `lits` a clause that is a tautology of the theory (ie a lemma)
    ///     and that is false in the current (partial) model.
    /// - `costly` if true, indicates that the conflict `c` was costly to produce.
    ///     This is a hint for the SAT solver to keep the theory lemma that corresponds
    ///     to `c` along with the actual learnt clause.
    pub fn raise_conflict(&mut self, lits: &[Lit], costly: bool) {
        if lits.len() == 0 {
            panic!("conflicts must have a least one literal")
        }
        if self.is_ok() {
            self.conflict = TheoryConflict::Clause { costly };
            self.lits.clear();
            self.lits.extend_from_slice(lits);
        }
    }
}

#[derive(Debug)]
enum ClauseSetSelect {
    Original,
    Learnt,
}

#[derive(Debug, Clone, Copy)]
struct VarData {
    reason: CRef,
    level: i32,
}

#[derive(Debug, Clone, Copy)]
struct Watcher {
    cref: CRef,
    blocker: Lit,
}

struct VarOrder<'a> {
    activity: &'a VMap<f64>,
}

/// Predicate to test whether a clause has been removed from some lit's watchlist
struct WatcherDeleted<'a> {
    ca: &'a ClauseAllocator,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
#[repr(u8)]
enum Seen {
    UNDEF,
    SOURCE,
    REMOVABLE,
}

mod utils {
    use super::*;

    /// Finite subsequences of the Luby-sequence:
    ///
    /// > 0: 1
    /// > 1: 1 1 2
    /// > 2: 1 1 2 1 1 2 4
    /// > 3: 1 1 2 1 1 2 4 1 1 2 1 1 2 4 8
    /// ...
    pub(super) fn luby(y: f64, mut x: i32) -> f64 {
        // Find the finite subsequence that contains index 'x', and the
        // size of that subsequence:
        let mut size = 1;
        let mut seq = 0;
        while size < x + 1 {
            seq += 1;
            size = 2 * size + 1;
        }

        while size - 1 != x {
            size = (size - 1) >> 1;
            seq -= 1;
            x = x % size;
        }

        return f64::powi(y, seq);
    }

    /// Generate a random double:
    pub(super) fn drand(seed: &mut f64) -> f64 {
        *seed *= 1389796.0;
        let q = (*seed / 2147483647.0) as i32;
        *seed -= q as f64 * 2147483647.0;
        return *seed / 2147483647.0;
    }

    /// Generate a random integer:
    pub(super) fn irand(seed: &mut f64, size: i32) -> i32 {
        (drand(seed) * size as f64) as i32
    }
}

impl Default for VarData {
    fn default() -> Self {
        Self {
            reason: CRef::UNDEF,
            level: 0,
        }
    }
}

impl VarData {
    #[inline(always)]
    pub(super) fn new(reason: CRef, level: i32) -> Self {
        Self { reason, level }
    }
}

impl PartialEq for Watcher {
    #[inline(always)]
    fn eq(&self, rhs: &Self) -> bool {
        self.cref == rhs.cref
    }
}
impl Eq for Watcher {}

impl<'a> Comparator<Var> for VarOrder<'a> {
    fn cmp(&self, lhs: &Var, rhs: &Var) -> cmp::Ordering {
        PartialOrd::partial_cmp(&self.activity[*rhs], &self.activity[*lhs]).expect("NaN activity")
    }
}

impl<'a> DeletePred<Watcher> for WatcherDeleted<'a> {
    #[inline]
    fn deleted(&self, w: &Watcher) -> bool {
        self.ca.get_ref(w.cref).mark() == 1
    }
}

impl Default for Seen {
    #[inline]
    fn default() -> Self {
        Seen::UNDEF
    }
}

impl Seen {
    #[inline(always)]
    fn is_seen(&self) -> bool {
        *self != Seen::UNDEF
    }
}

impl Watcher {
    const DUMMY: Watcher = Watcher {
        cref: CRef::UNDEF,
        blocker: Lit::UNDEF,
    };
    fn new(cref: CRef, blocker: Lit) -> Self {
        Self { cref, blocker }
    }
}

pub struct SolverOpts {
    pub var_decay: f64,
    pub clause_decay: f64,
    pub random_var_freq: f64,
    pub random_seed: f64,
    pub ccmin_mode: i32,
    pub phase_saving: i32,
    pub rnd_init_act: bool,
    pub luby_restart: bool,
    pub restart_first: i32,
    pub restart_inc: f64,
    pub garbage_frac: f64,
    pub min_learnts_lim: i32,
}

impl Default for SolverOpts {
    fn default() -> SolverOpts {
        Self {
            var_decay: 0.95,
            clause_decay: 0.999,
            random_var_freq: 0.0,
            random_seed: 91648253.0,
            ccmin_mode: 2,
            phase_saving: 2,
            rnd_init_act: false,
            luby_restart: true,
            restart_first: 100,
            restart_inc: 2.0,
            garbage_frac: 0.20,
            min_learnts_lim: 0,
        }
    }
}

impl SolverOpts {
    /// Check that options are valid.
    pub fn check(&self) -> bool {
        (0.0 < self.var_decay && self.var_decay < 1.0)
            && (0.0 < self.clause_decay && self.clause_decay < 1.0)
            && (0.0 <= self.random_var_freq && self.random_var_freq <= 1.0)
            && (0.0 < self.random_seed && self.random_seed < f64::INFINITY)
            && (0 <= self.ccmin_mode && self.ccmin_mode <= 2)
            && (0 <= self.phase_saving && self.phase_saving <= 2)
            && 1 <= self.restart_first
            && (1.0 < self.restart_inc && self.restart_inc < f64::INFINITY)
            && (0.0 < self.garbage_frac && self.garbage_frac < f64::INFINITY)
            && 0 <= self.min_learnts_lim
    }
}
