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
use bytemuck::cast_vec;
use core::ops::ControlFlow;
use default_vec2::ConstDefault;
use internal_iterator::InternalIterator;
use no_std_compat::prelude::v1::*;
use {
    crate::callbacks::{Callbacks, ProgressStatus},
    crate::clause::{
        self, lbool, CRef, ClauseAllocator, ClauseRef, DeletePred, Lit, OccLists, OccListsData,
        VMap, Var,
    },
    crate::heap::{CachedKeyComparator, Heap, HeapData},
    crate::interface::SolverInterface,
    crate::theory::Theory,
    std::{cmp, mem},
};

#[cfg(feature = "logging")]
use crate::clause::display::Print;
use crate::clause::VMapBool;
use crate::core::utils::LubyIter;
use crate::exact_sized_chain::ExactSizedChain;
/// The main solver structure.
///
/// Each instance is a full-fledged SAT solver, and
/// it can be parametrized further with a `theory::TheoryArg` and
/// with basic `callbacks::Callbacks`.
///
/// A `Solver` object contains the whole state of the SAT solver, including
/// a clause allocator, literals, clauses, and statistics.
pub struct Solver<Cb: Callbacks> {
    /// If problem is unsatisfiable (possibly under assumptions),
    /// this literal can be analyzed by `analyze_final`
    /// to produce the conflict clause expressed in the assumptions.
    conflict: Lit,

    cb: Cb, // the callbacks

    /// List of learnt and problem clauses.
    /// Some elements are CRef::UNDEF representing separators of assertion levels
    /// Clauses not allowed to be moved to lower assertion levels unless they all their literals
    /// are at that assertion level or lower
    clauses: Vec<CRef>,

    learnt: u32,

    v: SolverV,
}

/// The current assignments.
struct VarState {
    /// A heuristic measurement of the activity of a variable.
    activity: VMap<f32>,
    /// A priority queue of variables ordered with respect to the variable activity.
    order_heap_data: HeapData<Var, VarOrderKey>,
    /// Current assignment for each variable.
    ass: VMap<lbool>,
    /// Stores reason and level for each variable.
    vardata: VMap<VarData>,
    /// Amount to bump next variable with.
    var_inc: f32,

    /// Assignment stack; stores all assigments made in the order they were made.
    trail: Vec<Lit>,
    /// Separator indices for different decision levels in `trail`.
    trail_lim: Vec<i32>,
}

struct SolverV {
    opts: SolverOpts,
    vars: VarState,

    learntsize_adjust_start_confl: i32,
    learntsize_adjust_inc: f64,
    max_learnts: f64,
    learntsize_adjust_confl: f64,
    learntsize_adjust_cnt: i32,

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

    // /// A heuristic measurement of the activity of a variable.
    // v.activity: VMap<f64>,
    // /// The current assignments.
    // v.assigns: VMap<lbool>,
    // /// A priority queue of variables ordered with respect to the variable activity.
    // v.order_heap_data: HeapData<Var>,
    /// The preferred polarity of each variable.
    polarity: VMapBool,
    /// The users preferred polarity of each variable.
    user_pol: VMap<lbool>,
    /// Declares if a variable is eligible for selection in the decision heuristic.
    decision: VMapBool,
    // /// Stores reason and level for each variable.
    /// `watches[lit]` is a list of constraints watching 'lit' (will go there if literal becomes true).
    watches_data: OccListsData<Lit, Watcher>,
    /// If `self.ok < self.assertion_level()`, the constraints are already unsatisfiable using the first `ok` assertion levels.
    /// No part of the solver state may be used!
    /// Otherwise, equal to u32::MAX
    ok: u32,
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

    // /// Assignment stack; stores all assigments made in the order they were made.
    // v.trail: Vec<Lit>,
    // /// Separator indices for different decision levels in 'trail'.
    // v.trail_lim: Vec<i32>,

    // Temporaries (to reduce allocation overhead). Each variable is prefixed by the method in which it is
    // used, except `seen` wich is used in several places.
    seen: VMap<Seen>,
    minimize_stack: Vec<Lit>,
    analyze_toclear: Vec<Lit>,

    // Resource contraints:
    conflict_budget: i64,
    propagation_budget: i64,

    th_st: ExplainTheoryArg,
}

/// Enables adding lemmas during explanations
#[derive(Default)]
pub struct ExplainTheoryArg {
    lemma_lits: Vec<Lit>,
    lemma_offsets: Vec<usize>, // contiguous slices in `lemma_lits`
    /// Current set of assumptions provided to solve by the user.
    assumptions: Vec<Lit>,
    tmp_c_th: Vec<Lit>, // used for theory conflict
}

impl ExplainTheoryArg {
    fn clear(&mut self) {
        self.lemma_lits.clear();
        self.lemma_offsets.clear();
        self.tmp_c_th.clear()
    }

    /// Push a theory lemma into the solver.
    ///
    /// This is useful for lemma-on-demand or theory splitting, but can
    /// be relatively costly.
    ///
    /// NOTE: This is not fully supported yet.
    pub fn add_theory_lemma(&mut self, lits: &[Lit]) {
        self.lemma_lits.extend_from_slice(lits);
        let idx = self.lemma_lits.len();
        self.lemma_offsets.push(idx);
    }

    fn dedup_last_lemma(&mut self, possibly_equal: &[Lit]) {
        let last_offset = if self.lemma_offsets.len() < 2 {
            0
        } else {
            self.lemma_offsets[self.lemma_offsets.len() - 2]
        };
        if &self.lemma_lits[last_offset..] == possibly_equal {
            self.lemma_offsets.pop();
        }
    }

    /// Returns a list of lits that are represent the assertion levels created by
    /// [`SolverInterface::push_th`]
    ///
    /// The values returned will be `false` in the current model if `i` is less than the current
    /// decision level
    ///
    /// A theory can use `assertion_level_lit(i)` in its explanation/conflict clause to indicate
    /// that it depends on the `i`th assertion level (the first call to [`SolverInterface::push_th`]
    /// creates assertion level 0), but the returned literal should never be negated
    ///
    /// If `i` is larger that than the number of assertion levels this function may panic or return
    /// an arbitrary literal
    pub fn assertion_level_lit(&self, i: u32) -> Lit {
        !self.assumptions[i as usize]
    }

    /// During [`Theory::partial_check`] (and `final_check`) after calling
    /// [`TheoryArg::raise_conflict`] returns mutable access to the conflict clause to allow
    /// modifications
    ///
    /// During [`Theory::explain_propagation_clause`] (and `explain_propagation_clause_final`)
    /// returns a vector that may be useful as a scratch space
    /// (it may contain garbage values at the statr of `explain_propagation_clause(_final)`
    #[inline(always)]
    pub fn clause_builder(&mut self) -> &mut Vec<Lit> {
        &mut self.tmp_c_th
    }

    /// Iterate over the clauses contained in this theory state
    fn iter_lemmas(&self) -> impl Iterator<Item = &[Lit]> {
        let mut last = 0;
        self.lemma_offsets.iter().map(move |&offset| {
            let res = &self.lemma_lits[last..offset];
            last = offset;
            res
        })
    }

    fn num_lemmas(&self) -> usize {
        self.lemma_offsets.len()
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

    fn add_clause(&mut self, clause: impl IntoIterator<Item = Lit>) -> bool {
        let mut buf = mem::take(&mut self.v.th_st.tmp_c_th);
        buf.clear();
        buf.extend(clause);
        let res = self.add_clause_reuse(&mut buf);
        self.v.th_st.tmp_c_th = buf;
        res
    }

    // in the API, we can only add clauses at level 0
    fn add_clause_reuse(&mut self, clause: &mut Vec<Lit>) -> bool {
        debug!(
            "add toplevel clause {:?} at assertion level {}",
            clause,
            self.v.assertion_level()
        );

        if !self.is_ok() {
            return false;
        }

        debug_assert_eq!(
            self.v.decision_level(),
            self.v.assertion_level(),
            "add clause at decision level past assumptions"
        );

        clause.sort_unstable();

        let mut last_lit = Lit::UNDEF;
        let mut j = 0;
        // remove duplicates, true literals, etc.
        for i in 0..clause.len() {
            let lit_i = clause[i];
            let value = self.v.value_lit(lit_i);
            let lvl = self.v.level_lit(lit_i);
            if (value == lbool::TRUE && lvl as u32 <= self.v.assertion_level())
                || lit_i == !last_lit
            {
                return true; // tauto or satisfied already at a level less than or equal to the assertion level
            } else if !(value == lbool::FALSE && lvl as u32 <= self.v.assertion_level())
                && lit_i != last_lit
            {
                // not a duplicate
                last_lit = lit_i;
                clause[j] = lit_i;
                j += 1;
            }
        }

        clause.resize(j, Lit::UNDEF);
        self.add_clause_unchecked(clause.iter().copied())
    }

    fn add_clause_unchecked<I: IntoIterator<Item = Lit>>(&mut self, clause: I) -> bool
    where
        I::IntoIter: ExactSizeIterator,
    {
        let mut clause = clause.into_iter();

        if clause.len() == 0 {
            debug!("add toplevel clause []");
            self.v.ok = self.v.assertion_level();
            return false;
        } else if clause.len() == 1 {
            let lit = clause.next().unwrap();
            debug!("add toplevel clause [{lit:?}]");
            let cr = if let Some(x) = self.v.assumptions().last() {
                let cr = self.v.ca.alloc_with_learnt([lit, !*x].into_iter(), false);
                self.clauses.push(cr);
                self.v.attach_clause(cr);
                cr
            } else {
                CRef::UNDEF
            };
            self.v.vars.unchecked_enqueue(lit, cr);
        } else {
            let extra = self.v.assumptions().last().map(|x| !*x);
            let cr = self
                .v
                .ca
                .alloc_with_learnt(ExactSizedChain(clause.chain(extra)), false);
            debug!(
                "add toplevel clause {:?} ({cr:?})",
                self.v.ca.get_ref(cr).lits()
            );
            self.clauses.push(cr);
            self.v.attach_clause(cr);
        }

        true
    }

    fn reset(&mut self) {
        let new_v = SolverV::new(&self.v.opts);
        self.v = new_v;
        self.conflict = Lit::UNDEF;
        self.clauses.clear();
        self.learnt = 0;
    }

    fn solve_limited_preserving_trail_th<Th: Theory>(
        &mut self,
        th: &mut Th,
        assumps: &[Lit],
    ) -> lbool {
        let old_len = self.v.assumptions().len();
        self.v.th_st.assumptions.extend_from_slice(assumps);
        let res = self.solve_internal(th, old_len);
        self.v.th_st.assumptions.truncate(old_len);
        res
    }

    fn pop_model<Th: Theory>(&mut self, th: &mut Th) {
        self.cancel_until(th, self.v.assertion_level())
    }

    fn raw_value_lit(&self, l: Lit) -> lbool {
        self.v.value_lit(l)
    }

    fn raw_model(&self) -> &[Lit] {
        &self.v.vars.trail
    }

    #[inline(always)]
    fn simplify_th<Th: Theory>(&mut self, th: &mut Th) -> bool {
        if !self.is_ok() {
            return false;
        }
        debug_assert_eq!(self.v.decision_level(), self.v.assertion_level());
        match self.propagate_th(th) {
            Some(_) => {
                self.v.ok = self.v.decision_level();
                false
            }
            None => true,
        }
    }
    fn is_ok(&self) -> bool {
        self.v.ok > self.v.assertion_level()
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

    #[cfg(feature = "std")]
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

    #[cfg(not(feature = "std"))]
    fn print_stats(&self) {}

    fn unsat_core<'a, Th: Theory>(
        &'a mut self,
        th: &'a mut Th,
    ) -> impl InternalIterator<Item = Lit> + 'a {
        struct It<'a, Th, Cb: Callbacks>(&'a mut Solver<Cb>, &'a mut Th);

        impl<'a, Th: Theory, Cb: Callbacks> InternalIterator for It<'a, Th, Cb> {
            type Item = Lit;

            fn try_for_each<R, F>(self, f: F) -> ControlFlow<R>
            where
                F: FnMut(Self::Item) -> ControlFlow<R>,
            {
                if self.0.conflict != Lit::UNDEF {
                    self.0.v.analyze_final(self.1, self.0.conflict, f)
                } else {
                    ControlFlow::Continue(())
                }
            }
        }
        It(self, th)
    }

    fn proved_at_lvl_0(&self) -> &[Lit] {
        self.v.vars.proved_at_lvl_0()
    }

    fn set_decision_var(&mut self, v: Var, dvar: bool) {
        self.v.set_decision_var(v, dvar)
    }

    fn push_th<Th: Theory>(&mut self, th: &mut Th) {
        if self.simplify_th(th) {
            let lit = Lit::new(self.new_var(lbool::UNDEF, false), true);
            self.v.th_st.assumptions.push(lit);
            self.new_decision_level(th);
            self.v.vars.unchecked_enqueue(lit, CRef::UNDEF);
        } else {
            let lit = Lit::new(self.new_var(lbool::UNDEF, false), true);
            self.v.th_st.assumptions.push(lit);
        }
        self.clauses.push(CRef::UNDEF)
    }

    fn pop_n_th<Th: Theory>(&mut self, th: &mut Th, n: u32) {
        if self.is_ok() {
            debug_assert_eq!(self.v.decision_level(), self.v.assertion_level())
        }
        let new_len = self.v.assertion_level() - n;
        if self.v.ok > new_len {
            self.v.ok = u32::MAX;
        }
        self.cancel_until(th, new_len);
        let bound_lit = self.v.assumptions()[new_len as usize];
        trace!("All literals after {bound_lit:?} should have been removed from the theory");
        self.v.th_st.assumptions.truncate(new_len as usize);
        debug_assert!(bound_lit < !bound_lit);
        let mut i = self.clauses.len();
        let mut levels_passed = 0;
        while levels_passed < n {
            i -= 1;
            if self.clauses[i] == CRef::UNDEF {
                levels_passed += 1;
            }
        }
        // All clauses before `i` were created at an earlier assertion level so they must not
        // contain any of the literals we are deleting
        let mut j = i;
        while i < self.clauses.len() {
            let cr = self.clauses[i];
            i += 1;
            if cr == CRef::UNDEF {
                continue;
            }
            let cref = self.v.ca.get_ref(cr);
            if cref.lits().iter().all(|l| *l < bound_lit) {
                // this clause also doesn't contain any of the literals we are deleting so we can keep it
                self.clauses[j] = cr;
                j += 1;
            } else {
                if cref.learnt() {
                    self.learnt -= 1;
                }
                self.v.remove_clause(cr);
            }
        }
        self.clauses.truncate(j);
        let sentinel_lit = !bound_lit;
        for l in self.v.vars.trail.iter_mut() {
            if *l >= bound_lit {
                // Replace any of the literals we are replacing with a sentinel value
                // to make sure the trail length stays the same
                *l = sentinel_lit;
            }
        }
        self.v.next_var = Var::from_idx(sentinel_lit.var().idx() + 1);
    }

    fn with_theory_arg(&mut self, f: impl FnOnce(&mut TheoryArg)) {
        if !self.is_ok() {
            return;
        }
        debug_assert_eq!(self.v.decision_level(), self.v.assertion_level());
        let mut th_arg = {
            TheoryArg {
                v: &mut self.v,
                has_propagated: false,
                conflict: TheoryConflict::Nil,
            }
        };
        f(&mut th_arg);
        if let TheoryConflict::Clause { .. } = th_arg.conflict {
            self.v.ok = self.v.decision_level();
            return;
        } else if let TheoryConflict::Prop(_p) = th_arg.conflict {
            debug!("inconsistent theory propagation {:?}", _p);
            self.v.ok = self.v.decision_level();
            return;
        } else {
            debug_assert!(matches!(th_arg.conflict, TheoryConflict::Nil));

            if self.v.th_st.num_lemmas() > 0 {
                let mut th_st = mem::take(&mut self.v.th_st);
                let mut c = mem::take(&mut th_st.tmp_c_th);
                for lemma in th_st.iter_lemmas() {
                    debug!("add theory lemma {}", lemma.pp_dimacs());
                    c.clear();
                    c.extend_from_slice(lemma);
                    self.add_clause_reuse(&mut c);
                }
                th_st.clear(); // be sure to clean up
                th_st.tmp_c_th = c;
                self.v.th_st = th_st;
            }
        }
    }
}

#[derive(Clone)]
pub struct CheckPoint {
    trail_len: u32,
    clause_num: u32,
    next_var: Var,
    ok: u32,
}

impl<Cb: Callbacks> Solver<Cb> {
    pub fn checkpoint(&self) -> CheckPoint {
        CheckPoint {
            trail_len: self.v.vars.trail.len() as u32,
            clause_num: self.clauses.len() as u32,
            next_var: self.v.next_var,
            ok: self.v.ok,
        }
    }

    pub fn restore_checkpoint(&mut self, check_point: CheckPoint) {
        for v in self.v.vars.trail.drain(check_point.trail_len as usize..) {
            self.v.vars.ass[v.var()] = lbool::UNDEF;
            self.v.vars.vardata[v.var()] = VarData::default();
        }

        for cr in self.clauses.drain(check_point.clause_num as usize..) {
            self.v.remove_clause(cr);
        }

        self.v.next_var = check_point.next_var;
        self.v.ok = check_point.ok;
    }
}

impl<Cb: Callbacks + Default> Default for Solver<Cb> {
    fn default() -> Self {
        Solver::new(SolverOpts::default(), Default::default())
    }
}

impl<Cb: Callbacks> Solver<Cb> {
    /// Create a new solver with the given options and the callbacks `cb`.
    pub fn new(opts: SolverOpts, cb: Cb) -> Self {
        Solver::new_with(opts, cb)
    }
}

// main algorithm
impl<Cb: Callbacks> Solver<Cb> {
    /// Create a new solver with the given options and callbacks.
    pub fn new_with(opts: SolverOpts, cb: Cb) -> Self {
        assert!(opts.check());
        Self {
            // Parameters (user settable):
            conflict: Lit::UNDEF,
            cb,
            clauses: vec![],
            learnt: 0,
            v: SolverV::new(&opts),
        }
    }

    /// Returns the options that are currently being used
    pub fn options(&self) -> SolverOpts {
        self.v.opts.clone()
    }

    /// Tries to set the options being used to `new_opts`
    /// If `new_opts` aren't valid, returns `Err(())` and leaves the options unchanged
    pub fn set_options(&mut self, new_opts: SolverOpts) -> Result<(), ()> {
        if new_opts.check() {
            self.v.opts = new_opts;
            Ok(())
        } else {
            Err(())
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

    fn simplify_internal(&mut self) {
        debug_assert!(self.v.decision_level() <= self.v.assertion_level());

        if !self.is_ok() {
            return;
        }

        if self.v.num_assigns() as i32 == self.v.simp_db_assigns || self.v.simp_db_props > 0 {
            return;
        }

        self.remove_satisfied(); // Remove satisfied learnt clauses
        self.check_garbage();

        self.v.simp_db_assigns = self.v.num_assigns() as i32;
        // (shouldn't depend on stats really, but it will do for now)
        self.v.simp_db_props = (self.v.clauses_literals + self.v.learnts_literals) as i64;
    }

    fn propagate_th<Th: Theory>(&mut self, th: &mut Th) -> Option<Conflict> {
        loop {
            if let Some(conf) = self.v.propagate() {
                return Some(Conflict::BCP(conf));
            }

            match self.call_theory::<_, false>(th) {
                Ok(true) => {}
                Ok(false) => return None,
                Err(conf) => return Some(conf),
            }
        }
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
        debug_assert!(self.is_ok());
        let conflict_threshold = if nof_conflicts < 0 {
            u64::MAX
        } else {
            nof_conflicts as u64 + self.v.conflicts
        };
        self.v.starts += 1;

        'main: loop {
            // boolean propagation
            let confl = self.propagate_th(th);

            if let Some(confl) = confl {
                // conflict analysis
                if self.v.decision_level() == 0 {
                    return lbool::FALSE;
                }
                self.v.conflicts += 1;
                self.handle_conflict(th, tmp_learnt, confl);

                self.v.vars.var_decay_activity(self.v.opts.var_decay);
                self.v.cla_decay_activity();

                self.v.learntsize_adjust_cnt -= 1;
                if self.v.learntsize_adjust_cnt == 0 {
                    self.v.learntsize_adjust_confl *= self.v.learntsize_adjust_inc;
                    self.v.learntsize_adjust_cnt = self.v.learntsize_adjust_confl as i32;
                    self.v.max_learnts *= self.v.opts.learntsize_inc;

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
                // no conflict
                if self.v.conflicts > conflict_threshold || !self.within_budget() {
                    // Reached bound on number of conflicts:
                    self.v.progress_estimate = self.v.progress_estimate();
                    self.cancel_until(th, self.v.assertion_level());
                    return lbool::UNDEF;
                }

                // Simplify the set of problem clauses:
                if self.v.decision_level() == 0 {
                    self.simplify_internal()
                }

                if self.learnt as f64 - self.v.num_assigns() as f64 > self.v.max_learnts {
                    // Reduce the set of learnt clauses:
                    self.reduce_db();
                }

                // select the next decision (using assumptions, or variable heap)
                let mut next = Lit::UNDEF;
                while (self.v.decision_level() as usize) < self.v.assumptions().len() {
                    // Perform user provided assumption:
                    let p = self.v.assumptions()[self.v.decision_level() as usize];
                    if self.v.value_lit(p) == lbool::TRUE {
                        // Dummy decision level, since `p` is true already:
                        self.new_decision_level(th);
                    } else if self.v.value_lit(p) == lbool::FALSE {
                        // conflict at the next level because of `p`, unsat
                        self.conflict = !p;
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
                        let th_res = self.call_theory::<_, true>(th);

                        match th_res {
                            // Model found and validated by the theory
                            Ok(false) => return lbool::TRUE,
                            // some propagations in final-check
                            Ok(true) => continue 'main,
                            Err(confl) => {
                                self.v.conflicts += 1;
                                if self.v.decision_level() == 0 {
                                    return lbool::FALSE;
                                }
                                self.handle_conflict(th, tmp_learnt, confl);
                                continue 'main;
                            }
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

    fn handle_conflict<Th: Theory>(
        &mut self,
        th: &mut Th,
        tmp_learnt: &mut Vec<Lit>,
        confl: Conflict,
    ) {
        let learnt = self.v.analyze(confl, &self.clauses, tmp_learnt, th);
        self.add_learnt_and_backtrack(th, learnt, clause::Kind::Learnt);
    }

    /// Add a learnt clause and backtrack/propagate as necessary
    fn add_learnt_and_backtrack<Th: Theory>(
        &mut self,
        th: &mut Th,
        learnt: LearntClause,
        k: clause::Kind,
    ) {
        self.cb.on_new_clause(learnt.clause, k);
        self.cancel_until(th, learnt.backtrack_lvl as u32);

        // propagate the only lit of `learnt_clause` that isn't false
        if learnt.clause.len() == 1 {
            // directly propagate the unit clause at level 0
            self.v.vars.unchecked_enqueue(learnt.clause[0], CRef::UNDEF);
        } else if learnt.clause.is_empty() {
            self.v.ok = 0;
        } else {
            // propagate the lit, justified by `cr`
            let cr = self
                .v
                .ca
                .alloc_with_learnt(learnt.clause.iter().copied(), true);
            debug!("Learnt clause {:?} ({cr:?})", learnt.clause);
            self.clauses.push(cr);
            self.learnt += 1;
            self.v.attach_clause(cr);
            self.v.cla_bump_activity(&self.clauses, cr);
            self.v.vars.unchecked_enqueue(learnt.clause[0], cr);
        }

        self.flush_th_lemmas(th);
    }

    fn flush_th_lemmas<Th: Theory>(&mut self, th: &mut Th) {
        let mut th_st = mem::take(&mut self.v.th_st);
        let mut c = mem::take(&mut th_st.tmp_c_th);
        for lemma in th_st.iter_lemmas() {
            debug!("add theory lemma {}", lemma.pp_dimacs());
            c.clear();
            c.extend_from_slice(lemma);
            self.add_clause_during_search(th, &mut c);
        }
        th_st.clear(); // be sure to cleanup
        th_st.tmp_c_th = c;
        self.v.th_st = th_st;
    }

    /// Call theory to check the current (possibly partial) model
    ///
    /// Returns `Ok(true)` if the theory propagated something, `Ok(false)` if
    /// the theory accepted the model without propagations, and `Err(conf)` if the theory
    /// rejected the model
    fn call_theory<Th: Theory, const FINAL: bool>(
        &mut self,
        th: &mut Th,
    ) -> Result<bool, Conflict> {
        let mut th_arg = {
            TheoryArg {
                v: &mut self.v,
                has_propagated: false,
                conflict: TheoryConflict::Nil,
            }
        };
        // call theory
        match FINAL {
            false => th.partial_check(&mut th_arg),
            true => th.final_check(&mut th_arg),
        }
        if let TheoryConflict::Clause { costly } = th_arg.conflict {
            // borrow magic

            debug!(
                "theory conflict {:?} (costly: {})",
                &self.v.th_st.tmp_c_th, costly
            );
            self.v.vars.sort_clause_lits(&mut self.v.th_st.tmp_c_th); // as if it were a normal clause
            self.v.th_st.tmp_c_th.dedup();
            Err(Conflict::ThLemma { add: costly })
        } else if let TheoryConflict::Prop(p) = th_arg.conflict {
            // conflict: propagation of a lit known to be false
            debug!("inconsistent theory propagation {:?}", p);
            Err(Conflict::ThProp(p))
        } else {
            debug_assert!(matches!(th_arg.conflict, TheoryConflict::Nil));

            let mut has_propagated = th_arg.has_propagated;

            if self.v.th_st.num_lemmas() > 0 {
                self.flush_th_lemmas(th);
                has_propagated = true;
            }

            if has_propagated {
                Ok(true)
            } else {
                Ok(false) // Model validated without further work needed
            }
        }
    }

    /// Main solve method (assumptions given in `self.assumptions`).
    #[inline(always)]
    fn solve_internal<Th: Theory>(&mut self, th: &mut Th, assertion_level: usize) -> lbool {
        assert!(self.v.decision_level() <= self.v.assertion_level());
        self.conflict = Lit::UNDEF;
        if !self.is_ok() {
            return lbool::FALSE;
        }

        self.v.solves += 1;
        let mut tmp_learnt: Vec<Lit> = vec![];

        self.v.max_learnts = self.num_clauses() as f64 * self.v.opts.learntsize_factor;
        if self.v.max_learnts < self.v.opts.min_learnts_lim as f64 {
            self.v.max_learnts = self.v.opts.min_learnts_lim as f64;
        }

        self.v.learntsize_adjust_confl = self.v.learntsize_adjust_start_confl as f64;
        self.v.learntsize_adjust_cnt = self.v.learntsize_adjust_confl as i32;
        let mut status;

        info!("search.start");
        self.cb.on_start();

        // Search:
        let mut rest_base: f64 = 1.0;
        let mut luby_state = LubyIter::new();
        loop {
            let nof_clauses = (rest_base * self.v.opts.restart_first as f64) as i32;
            status = self.search(th, nof_clauses, &mut tmp_learnt);
            if !self.within_budget() {
                break;
            }

            if status != lbool::UNDEF {
                break;
            } else {
                info!("search.restart");
                self.cb.on_restart();
                if self.v.opts.luby_restart {
                    luby_state.step(&mut rest_base, self.v.opts.restart_inc);
                } else {
                    rest_base *= self.v.opts.restart_inc;
                };
            }
        }

        self.cb.on_result(status);

        if status == lbool::FALSE {
            if self.conflict == Lit::UNDEF {
                // NOTE: we may return `false` without an empty conflict in case we had assumptions. In
                // this case `self.conflict` contains the unsat-core but adding new clauses might
                // succeed in the absence of these assumptions.
                self.v.ok = 0;
            } else if self.v.decision_level() < assertion_level as u32 {
                // assumptions above the decision level are conflicting
                self.v.ok = self.v.decision_level() + 1;
            }
        }

        debug!("res: {:?}", status);
        trace!("lowest failing level {}", self.v.ok);
        trace!("proved at lvl 0: {:?}", self.v.vars.proved_at_lvl_0());
        status
    }

    /// Remove half of the learnt clauses, minus the clauses locked by the current assignment. Locked
    /// clauses are clauses that are reason to some assignment. Binary clauses are never removed.
    fn reduce_db(&mut self) {
        let extra_lim = self.v.cla_inc / self.learnt as f64; // Remove any clause below this activity
        let mut buf = mem::take(&mut self.v.th_st.tmp_c_th);
        buf.clear();
        let mut activities: Vec<f32> = cast_vec(buf);
        for cr in &self.clauses {
            if *cr == CRef::UNDEF {
                continue;
            }
            let cr = self.v.ca.get_ref(*cr);
            if cr.learnt() {
                if cr.size() <= 2 {
                    activities.push(f32::INFINITY)
                } else {
                    activities.push(cr.activity())
                }
            }
        }
        debug_assert_eq!(activities.len(), self.learnt as usize);
        let mid_point = activities.len() / 2;
        let (_, median_activity, _) = activities
            .select_nth_unstable_by(mid_point, |x, y| x.partial_cmp(y).expect("NaN activity"));
        let lim = cmp::max_by(*median_activity, extra_lim as f32, |x, y| {
            x.partial_cmp(y).unwrap()
        });
        activities.clear();
        self.v.th_st.tmp_c_th = cast_vec(activities);

        debug!("reduce_db.start");
        // Don't delete binary or locked clauses. From the rest, delete clauses from the first half
        // and clauses with activity smaller than `extra_lim`:
        let mut j = 0;
        for i in 0..self.clauses.len() {
            let cr = self.clauses[i];
            let cond = cr != CRef::UNDEF && {
                let c = self.v.ca.get_ref(cr);
                c.learnt() && c.size() > 2 && !self.v.locked(c) && c.activity() < lim
            };
            if cond {
                self.v.remove_clause(cr);
                self.cb.on_delete_clause(self.v.ca.get_ref(cr).lits());
            } else {
                self.clauses[j] = cr;
                j += 1;
            }
        }

        // self.learnts.resize_default(j);
        let deleted = self.clauses.len() - j;
        self.clauses.truncate(j);
        self.learnt -= deleted as u32;

        debug!("reduce_db.done (deleted {})", deleted);

        self.check_garbage();
    }

    /// Shrink the given set to contain only non-satisfied clauses.
    fn remove_satisfied(&mut self) {
        assert_eq!(self.v.decision_level(), 0);
        let cs = &mut self.clauses;
        let self_v = &mut self.v;
        cs.retain(|&cr| {
            if cr == CRef::UNDEF {
                return true;
            }
            let cr_ref = self_v.ca.get_ref(cr);
            // TODO investigate why this causes slow down (is garbage_frac to low)
            if !cr_ref.learnt() {
                return true;
            }
            let satisfied = self_v.satisfied(cr_ref);
            if satisfied {
                if cr_ref.learnt() {
                    self.learnt -= 1;
                }
                debug!("remove satisfied clause {:?}", cr_ref.lits());
                self_v.remove_clause(cr);
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

        self.v.reloc_all(&mut self.clauses, &mut to);

        self.cb.on_gc(
            (self.v.ca.len() * ClauseAllocator::UNIT_SIZE) as usize,
            (to.len() * ClauseAllocator::UNIT_SIZE) as usize,
        );
        self.v.ca = to;
    }

    /// Check whether the space wasted by dead clauses in the clause allocator exceeds
    /// the threshold
    fn check_garbage(&mut self) {
        if self.v.ca.wasted() as f64 > self.v.ca.len() as f64 * self.v.opts.garbage_frac {
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

    fn within_budget(&self) -> bool {
        (self.v.conflict_budget < 0 || self.v.conflicts < self.v.conflict_budget as u64)
            && (self.v.propagation_budget < 0
                || self.v.propagations < self.v.propagation_budget as u64)
            && !self.cb.stop()
    }

    /// Add clause during search
    fn add_clause_during_search<Th: Theory>(&mut self, th: &mut Th, clause: &mut Vec<Lit>) -> bool {
        debug!("add internal clause {:?}", clause);
        if self.v.ok == 0 {
            return false;
        }

        self.v.vars.sort_clause_lits(clause);

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

        if clause.is_empty() {
            self.v.ok = 0;
            return false;
        } else if clause.len() == 1 {
            self.cancel_until(th, 0); // only at level 0
            self.v.vars.unchecked_enqueue(clause[0], CRef::UNDEF);
        } else {
            let cr = self.v.ca.alloc_with_learnt(clause.iter().copied(), false);
            self.clauses.push(cr);
            self.v.attach_clause(cr);
        }

        true
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
/// When the theory is called (on a partial model that is satisfiable on
/// the boolean level), it can use this object to trigger conflicts,
/// add lemmas, and propagate literals.
pub struct TheoryArg<'a> {
    v: &'a mut SolverV,
    has_propagated: bool,
    conflict: TheoryConflict,
}

/// Temporary representation of a learnt clause, produced in `analyze`.
struct LearntClause<'a> {
    clause: &'a [Lit],  // the clause
    backtrack_lvl: i32, // where to backtrack?
}

#[derive(Clone, Copy, Debug)]
enum Conflict {
    BCP(CRef),             // boolean propagation conflict
    ThLemma { add: bool }, // clause in in v.th_st.tmp_c_th
    ThProp(Lit),           // literal was propagated, but is false
}

#[derive(Clone, Copy, Debug)]
enum ResolveWith {
    Init(Conflict),     // initial conflict
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

    #[inline(always)]
    pub fn assumptions(&self) -> &[Lit] {
        &self.th_st.assumptions
    }

    #[inline(always)]
    fn assertion_level(&self) -> u32 {
        self.assumptions().len() as u32
    }

    fn order_heap(&mut self) -> Heap<Var, VarOrder> {
        self.vars.order_heap()
    }

    fn set_decision_var(&mut self, v: Var, b: bool) {
        let old_contains = self.decision.set(v, b);
        self.dec_vars += b as u64;
        self.dec_vars -= old_contains as u64;
        self.insert_var_order(v);
    }

    fn insert_var_order(&mut self, x: Var) {
        if !self.order_heap().in_heap(x) && self.decision.contains_mut(x) {
            self.order_heap().insert(x);
        }
    }

    fn cla_decay_activity(&mut self) {
        self.cla_inc *= 1.0 / self.opts.clause_decay;
    }

    fn cla_bump_activity(&mut self, clauses: &[CRef], cr: CRef) {
        let new_activity = {
            let mut c = self.ca.get_mut(cr);
            let r = c.activity() + self.cla_inc as f32;
            c.set_activity(r);
            r
        };
        if new_activity > 1e20 {
            // Rescale:
            for &learnt in clauses.iter() {
                let mut c = self.ca.get_mut(learnt);
                if c.as_clause_ref().learnt() {
                    let r = c.activity() * 1e-20;
                    c.set_activity(r);
                }
            }
            self.cla_inc *= 1e-20;
        }
    }

    /// Pick a literal to make a decision with
    fn pick_branch_lit(&mut self) -> Lit {
        let mut next = Var::UNDEF;

        // Random decision:
        if utils::drand(&mut self.opts.random_seed) < self.opts.random_var_freq
            && !self.order_heap().is_empty()
        {
            let idx_tmp = utils::irand(
                &mut self.opts.random_seed,
                self.vars.order_heap_data.len() as i32,
            ) as usize;
            next = self.vars.order_heap_data[idx_tmp].var();
            if self.value(next) == lbool::UNDEF && self.decision.contains_mut(next) {
                self.rnd_decisions += 1;
            }
        }

        // Activity based decision:
        while next == Var::UNDEF
            || self.value(next) != lbool::UNDEF
            || !self.decision.contains_mut(next)
        {
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
        } else if self.opts.rnd_pol {
            Lit::new(next, utils::drand(&mut self.opts.random_seed) < 0.5)
        } else {
            Lit::new(next, self.polarity.contains_mut(next))
        }
    }

    fn watches(&mut self) -> OccLists<Lit, Watcher, WatcherDeleted> {
        self.watches_data.promote(WatcherDeleted { ca: &self.ca })
    }

    fn new_var(&mut self, upol: lbool, dvar: bool) -> Var {
        let v = self.next_var;
        self.next_var = Var::from_idx(self.next_var.idx() + 1);
        self.watches().init(Lit::new(v, false));
        self.watches().init(Lit::new(v, true));
        *self.vars.ass.get_mut(v) = lbool::UNDEF;
        *self.vars.vardata.get_mut(v) = VarData::default();
        *self.vars.activity.get_mut(v) = if self.opts.rnd_init_act {
            (utils::drand(&mut self.opts.random_seed) * 0.00001) as f32
        } else {
            0.0
        };
        *self.seen.get_mut(v) = Seen::UNDEF;
        self.polarity.remove(v);
        *self.user_pol.get_mut(v) = upol;
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
        orig: Conflict,
        clauses: &[CRef],
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
            Conflict::ThLemma { add, .. } => {
                let lits = &self.th_st.tmp_c_th;
                if add {
                    self.th_st.lemma_lits.extend_from_slice(lits);
                    let idx = self.th_st.lemma_lits.len();
                    self.th_st.lemma_offsets.push(idx);
                }
                // check it's a proper conflict clause
                debug_assert!(lits.iter().all(|&p| self.value_lit(p) == lbool::FALSE));

                if lits.len() <= 1 {
                    // unit clause: learn the clause itself at level 0
                    trace!("analyze: learn unit clause {:?} itself", lits);
                    out_learnt.extend_from_slice(lits);
                    return LearntClause {
                        clause: &*out_learnt,
                        backtrack_lvl: 0,
                    };
                }
                let lvl = lits
                    .iter()
                    .map(|&lit| self.level_lit(lit))
                    .max()
                    .unwrap_or(0);
                if lvl == 0 {
                    // all at level 0: empty clause
                    trace!("analyze: conflict level 0, learn empty clause");
                    return LearntClause {
                        clause: &[],
                        backtrack_lvl: 0,
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
            let lits = match cur_clause {
                ResolveWith::Init(Conflict::ThLemma { .. }) => &self.th_st.tmp_c_th,
                ResolveWith::Init(Conflict::ThProp(lit)) => {
                    // theory propagation, ask the theory to justify `lit` with Γ.
                    // The initial conflict is `Γ => lit`, which is false in current trail.
                    let lits = th.explain_propagation_clause(lit, &mut self.th_st);
                    debug_assert_eq!(lits[0], lit);
                    debug_assert!({
                        let vars = &self.vars;
                        lits.iter().all(|&q| vars.value_lit(q) == lbool::FALSE)
                    });
                    lits
                }
                ResolveWith::Init(Conflict::BCP(cr)) => {
                    // bump activity if `cr` is a learnt clause
                    let mut c = self.ca.get_ref(cr);
                    if c.learnt() {
                        self.cla_bump_activity(clauses, cr);
                        c = self.ca.get_ref(cr); // re-borrow
                    }

                    c.lits()
                }
                ResolveWith::Resolve(lit, cr) if cr == CRef::SPECIAL => {
                    // theory propagation, ask the theory to justify `lit`
                    let lits = th.explain_propagation_clause(lit, &mut self.th_st);
                    debug_assert_eq!(lits[0], lit);
                    let lits = &lits[1..];
                    debug_assert!(lits.iter().all(|&q| self.vars.value_lit(q) == lbool::FALSE));
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
                        self.cla_bump_activity(clauses, cr);
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
                let lvl = self.vars.level(q.var());
                assert!(lvl <= conflict_level);
                if !self.seen[q.var()].is_seen() && lvl > 0 {
                    self.vars.var_bump_activity(q.var());
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
                    panic!("possible cycle in conflict graph between");
                }
            }
            // Select next literal in the trail to look at:
            while !self.seen[self.vars.trail[index - 1].var()].is_seen() {
                debug_assert!(self.vars.level(self.vars.trail[index - 1].var()) >= conflict_level);
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
        match orig {
            Conflict::ThLemma { add: true } => self.th_st.dedup_last_lemma(&out_learnt),
            _ => {}
        }
        LearntClause {
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
        self.analyze_toclear.extend_from_slice(out_learnt);
        let new_size = if self.opts.ccmin_mode == 2 {
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
        } else if self.opts.ccmin_mode == 1 {
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
    fn analyze_final<Th: Theory, E>(
        &mut self,
        th: &mut Th,
        p: Lit,
        mut f: impl FnMut(Lit) -> ControlFlow<E>,
    ) -> ControlFlow<E> {
        f(p);
        debug!("analyze_final lit={:?}", p);

        if self.decision_level() == 0 {
            return ControlFlow::Continue(()); // no assumptions
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
                    f(!lit)?;
                } else if reason == CRef::SPECIAL {
                    // resolution with propagation reason
                    let lits = th.explain_propagation_clause_final(lit, &mut self.th_st);
                    debug_assert_eq!(lits[0], lit);
                    for &p in &lits[1..] {
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
        debug_assert!(self.seen.iter().all(|&s| s == Seen::UNDEF));
        ControlFlow::Continue(())
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
                let ws = self.watches_data.get_mut(p);
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
                        debug_assert_ne!(!c[1], p);
                        self.watches_data.get_mut(!c[1]).push(w);
                        continue 'clauses;
                    }
                }
                let ws = self.watches_data.get_mut(p);

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
            let ws = self.watches_data.get_mut(p);
            let dummy = Watcher::DUMMY;
            ws.resize(j, dummy);
        }
        self.propagations += num_props as u64;
        self.simp_db_props -= num_props as i64;

        confl
    }

    /// Move to the given clause allocator, where clause indices might differ
    fn reloc_all(&mut self, clauses: &mut Vec<CRef>, to: &mut ClauseAllocator) {
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
                for watch in self.watches_data.get_mut(p) {
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

        // All clauses:
        for cr in clauses.iter_mut() {
            if *cr != CRef::UNDEF {
                debug_assert!(!is_removed!(self.ca, *cr));
                self.ca.reloc(cr, to);
            }
        }
    }

    /// Attach a clause to watcher lists
    fn attach_clause(&mut self, cr: CRef) {
        let (c0, c1, learnt, size) = {
            let c = self.ca.get_ref(cr);
            debug_assert!(c.size() > 1);
            (c[0], c[1], c.learnt(), c.size())
        };
        self.watches().get_mut(!c0).push(Watcher::new(cr, c1));
        self.watches().get_mut(!c1).push(Watcher::new(cr, c0));
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
        for c in trail_lim_level..self.vars.trail.len() {
            let x = self.vars.trail[c].var();
            self.vars.ass[x] = lbool::UNDEF;
            if self.opts.phase_saving > 1 || (self.opts.phase_saving == 1 && c > trail_lim_last) {
                self.polarity.set(x, self.vars.trail[c].sign());
            }
            self.insert_var_order(x);
        }
        self.qhead = trail_lim_level as i32;
        self.vars.trail.truncate(trail_lim_level);
        // eprintln!("decision_level {} -> {}", self.trail_lim.len(), level);
        self.vars.trail_lim.truncate(level as usize);
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
            let pos = watches
                .get_mut(!c0)
                .iter()
                .position(|x| x == &Watcher::new(cr, c1))
                .expect("Watcher not found");
            watches.get_mut(!c0).remove(pos);
            let pos = watches
                .get_mut(!c1)
                .iter()
                .position(|x| x == &Watcher::new(cr, c0))
                .expect("Watcher not found");
            watches.get_mut(!c1).remove(pos);
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
        let mut f_pow_i = 1.0;

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
            progress += f_pow_i * (end - beg) as f64;
            f_pow_i *= f;
        }

        progress / self.num_vars() as f64
    }
    fn new(opts: &SolverOpts) -> Self {
        Self {
            opts: opts.clone(),
            vars: VarState::new(),
            num_clauses: 0,
            num_learnts: 0,
            clauses_literals: 0,
            learnts_literals: 0,

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

            polarity: VMapBool::default(),
            user_pol: VMap::default(),
            decision: VMapBool::default(),
            // v.vardata: VMap::new(),
            watches_data: OccListsData::new(),
            ok: u32::MAX,
            cla_inc: 1.0,
            // v.var_inc: 1.0,
            qhead: 0,
            simp_db_assigns: -1,
            simp_db_props: 0,
            progress_estimate: 0.0,
            next_var: Var::from_idx(0),

            ca: ClauseAllocator::new(),

            seen: VMap::default(),
            minimize_stack: vec![],
            analyze_toclear: vec![],
            max_learnts: 0.0,
            learntsize_adjust_confl: 0.0,
            learntsize_adjust_cnt: 0,

            // Resource constraints:
            conflict_budget: -1,
            propagation_budget: -1,

            th_st: ExplainTheoryArg::default(),
        }
    }
}

/// Large f32 that is still small enough that it can't cause another f32 to overflow to infinity
const THRESHOLD: f32 = 1.0141204e31;
#[test]
fn test_threshold() {
    let f = f32::MAX * 2.0f32.powi(-1 - (f32::MANTISSA_DIGITS as i32));
    assert_eq!(THRESHOLD, f);
    // adding THRESHOLD to a float can never make it overflow to infinity
    assert_eq!(f32::MAX + THRESHOLD, f32::MAX)
}

/// multiply a positive float `f` by 0.5f32.powi(`pow2`)
/// truncates to positive 0 instead of using sub-normal numbers
#[inline]
fn scale_down_float(f: f32, pow2: u32) -> f32 {
    f32::from_bits(
        f.to_bits()
            .saturating_sub(pow2 << (f32::MANTISSA_DIGITS - 1)),
    )
}

#[test]
fn test_scale_down_float() {
    assert_eq!(scale_down_float(42.0, 10), 42.0 * 0.5f32.powi(10));
    let actual = scale_down_float(42.0, 140);
    let expect = 42.0 * 0.5_f32.powi(140);
    assert!(0.0 <= actual && actual <= expect && expect < f32::MIN_POSITIVE)
}

impl VarState {
    fn new() -> Self {
        Self {
            ass: VMap::default(),
            vardata: VMap::default(),
            activity: VMap::default(),
            var_inc: 1.0,
            trail: vec![],
            trail_lim: vec![],
            order_heap_data: HeapData::new(),
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

    fn var_decay_activity(&mut self, decay: f32) {
        self.var_inc *= 1.0 / decay;
        if self.var_inc > THRESHOLD {
            let scale = -f32::MIN_EXP as u32;
            // Rescale:
            for x in self.activity.iter_mut() {
                *x = scale_down_float(*x, scale)
            }
            for x in self.order_heap_data.heap_mut().iter_mut() {
                x.map_activity(|activity| scale_down_float(activity, scale))
            }
            self.var_inc = scale_down_float(self.var_inc, scale);
        }
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

    fn order_heap(&mut self) -> Heap<Var, VarOrder> {
        self.order_heap_data.promote(VarOrder {
            activity: &self.activity,
        })
    }

    /// Increase a variable with the current 'bump' value.
    fn var_bump_activity(&mut self, v: Var) {
        *self.activity.get_mut(v) += self.var_inc;

        // Update order_heap with respect to new activity:
        let mut order_heap = self.order_heap();
        if order_heap.in_heap(v) {
            order_heap.decrease(v);
        }
    }

    #[allow(dead_code)]
    fn iter_trail<'a>(&'a self) -> impl Iterator<Item = Lit> + 'a {
        self.trail.iter().map(|l| *l)
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

            let lvl1 = self.level(lit1.var());
            let lvl2 = self.level(lit2.var());
            if lvl1 != lvl2 {
                lvl2.cmp(&lvl1) // higher level come first
            } else {
                lit1.cmp(&lit2) // otherwise default comparison
            }
        });

        // check that the first literal is a proper watch
        debug_assert!(
            clause.len() == 0 || self.value_lit(clause[0]) == lbool::UNDEF || {
                let lvl0 = self.level(clause[0].var());
                clause[1..]
                    .iter()
                    .all(|&lit2| self.level(lit2.var()) <= lvl0)
            }
        );
    }
}

impl<'a> TheoryArg<'a> {
    /// Is the state of the solver still potentially satisfiable?
    ///
    /// `is_ok() == false` means UNSAT was found.
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

    /// Current (possibly partial) model, as a slice of true literals.
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
            self.v.th_st.add_theory_lemma(c)
        }
    }

    pub fn explain_arg(&mut self) -> &mut ExplainTheoryArg {
        &mut self.v.th_st
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
        if self.is_ok() {
            self.conflict = TheoryConflict::Clause { costly };
            self.v.th_st.tmp_c_th.clear();
            self.v.th_st.tmp_c_th.extend_from_slice(lits);
        }
    }

    /// Must be called after calling [`raise_conflict`](TheoryArg::raise_conflict)
    ///
    /// Marks the previously added conflict as costly
    pub fn make_conflict_costly(&mut self) {
        debug_assert!(matches!(self.conflict, TheoryConflict::Clause { .. }));
        self.conflict = TheoryConflict::Clause { costly: true };
    }
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
    activity: &'a VMap<f32>,
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

    /// See https://www.cs.ubc.ca/~nickhar/papers/PostOrderHeap/FUN04-PostOrderHeap.pdf
    pub(super) struct LubyIter {
        /// D_n
        d: u32,
        /// 1 << H(n)
        /// also Luby(n)
        h: u32,
    }

    impl LubyIter {
        #[inline]
        pub(crate) fn new() -> Self {
            LubyIter { d: 0, h: 1 }
        }

        #[inline]
        pub(crate) fn step(&mut self, rest_base: &mut f64, restart_inc: f64) {
            if self.h & self.d == 0 {
                self.d |= self.h;
                self.h = 1;
                *rest_base = 1.0;
            } else {
                self.d &= !self.h;
                self.h <<= 1;
                *rest_base *= restart_inc;
            }
        }
    }

    #[test]
    fn test_luby() {
        let luby_seq = [1u32, 1, 2, 1, 1, 2, 4, 1, 1, 2, 1, 1, 2, 4, 8];
        let mut rest_base = 1.0f64;
        let restart_inc = 1.5f64;
        let mut luby_state = LubyIter::new();
        for luby in luby_seq {
            assert_eq!(rest_base, restart_inc.powi(luby.ilog2() as i32));
            luby_state.step(&mut rest_base, restart_inc)
        }
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
        *Self::DEFAULT
    }
}

impl ConstDefault for VarData {
    const DEFAULT: &'static Self = &Self {
        reason: CRef::UNDEF,
        level: 0,
    };
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

#[derive(Copy, Clone, Ord, PartialOrd, Eq, PartialEq)]
struct VarOrderKey(u64);

impl VarOrderKey {
    #[inline]
    fn new(var: Var, activity: f32) -> Self {
        VarOrderKey((!(activity.to_bits() as u64) << u32::BITS) | (var.idx() as u64))
    }

    fn var(self) -> Var {
        Var::unsafe_from_idx(self.0 as u32)
    }

    fn activity(self) -> f32 {
        f32::from_bits(!((self.0 >> u32::BITS) as u32))
    }

    fn map_activity(&mut self, f: impl FnOnce(f32) -> f32) {
        *self = VarOrderKey::new(self.var(), f(self.activity()))
    }
}
impl<'a> CachedKeyComparator<Var> for VarOrder<'a> {
    type Key = VarOrderKey;

    fn cache_key(&self, t: Var) -> Self::Key {
        VarOrderKey::new(t, self.activity.get(t))
    }

    fn max_key(&self) -> Self::Key {
        VarOrderKey::new(Var::UNDEF, 0.0)
    }

    fn un_cache_key(&self, k: Self::Key) -> Var {
        k.var()
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

impl ConstDefault for Seen {
    const DEFAULT: &'static Self = &Seen::UNDEF;
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

/// Solver options.
///
/// This can be used to tune the solver heuristics.
#[derive(Clone)]
pub struct SolverOpts {
    pub var_decay: f32,
    pub clause_decay: f64,
    pub random_var_freq: f64,
    pub random_seed: f64,
    pub luby_restart: bool,
    /// Controls conflict clause minimization (0=none, 1=basic, 2=deep).
    pub ccmin_mode: i32,
    /// Controls the level of phase saving (0=none, 1=limited, 2=full).
    pub phase_saving: i32,
    /// Use random polarities for branching heuristics.
    pub rnd_pol: bool,
    /// Initialize variable activities with a small random value.
    pub rnd_init_act: bool,
    /// The fraction of wasted memory allowed before a garbage collection is triggered.
    pub garbage_frac: f64,
    /// Minimum number to set the learnts limit to.
    pub min_learnts_lim: i32,

    /// The initial restart limit. (default 100)
    pub restart_first: i32,
    /// The factor with which the restart limit is multiplied in each restart. (default 1.5)
    pub restart_inc: f64,
    /// The intitial limit for learnt clauses is a factor of the original clauses. (default 1 / 3)
    pub learntsize_factor: f64,
    /// The limit for learnt clauses is multiplied with this factor each restart. (default 1.1)
    pub learntsize_inc: f64,
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
            learntsize_factor: 1.0 / 3.0,
            learntsize_inc: 1.1,
            rnd_pol: false,
        }
    }
}

impl SolverOpts {
    /// Check that options are valid.
    pub fn check(&self) -> bool {
        (1f32 / THRESHOLD < self.var_decay && self.var_decay < 1.0)
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
