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

use std::cmp;
use std::f64;
use std::mem;
use std::collections::VecDeque;
use system::{cpu_time, mem_used_peak};
use {lbool, Lit, Var};
use intmap::{Comparator, Heap, HeapData, PartialComparator};
use clause::{CRef, ClauseAllocator, ClauseRef, DeletePred, LMap, LSet, OccLists, OccListsData,
             VMap};

#[derive(Debug)]
pub struct Solver {
    // Extra results: (read-only member variable)
    /// If problem is satisfiable, this vector contains the model (if any).
    pub model: Vec<lbool>,
    /// If problem is unsatisfiable (possibly under assumptions),
    /// this vector represent the final conflict clause expressed in the assumptions.
    conflict: LSet,

    // Mode of operation:
    verbosity: i32,
    var_decay: f64,
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

    learntsize_adjust_start_confl: i32,
    learntsize_adjust_inc: f64,

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

    // Solver state:
    /// List of problem clauses.
    clauses: Vec<CRef>,
    /// List of learnt clauses.
    learnts: Vec<CRef>,
    // /// Assignment stack; stores all assigments made in the order they were made.
    // v.trail: Vec<Lit>,
    // /// Separator indices for different decision levels in 'trail'.
    // v.trail_lim: Vec<i32>,
    /// Current set of assumptions provided to solve by the user.
    assumptions: Vec<Lit>,

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
    // v.vardata: VMap<VarData>,
    /// 'watches[lit]' is a list of constraints watching 'lit' (will go there if literal becomes true).
    watches_data: OccListsData<Lit, Watcher>,
    /// A priority queue of variables ordered with respect to the variable activity.
    order_heap_data: HeapData<Var>,
    /// If FALSE, the constraints are already unsatisfiable. No part of the solver state may be used!
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
    /// Set by 'search()'.
    progress_estimate: f64,
    /// Indicates whether possibly inefficient linear scan for satisfied clauses should be performed in 'simplify'.
    remove_satisfied: bool,
    /// Next variable to be created.
    next_var: Var,
    ca: ClauseAllocator,

    released_vars: Vec<Var>,
    free_vars: Vec<Var>,

    // Temporaries (to reduce allocation overhead). Each variable is prefixed by the method in which it is
    // used, exept 'seen' wich is used in several places.
    seen: VMap<Seen>,
    analyze_stack: Vec<ShrinkStackElem>,
    analyze_toclear: Vec<Lit>,
    add_tmp: Vec<Lit>,

    max_learnts: f64,
    learntsize_adjust_confl: f64,
    learntsize_adjust_cnt: i32,

    // Resource contraints:
    conflict_budget: i64,
    propagation_budget: i64,
    asynch_interrupt: bool,

    // Mode of operation:
    /// Allow a variable elimination step to grow by a number of clauses (default to zero).
    grow: i32,
    /// Variables are not eliminated if it produces a resolvent with a length above this limit.
    /// -1 means no limit.
    clause_lim: i32,
    /// Do not check if subsumption against a clause larger than this. -1 means no limit.
    subsumption_lim: i32,
    /// A different limit for when to issue a GC during simplification (Also see 'garbage_frac').
    simp_garbage_frac: f64,

    /// Shrink clauses by asymmetric branching.
    use_asymm: bool,
    /// Check if a clause is already implied. Prett costly, and subsumes subsumptions :)
    use_rcheck: bool,
    /// Perform variable elimination.
    use_elim: bool,
    /// Flag to indicate whether the user needs to look at the full model.
    extend_model: bool,

    // Statistics:
    merges: i32,
    asymm_lits: i32,
    eliminated_vars: i32,

    // Solver state:
    elimorder: i32,
    use_simplification: bool,
    /// Max variable at the point simplification was turned off.
    max_simp_var: Var,
    elimclauses: Vec<u32>,
    touched: VMap<bool>,
    occurs_data: OccListsData<Var, CRef>,
    n_occ: LMap<i32>,
    elim_heap_data: HeapData<Var>,
    subsumption_queue: VecDeque<CRef>,
    frozen: VMap<bool>,
    frozen_vars: Vec<Var>,
    eliminated: VMap<bool>,
    bwdsub_assigns: i32,
    n_touched: i32,

    // Temporaries:
    bwdsub_tmpunit: CRef,

    v: SolverV,
}

#[derive(Debug)]
struct SolverV {
    /// A heuristic measurement of the activity of a variable.
    activity: VMap<f64>,
    /// The current assignments.
    assigns: VMap<lbool>,
    /// Assignment stack; stores all assigments made in the order they were made.
    trail: Vec<Lit>,
    /// Separator indices for different decision levels in 'trail'.
    trail_lim: Vec<i32>,
    /// Stores reason and level for each variable.
    vardata: VMap<VarData>,
    /// Amount to bump next variable with.
    var_inc: f64,

    num_clauses: u64,
    num_learnts: u64,
    clauses_literals: u64,
    learnts_literals: u64,
}

impl Default for Solver {
    fn default() -> Self {
        Self::new(&SolverOpts::default())
    }
}

impl Solver {
    pub fn new(opts: &SolverOpts) -> Self {
        assert!(opts.check());
        let mut ca = ClauseAllocator::new();
        ca.extra_clause_field = true; // simp
        let bwdsub_tmpunit = ca.alloc(&[Lit::UNDEF]);
        Self {
            // Parameters (user settable):
            model: vec![],
            conflict: LSet::new(),
            verbosity: 0,
            var_decay: opts.var_decay,
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

            // Parameters (the rest):
            learntsize_factor: 1.0 / 3.0,
            learntsize_inc: 1.1,

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

            clauses: vec![],
            learnts: vec![],
            // v.trail: vec![],
            // v.trail_lim: vec![],
            assumptions: vec![],
            // v.activity: VMap::new(),
            // v.assigns: VMap::new(),
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
            remove_satisfied: false, // simp
            next_var: Var::from_idx(0),

            ca: ca,
            released_vars: vec![],
            free_vars: vec![],
            seen: VMap::new(),
            analyze_stack: vec![],
            analyze_toclear: vec![],
            add_tmp: vec![],
            max_learnts: 0.0,
            learntsize_adjust_confl: 0.0,
            learntsize_adjust_cnt: 0,

            // Resource constraints:
            conflict_budget: -1,
            propagation_budget: -1,
            asynch_interrupt: false,

            // Mode of operation:
            grow: opts.grow,
            clause_lim: opts.clause_lim,
            subsumption_lim: opts.subsumption_lim,
            simp_garbage_frac: opts.simp_garbage_frac,

            use_asymm: opts.use_asymm,
            use_rcheck: opts.use_rcheck,
            use_elim: opts.use_elim,
            extend_model: true,

            // Statistics:
            merges: 0,
            asymm_lits: 0,
            eliminated_vars: 0,

            // Solver state:
            elimorder: 0,
            use_simplification: true,
            max_simp_var: Var::from_idx(0),
            elimclauses: Vec::new(),
            touched: VMap::new(),
            occurs_data: OccListsData::new(),
            n_occ: LMap::new(),
            elim_heap_data: HeapData::new(),
            subsumption_queue: VecDeque::new(),
            frozen: VMap::new(),
            frozen_vars: Vec::new(),
            eliminated: VMap::new(),
            bwdsub_assigns: 0,
            n_touched: 0,

            // Temporaries:
            bwdsub_tmpunit: bwdsub_tmpunit,

            v: SolverV {
                activity: VMap::new(),
                assigns: VMap::new(),
                trail: vec![],
                trail_lim: vec![],
                vardata: VMap::new(),
                var_inc: 1.0,
                num_clauses: 0,
                num_learnts: 0,
                clauses_literals: 0,
                learnts_literals: 0,
            },
        }
    }

    pub fn set_verbosity(&mut self, verbosity: i32) {
        debug_assert!(0 <= verbosity && verbosity <= 2);
        self.verbosity = verbosity;
    }
    pub fn num_clauses(&self) -> u32 {
        self.v.num_clauses as u32
    }
    pub fn num_learnts(&self) -> u32 {
        self.v.num_learnts as u32
    }
    pub fn verbosity(&self) -> i32 {
        self.verbosity
    }

    fn var_decay_activity(&mut self) {
        self.v.var_inc *= 1.0 / self.var_decay;
    }

    fn cla_decay_activity(&mut self) {
        self.cla_inc *= 1.0 / self.clause_decay;
    }

    fn cla_bump_activity(&mut self, cr: CRef) {
        let new_activity = {
            let mut c = self.ca.get_mut(cr);
            let r = c.activity() + self.cla_inc as f32;
            c.set_activity(r);
            r
        };
        if new_activity > 1e20 {
            // Rescale:
            for &learnt in &self.learnts {
                let mut c = self.ca.get_mut(learnt);
                let r = c.activity() * 1e-20;
                c.set_activity(r);
            }
            self.cla_inc *= 1e-20;
        }
    }

    pub fn set_decision_var(&mut self, v: Var, b: bool) {
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

    fn pick_branch_lit(&mut self) -> Lit {
        let mut next = Var::UNDEF;

        // Random decision:
        if drand(&mut self.random_seed) < self.random_var_freq && !self.order_heap().is_empty() {
            let idx_tmp = irand(&mut self.random_seed, self.order_heap_data.len() as i32) as usize;
            next = self.order_heap_data[idx_tmp];
            if self.v.value(next) == lbool::UNDEF && self.decision[next] {
                self.rnd_decisions += 1;
            }
        }

        // Activity based decision:
        while next == Var::UNDEF || self.v.value(next) != lbool::UNDEF || !self.decision[next] {
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
            Lit::new(next, drand(&mut self.random_seed) < 0.5)
        } else {
            Lit::new(next, self.polarity[next])
        }
    }

    /// Begins a new decision level.
    fn new_decision_level(&mut self) {
        // eprintln!(
        //     "decision_level {} -> {}",
        //     self.v.trail_lim.len(),
        //     self.v.trail_lim.len() + 1
        // );
        self.v.trail_lim.push(self.v.trail.len() as i32);
    }

    pub fn num_vars(&self) -> u32 {
        self.next_var.idx()
    }

    /// Print some current statistics to standard output.
    pub fn print_stats(&self) {
        let cpu_time = cpu_time();
        let mem_used = mem_used_peak();
        println!("restarts              : {}", self.starts);
        println!(
            "conflicts             : {:<12}   ({:.0} /sec)",
            self.conflicts,
            self.conflicts as f64 / cpu_time
        );
        println!(
            "decisions             : {:<12}   ({:4.2} % random) ({:.0} /sec)",
            self.decisions,
            self.rnd_decisions as f32 * 100.0 / self.decisions as f32,
            self.decisions as f64 / cpu_time as f64
        );
        println!(
            "propagations          : {:<12}   ({:.0} /sec)",
            self.propagations,
            self.propagations as f64 / cpu_time
        );
        println!(
            "conflict literals     : {:<12}   ({:4.2} % deleted)",
            self.tot_literals,
            (self.max_literals - self.tot_literals) as f64 * 100.0 / self.max_literals as f64
        );
        if mem_used != 0.0 {
            println!("Memory used           : {:.2} MB", mem_used);
        }
        println!("CPU time              : {} s", cpu_time);
    }

    pub fn new_var(&mut self, upol: lbool, dvar: bool) -> Var {
        let v = self.core_new_var(upol, dvar);

        self.frozen.insert_default(v, false);
        self.eliminated.insert_default(v, false);

        if self.use_simplification {
            self.n_occ.insert_default(Lit::new(v, false), 0);
            self.n_occ.insert_default(Lit::new(v, true), 0);
            self.occurs_data.init(v);
            self.touched.insert_default(v, false);
            self.elim_heap().insert(v);
        }
        return v;
    }

    pub fn new_var_default(&mut self) -> Var {
        self.new_var(lbool::UNDEF, true)
    }

    /// Creates a new SAT variable in the solver. If 'decision' is cleared, variable will not be
    /// used as a decision variable (NOTE! This has effects on the meaning of a SATISFIABLE result).
    pub fn core_new_var(&mut self, upol: lbool, dvar: bool) -> Var {
        let v = self.free_vars.pop().unwrap_or_else(|| {
            let v = self.next_var;
            self.next_var = Var::from_idx(self.next_var.idx() + 1);
            v
        });
        self.watches().init(Lit::new(v, false));
        self.watches().init(Lit::new(v, true));
        self.v.assigns.insert_default(v, lbool::UNDEF);
        self.v
            .vardata
            .insert_default(v, VarData::new(CRef::UNDEF, 0));
        if self.rnd_init_act {
            self.v
                .activity
                .insert_default(v, drand(&mut self.random_seed) * 0.00001);
        } else {
            self.v.activity.insert_default(v, 0.0);
        }
        self.seen.insert_default(v, Seen::UNDEF);
        self.polarity.insert_default(v, true);
        self.user_pol.insert_default(v, upol);
        self.decision.reserve_default(v);
        let len = self.v.trail.len();
        self.v.trail.reserve(v.idx() as usize + 1 - len);
        self.set_decision_var(v, dvar);
        v
    }

    pub fn core_new_var_default(&mut self) -> Var {
        self.core_new_var(lbool::UNDEF, true)
    }

    pub fn add_clause_reuse(&mut self, clause: &mut Vec<Lit>) -> bool {
        unimplemented!();
    }

    pub fn core_add_clause_reuse(&mut self, clause: &mut Vec<Lit>) -> bool {
        debug_assert_eq!(self.v.decision_level(), 0);
        if !self.ok {
            return false;
        }
        clause.sort();
        let mut last_lit = Lit::UNDEF;
        let mut j = 0;
        for i in 0..clause.len() {
            let value = self.v.value_lit(clause[i]);
            if value == lbool::TRUE || clause[i] == !last_lit {
                return true;
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
            self.v.unchecked_enqueue(clause[0], CRef::UNDEF);
        } else {
            let cr = self.ca.alloc_with_learnt(&clause, false);
            self.clauses.push(cr);
            self.attach_clause(cr);
        }

        true
    }

    /// Simplify the clause database according to the current top-level assigment. Currently, the only
    /// thing done here is the removal of satisfied clauses, but more things can be put here.
    pub fn simplify(&mut self) -> bool {
        debug_assert_eq!(self.v.decision_level(), 0);

        if !self.ok || self.propagate() != CRef::UNDEF {
            self.ok = false;
            return false;
        }

        if self.v.num_assigns() as i32 == self.simp_db_assigns || self.simp_db_props > 0 {
            return true;
        }

        // Remove satisfied clauses:
        self.remove_satisfied(true);
        if self.remove_satisfied {
            // Can be turned off.
            self.remove_satisfied(false);

            // TODO: what todo in if 'remove_satisfied' is false?

            // Remove all released variables from the trail:
            for &rvar in &self.released_vars {
                debug_assert_eq!(self.seen[rvar], Seen::UNDEF);
                self.seen[rvar] = Seen::SOURCE;
            }

            {
                let seen = &self.seen;
                self.v.trail.retain(|&lit| !seen[lit.var()].is_seen());
            }
            // eprintln!(
            //     "trail.size()= {}, qhead = {}",
            //     self.v.trail.len(),
            //     self.qhead
            // );
            self.qhead = self.v.trail.len() as i32;

            for &rvar in &self.released_vars {
                self.seen[rvar] = Seen::UNDEF;
            }

            // Released variables are now ready to be reused:
            self.free_vars.extend(self.released_vars.drain(..));
        }
        self.check_garbage();
        self.rebuild_order_heap();

        self.simp_db_assigns = self.v.num_assigns() as i32;
        // (shouldn't depend on stats really, but it will do for now)
        self.simp_db_props = (self.v.clauses_literals + self.v.learnts_literals) as i64;

        true
    }

    pub fn solve_limited(&mut self, assumps: &[Lit]) -> lbool {
        unimplemented!();
    }

    /// Search for a model that respects a given set of assumptions (With resource constraints).
    pub fn core_solve_limited(&mut self, assumps: &[Lit]) -> lbool {
        self.assumptions.clear();
        self.assumptions.extend_from_slice(assumps);
        self.core_solve_internal()
    }

    /// Search for a model the specified number of conflicts.
    /// NOTE! Use negative value for 'nof_conflicts' indicate infinity.
    ///
    /// # Output:
    ///
    /// 'l_True' if a partial assigment that is consistent with respect to the clauseset is found. If
    /// all variables are decision variables, this means that the clause set is satisfiable. 'l_False'
    /// if the clause set is unsatisfiable. 'l_Undef' if the bound on number of conflicts is reached.
    fn search(&mut self, nof_conflicts: i32) -> lbool {
        debug_assert!(self.ok);
        let mut conflict_c = 0;
        let mut learnt_clause: Vec<Lit> = vec![];
        self.starts += 1;

        loop {
            let confl = self.propagate();
            if confl != CRef::UNDEF {
                // CONFLICT
                self.conflicts += 1;
                conflict_c += 1;
                if self.v.decision_level() == 0 {
                    return lbool::FALSE;
                }

                learnt_clause.clear();
                let backtrack_level = self.analyze(confl, &mut learnt_clause);
                self.cancel_until(backtrack_level as u32);

                if learnt_clause.len() == 1 {
                    self.v.unchecked_enqueue(learnt_clause[0], CRef::UNDEF);
                } else {
                    let cr = self.ca.alloc_with_learnt(&learnt_clause, true);
                    self.learnts.push(cr);
                    self.attach_clause(cr);
                    self.cla_bump_activity(cr);
                    self.v.unchecked_enqueue(learnt_clause[0], cr);
                }

                self.var_decay_activity();
                self.cla_decay_activity();

                self.learntsize_adjust_cnt -= 1;
                if self.learntsize_adjust_cnt == 0 {
                    self.learntsize_adjust_confl *= self.learntsize_adjust_inc;
                    self.learntsize_adjust_cnt = self.learntsize_adjust_confl as i32;
                    self.max_learnts *= self.learntsize_inc;

                    if self.verbosity >= 1 {
                        let trail_lim_head = self.v
                            .trail_lim
                            .first()
                            .cloned()
                            .unwrap_or(self.v.trail.len() as i32);
                        println!(
                            "| {:9} | {:7} {:8} {:8} | {:8} {:8} {:6.0} | {:6.3} % |",
                            self.conflicts as i32,
                            self.dec_vars as i32 - trail_lim_head,
                            self.num_clauses(),
                            self.v.clauses_literals as i32,
                            self.max_learnts as i32,
                            self.num_learnts(),
                            self.v.learnts_literals as f64 / self.num_learnts() as f64,
                            self.progress_estimate() * 100.0
                        );
                    }
                }
            } else {
                // NO CONFLICT
                if (nof_conflicts >= 0 && conflict_c >= nof_conflicts) || !self.within_budget() {
                    // Reached bound on number of conflicts:
                    self.progress_estimate = self.progress_estimate();
                    self.cancel_until(0);
                    return lbool::UNDEF;
                }

                // Simplify the set of problem clauses:
                if self.v.decision_level() == 0 && !self.simplify() {
                    return lbool::FALSE;
                }

                if self.learnts.len() as f64 - self.v.num_assigns() as f64 >= self.max_learnts {
                    // Reduce the set of learnt clauses:
                    self.reduce_db();
                }

                let mut next = Lit::UNDEF;
                while (self.v.decision_level() as usize) < self.assumptions.len() {
                    // Perform user provided assumption:
                    let p = self.assumptions[self.v.decision_level() as usize];
                    if self.v.value_lit(p) == lbool::TRUE {
                        // Dummy decision level:
                        self.new_decision_level();
                    } else if self.v.value_lit(p) == lbool::FALSE {
                        let mut conflict = mem::replace(&mut self.conflict, LSet::new());
                        self.analyze_final(!p, &mut conflict);
                        self.conflict = conflict;
                        return lbool::FALSE;
                    } else {
                        next = p;
                        break;
                    }
                }

                if next == Lit::UNDEF {
                    // New variable decision:
                    self.decisions += 1;
                    next = self.pick_branch_lit();

                    if next == Lit::UNDEF {
                        // Model found:
                        return lbool::TRUE;
                    }
                }

                // Increase decision level and enqueue 'next'
                self.new_decision_level();
                // eprintln!("assumption: {:?}", next);
                self.v.unchecked_enqueue(next, CRef::UNDEF);
            }
        }
    }

    fn solve_internal(&mut self) -> lbool {
        unimplemented!();
    }

    // NOTE: assumptions passed in member-variable 'assumptions'.
    /// Main solve method (assumptions given in 'assumptions').
    fn core_solve_internal(&mut self) -> lbool {
        self.model.clear();
        self.conflict.clear();
        if !self.ok {
            return lbool::FALSE;
        }

        self.solves += 1;

        self.max_learnts = self.num_clauses() as f64 * self.learntsize_factor;
        if self.max_learnts < self.min_learnts_lim as f64 {
            self.max_learnts = self.min_learnts_lim as f64;
        }

        self.learntsize_adjust_confl = self.learntsize_adjust_start_confl as f64;
        self.learntsize_adjust_cnt = self.learntsize_adjust_confl as i32;
        let mut status = lbool::UNDEF;

        if self.verbosity >= 1 {
            println!(
                "============================[ Search Statistics ]=============================="
            );
            println!(
                "| Conflicts |          ORIGINAL         |          LEARNT          | Progress |"
            );
            println!(
                "|           |    Vars  Clauses Literals |    Limit  Clauses Lit/Cl |          |"
            );
            println!(
                "==============================================================================="
            );
        }

        // Search:
        let mut curr_restarts: i32 = 0;
        while status == lbool::UNDEF {
            let rest_base = if self.luby_restart {
                luby(self.restart_inc, curr_restarts)
            } else {
                f64::powi(self.restart_inc, curr_restarts)
            };
            let nof_clauses = (rest_base * self.restart_first as f64) as i32;
            status = self.search(nof_clauses);
            if !self.within_budget() {
                break;
            }
            curr_restarts += 1;
        }

        if self.verbosity >= 1 {
            println!(
                "==============================================================================="
            );
        }

        if status == lbool::TRUE {
            // Extend & copy model:
            let num_vars = self.num_vars();
            self.model.resize(num_vars as usize, lbool::UNDEF);
            for i in 0..num_vars {
                self.model[i as usize] = self.v.value(Var::from_idx(i));
            }
        } else if status == lbool::FALSE && self.conflict.len() == 0 {
            self.ok = false;
        }

        self.cancel_until(0);
        status
    }

    /// Remove half of the learnt clauses, minus the clauses locked by the current assignment. Locked
    /// clauses are clauses that are reason to some assignment. Binary clauses are never removed.
    fn reduce_db(&mut self) {
        let extra_lim = self.cla_inc / self.learnts.len() as f64; // Remove any clause below this activity

        {
            let ca = &self.ca;
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
        // and clauses with activity smaller than 'extra_lim':
        let mut j = 0;
        for i in 0..self.learnts.len() {
            let cr = self.learnts[i];
            let cond = {
                let c = self.ca.get_ref(cr);
                c.size() > 2 && !self.v.locked(&self.ca, c)
                    && (i < self.learnts.len() / 2 || (c.activity() as f64) < extra_lim)
            };
            if cond {
                self.v
                    .core_remove_clause(&mut self.ca, &mut self.watches_data, cr);
            } else {
                self.learnts[j] = cr;
                j += 1;
            }
        }
        // self.learnts.resize_default(j);
        self.learnts.resize(j, CRef::UNDEF);
        self.check_garbage();
    }

    /// Shrink 'cs' to contain only non-satisfied clauses.
    // fn remove_satisfied(&mut self, cs: &mut Vec<CRef>) {
    fn remove_satisfied(&mut self, shrink_learnts: bool) {
        let cs: &mut Vec<CRef> = if shrink_learnts {
            &mut self.learnts
        } else {
            &mut self.clauses
        };
        let ca = &mut self.ca;
        let watches_data = &mut self.watches_data;
        let self_v = &mut self.v;
        cs.retain(|&cr| {
            let satisfied = self_v.satisfied(ca.get_ref(cr));
            if satisfied {
                self_v.core_remove_clause(ca, watches_data, cr)
            } else {
                let amount = {
                    let mut c = ca.get_mut(cr);
                    // Trim clause:
                    debug_assert_eq!(self_v.value_lit(c[0]), lbool::UNDEF);
                    debug_assert_eq!(self_v.value_lit(c[1]), lbool::UNDEF);
                    let mut k = 2;
                    let orig_size = c.size();
                    let mut end = c.size();
                    while k < end {
                        if self_v.value_lit(c[k]) == lbool::FALSE {
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
                ca.free_amount(amount);
            }
            !satisfied
        });
    }

    fn rebuild_order_heap(&mut self) {
        let mut vs = vec![];
        for v in (0..self.num_vars()).map(Var::from_idx) {
            if self.decision[v] && self.v.value(v) == lbool::UNDEF {
                vs.push(v);
            }
        }
        self.order_heap().build(&vs);
    }

    fn attach_clause(&mut self, cr: CRef) {
        let (c0, c1, learnt, size) = {
            let c = self.ca.get_ref(cr);
            debug_assert!(c.size() > 1);
            (c[0], c[1], c.learnt(), c.size())
        };
        self.watches()[!c0].push(Watcher::new(cr, c1));
        self.watches()[!c1].push(Watcher::new(cr, c0));
        if learnt {
            self.v.num_learnts += 1;
            self.v.learnts_literals += size as u64;
        } else {
            self.v.num_clauses += 1;
            self.v.clauses_literals += size as u64;
        }
    }

    /// Revert to the state at given level (keeping all assignment at 'level' but not beyond).
    fn cancel_until(&mut self, level: u32) {
        if self.v.decision_level() > level {
            let trail_lim_last = *self.v.trail_lim.last().expect("trail_lim is empty") as usize;
            let trail_lim_level = self.v.trail_lim[level as usize] as usize;
            for c in (trail_lim_level..self.v.trail.len()).rev() {
                let x = self.v.trail[c].var();
                self.v.assigns[x] = lbool::UNDEF;
                if self.phase_saving > 1 || (self.phase_saving == 1 && c > trail_lim_last) {
                    self.polarity[x] = self.v.trail[c].sign();
                }
                self.insert_var_order(x);
            }
            self.qhead = trail_lim_level as i32;
            self.v.trail.resize(trail_lim_level, Lit::UNDEF);
            // eprintln!("decision_level {} -> {}", self.v.trail_lim.len(), level);
            self.v.trail_lim.resize(level as usize, 0);
        }
    }

    /// Analyze conflict and produce a reason clause.
    ///
    /// # Pre-conditions:
    ///
    /// - `out_learnt` is assumed to be cleared.
    /// - Current decision level must be greater than root level.
    ///
    /// # Post-conditions:
    ///
    /// - `btlevel` is returned.
    /// - `out_learnt[0]` is the asserting literal at level `btlevel`.
    /// - If out_learnt.size() > 1 then `out_learnt[1]` has the greatest decision level of the
    ///   rest of literals. There may be others from the same level though.
    fn analyze(&mut self, mut confl: CRef, out_learnt: &mut Vec<Lit>) -> i32 {
        let mut path_c = 0;
        let mut p = Lit::UNDEF;

        // Generate conflict clause:
        //
        out_learnt.push(Lit::from_idx(0)); // (leave room for the asserting literal)
        let mut index = self.v.trail.len();

        loop {
            debug_assert_ne!(confl, CRef::UNDEF); // (otherwise should be UIP)
            if self.ca.get_ref(confl).learnt() {
                self.cla_bump_activity(confl);
            }

            let c = self.ca.get_mut(confl);

            let mut iter = c.iter();
            if p != Lit::UNDEF {
                iter.next();
            }
            for &q in iter {
                if !self.seen[q.var()].is_seen() && self.v.level(q.var()) > 0 {
                    self.v.var_bump_activity(&mut self.order_heap_data, q.var());
                    self.seen[q.var()] = Seen::SOURCE;
                    if self.v.level(q.var()) >= self.v.decision_level() as i32 {
                        path_c += 1;
                    } else {
                        out_learnt.push(q);
                    }
                }
            }

            // Select next clause to look at:
            while !self.seen[self.v.trail[index - 1].var()].is_seen() {
                index -= 1;
            }
            p = self.v.trail[index - 1];
            index -= 1;
            confl = self.v.reason(p.var());
            self.seen[p.var()] = Seen::UNDEF;
            path_c -= 1;

            if path_c <= 0 {
                break;
            }
        }
        out_learnt[0] = !p;

        // Simplify conflict clause:
        //
        self.analyze_toclear.clear();
        self.analyze_toclear.extend_from_slice(&out_learnt);
        let new_size = if self.ccmin_mode == 2 {
            let mut j = 1;
            for i in 1..out_learnt.len() {
                let lit = out_learnt[i];
                if self.v.reason(lit.var()) == CRef::UNDEF || !self.lit_redundant(lit) {
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
                let reason = self.v.reason(x);

                let mut retain = true;
                if reason == CRef::UNDEF {
                    retain = true;
                } else {
                    let c = self.ca.get_ref(reason);
                    for k in 1..c.size() {
                        let v = c[k].var();
                        if !self.seen[v].is_seen() && self.v.level(v) > 0 {
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

        self.max_literals += out_learnt.len() as u64;
        self.tot_literals += new_size as u64;
        out_learnt.resize(new_size, Lit::UNDEF);

        // Find correct backtrack level:
        //
        let btlevel = if new_size == 1 {
            0
        } else {
            let mut max_i = 1;
            let mut max_level = self.v.level(out_learnt[max_i].var());
            // Find the first literal assigned at the next-highest level:
            for i in 2..out_learnt.len() {
                let level = self.v.level(out_learnt[i].var());
                if level > max_level {
                    max_i = i;
                    max_level = level;
                }
            }
            // Swap-in this literal at index 1:
            let p = out_learnt[max_i];
            out_learnt[max_i] = out_learnt[1];
            out_learnt[1] = p;
            self.v.level(p.var())
        };

        for &lit in &self.analyze_toclear {
            self.seen[lit.var()] = Seen::UNDEF; // ('seen[]' is now cleared)
        }
        btlevel
    }

    // COULD THIS BE IMPLEMENTED BY THE ORDINARIY "analyze" BY SOME REASONABLE GENERALIZATION?
    /// Specialized analysis procedure to express the final conflict in terms of assumptions.
    /// Calculates the (possibly empty) set of assumptions that led to the assignment of 'p', and
    /// stores the result in 'out_conflict'.
    fn analyze_final(&mut self, p: Lit, out_conflict: &mut LSet) {
        out_conflict.clear();
        out_conflict.insert(p);

        if self.v.decision_level() == 0 {
            return;
        }

        self.seen[p.var()] = Seen::SOURCE;

        for &lit in &self.v.trail[self.v.trail_lim[0] as usize..] {
            let x = lit.var();
            if self.seen[x].is_seen() {
                let reason = self.v.reason(x);
                if reason == CRef::UNDEF {
                    debug_assert!(self.v.level(x) > 0);
                    out_conflict.insert(!lit);
                } else {
                    let c = self.ca.get_mut(reason);
                    for j in 1..c.size() {
                        if self.v.level(c[j].var()) > 0 {
                            self.seen[c[j].var()] = Seen::SOURCE;
                        }
                    }
                }
                self.seen[x] = Seen::UNDEF;
            }
        }

        self.seen[p.var()] = Seen::UNDEF;
    }

    // Check if 'p' can be removed from a conflict clause.
    fn lit_redundant(&mut self, mut p: Lit) -> bool {
        debug_assert!(self.seen[p.var()] == Seen::UNDEF || self.seen[p.var()] == Seen::SOURCE);
        debug_assert!(self.v.reason(p.var()) != CRef::UNDEF);

        let mut cr = self.v.reason(p.var());
        let stack = &mut self.analyze_stack;
        stack.clear();

        let mut i: u32 = 1;
        loop {
            let c = self.ca.get_mut(cr);
            if i < c.size() {
                // Checking 'p'-parents 'l':
                let l: Lit = c[i];

                // Variable at level 0 or previously removable:
                if self.v.level(l.var()) == 0 || self.seen[l.var()] == Seen::SOURCE
                    || self.seen[l.var()] == Seen::REMOVABLE
                {
                    i += 1;
                    continue;
                }

                // Check variable can not be removed for some local reason:
                if self.v.reason(l.var()) == CRef::UNDEF || self.seen[l.var()] == Seen::FAILED {
                    stack.push(ShrinkStackElem::new(0, p));
                    for elem in stack.iter() {
                        if self.seen[elem.l.var()] == Seen::UNDEF {
                            self.seen[elem.l.var()] = Seen::FAILED;
                            self.analyze_toclear.push(elem.l);
                        }
                    }

                    return false;
                }

                // Recursively check 'l':
                stack.push(ShrinkStackElem::new(i, p));
                i = 0;
                p = l;
                cr = self.v.reason(p.var());
            } else {
                // Finished with current element 'p' and reason 'c':
                if self.seen[p.var()] == Seen::UNDEF {
                    self.seen[p.var()] = Seen::REMOVABLE;
                    self.analyze_toclear.push(p);
                }

                // Terminate with success if stack is empty:
                if stack.len() == 0 {
                    break;
                }

                // Continue with top element on stack:
                let last = stack.pop().expect("stack is empty");
                i = last.i;
                p = last.l;
                cr = self.v.reason(p.var());
            }
            i += 1;
        }

        true
    }

    /// Propagates all enqueued facts. If a conflict arises, the conflicting clause is returned,
    /// otherwise CRef_Undef.
    ///
    /// # Post-conditions:
    ///
    /// - the propagation queue is empty, even if there was a conflict.
    fn propagate(&mut self) -> CRef {
        let mut confl = CRef::UNDEF;
        let mut num_props: u32 = 0;

        while (self.qhead as usize) < self.v.trail.len() {
            // 'p' is enqueued fact to propagate.
            let p = self.v.trail[self.qhead as usize];
            // eprintln!("propagating trail[{}] = {:?}", self.qhead, p);
            self.qhead += 1;
            let watches_data_ptr: *mut OccListsData<_, _> = &mut self.watches_data;
            // let ws = self.watches().lookup_mut(p);
            let ws = self.watches_data
                .lookup_mut_pred(p, &WatcherDeleted { ca: &self.ca });
            // eprintln!("watcher of {:?} = {:?}", p, ws);
            let mut i: usize = 0;
            let mut j: usize = 0;
            let end: usize = ws.len();
            num_props += 1;
            'clauses: while i < end {
                // Try to avoid inspecting the clause:
                let blocker = ws[i].blocker;
                if self.v.value_lit(blocker) == lbool::TRUE {
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
                if first != blocker && self.v.value_lit(first) == lbool::TRUE {
                    ws[j] = w;
                    j += 1;
                    continue;
                }

                // Look for new watch:
                for k in 2..c.size() {
                    if self.v.value_lit(c[k]) != lbool::FALSE {
                        c[1] = c[k];
                        c[k] = false_lit;

                        // self.watches()[!c[1]].push(w);
                        assert_ne!(!c[1], p);
                        unsafe { &mut (*watches_data_ptr)[!c[1]] }.push(w);
                        continue 'clauses;
                    }
                }

                // Did not find watch -- clause is unit under assignment:
                ws[j] = w;
                j += 1;
                if self.v.value_lit(first) == lbool::FALSE {
                    // eprintln!("propagation: conflict at {:?}", first);
                    confl = cr;
                    self.qhead = self.v.trail.len() as i32;
                    // Copy the remaining watches:
                    while i < end {
                        ws[j] = ws[i];
                        j += 1;
                        i += 1;
                    }
                } else {
                    // eprintln!("propagation: got {:?}", first);
                    self.v.unchecked_enqueue(first, cr);
                }
            }
            let dummy = Watcher {
                cref: CRef::UNDEF,
                blocker: Lit::UNDEF,
            };
            ws.resize(j, dummy);
        }
        self.propagations += num_props as u64;
        self.simp_db_props -= num_props as i64;

        confl
    }

    fn check_garbage(&mut self) {
        if self.ca.wasted() as f64 > self.ca.len() as f64 * self.garbage_frac {
            self.garbage_collect();
        }
    }

    fn garbage_collect(&mut self) {
        // Initialize the next region to a size corresponding to the estimated utilization degree. This
        // is not precise but should avoid some unnecessary reallocations for the new region:
        let mut to = ClauseAllocator::with_start_cap(self.ca.len() - self.ca.wasted());

        self.core_reloc_all(&mut to);
        if self.verbosity >= 2 {
            println!(
                "|  Garbage collection:   {:12} bytes => {:12} bytes             |",
                self.ca.len() * ClauseAllocator::UNIT_SIZE,
                to.len() * ClauseAllocator::UNIT_SIZE
            );
        }
        self.ca = to;
    }

    fn progress_estimate(&self) -> f64 {
        let mut progress = 0.0;
        let f = 1.0 / self.num_vars() as f64;

        for i in 0..self.v.decision_level() + 1 {
            let beg: i32 = if i == 0 {
                0
            } else {
                self.v.trail_lim[i as usize - 1]
            };
            let end: i32 = if i == self.v.decision_level() {
                self.v.trail.len() as i32
            } else {
                self.v.trail_lim[i as usize]
            };
            progress += f64::powi(f, i as i32) * (end - beg) as f64;
        }

        progress / self.num_vars() as f64
    }

    fn within_budget(&self) -> bool {
        !self.asynch_interrupt
            && (self.conflict_budget < 0 || self.conflicts < self.conflict_budget as u64)
            && (self.propagation_budget < 0 || self.propagations < self.propagation_budget as u64)
    }

    fn reloc_all(&mut self, to: &mut ClauseAllocator) {
        unimplemented!();
    }

    fn core_reloc_all(&mut self, to: &mut ClauseAllocator) {
        macro_rules! is_removed {
            ($ca:expr, $cr:expr) => {
                $ca.get_ref($cr).mark() == 1
            };
        }
        // All watchers:
        //
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
        //
        for &lit in &self.v.trail {
            let v = lit.var();

            // Note: it is not safe to call 'locked()' on a relocated clause. This is why we keep
            // 'dangling' reasons here. It is safe and does not hurt.
            let reason = self.v.reason(v);
            if reason != CRef::UNDEF {
                let cond = {
                    let c = self.ca.get_ref(reason);
                    c.reloced() || self.v.locked(&self.ca, c)
                };
                if cond {
                    debug_assert!(!is_removed!(self.ca, reason));
                    self.ca.reloc(&mut self.v.vardata[v].reason, to);
                }
            }
        }

        // All learnt:
        //
        {
            // let ca = &mut self.ca;
            // self.learnts.drain_filter(|cr| {
            //     if !is_removed!(ca, *cr) {
            //         ca.reloc(cr, to);
            //         false
            //     } else {
            //         true
            //     }
            // }).count();
            let mut j = 0;
            for i in 0..self.learnts.len() {
                let mut cr = self.learnts[i];
                if !is_removed!(self.ca, cr) {
                    self.ca.reloc(&mut cr, to);
                    self.learnts[j] = cr;
                    j += 1;
                }
            }
            self.learnts.resize(j, CRef::UNDEF);
        }

        // All original:
        //
        {
            // let ca = &mut self.ca;
            // self.clauses.drain_filter(|cr| {
            //     if !is_removed!(ca, *cr) {
            //         ca.reloc(cr, to);
            //         false
            //     } else {
            //         true
            //     }
            // }).count();
            let mut j = 0;
            for i in 0..self.clauses.len() {
                let mut cr = self.clauses[i];
                if !is_removed!(self.ca, cr) {
                    self.ca.reloc(&mut cr, to);
                    self.clauses[j] = cr;
                    j += 1;
                }
            }
            self.clauses.resize(j, CRef::UNDEF);
        }
    }

    fn order_heap(&mut self) -> Heap<Var, VarOrder> {
        self.order_heap_data.promote(VarOrder {
            activity: &self.v.activity,
        })
    }
    fn watches(&mut self) -> OccLists<Lit, Watcher, WatcherDeleted> {
        self.watches_data.promote(WatcherDeleted { ca: &self.ca })
    }

    fn occurs(&mut self) -> OccLists<Var, CRef, ClauseDeleted> {
        self.occurs_data.promote(ClauseDeleted { ca: &self.ca })
    }

    fn elim_heap(&mut self) -> Heap<Var, ElimOrder> {
        self.elim_heap_data
            .promote(ElimOrder { n_occ: &self.n_occ })
    }
}

impl SolverV {
    pub fn num_assigns(&self) -> u32 {
        self.trail.len() as u32
    }

    pub fn value(&self, x: Var) -> lbool {
        self.assigns[x]
    }
    pub fn value_lit(&self, x: Lit) -> lbool {
        self.assigns[x.var()] ^ x.sign()
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

    /// Detach a clause to watcher lists.
    fn detach_clause_strict(
        &mut self,
        ca: &mut ClauseAllocator,
        watches_data: &mut OccListsData<Lit, Watcher>,
        cr: CRef,
        strict: bool,
    ) {
        let (c0, c1, csize, clearnt) = {
            let c = ca.get_ref(cr);
            (c[0], c[1], c.size(), c.learnt())
        };
        debug_assert!(csize > 1);

        let mut watches = watches_data.promote(WatcherDeleted { ca });

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
    fn detach_clause(
        &mut self,
        ca: &mut ClauseAllocator,
        watches_data: &mut OccListsData<Lit, Watcher>,
        cr: CRef,
    ) {
        self.detach_clause_strict(ca, watches_data, cr, false)
    }

    /// Detach and free a clause.
    fn remove_clause(
        &mut self,
        ca: &mut ClauseAllocator,
        watches_data: &mut OccListsData<Lit, Watcher>,
        cr: CRef,
    ) {
        unimplemented!();
    }

    /// Detach and free a clause.
    fn core_remove_clause(
        &mut self,
        ca: &mut ClauseAllocator,
        watches_data: &mut OccListsData<Lit, Watcher>,
        cr: CRef,
    ) {
        self.detach_clause(ca, watches_data, cr);
        {
            let c = ca.get_ref(cr);
            // Don't leave pointers to free'd memory!
            if self.locked(ca, c) {
                self.vardata[c[0].var()].reason = CRef::UNDEF;
            }
        }
        ca.get_mut(cr).set_mark(1);
        ca.free(cr);
    }

    pub fn satisfied(&self, c: ClauseRef) -> bool {
        c.iter().any(|&lit| self.value_lit(lit) == lbool::TRUE)
    }

    pub fn decision_level(&self) -> u32 {
        self.trail_lim.len() as u32
    }

    fn reason(&self, x: Var) -> CRef {
        self.vardata[x].reason
    }

    fn level(&self, x: Var) -> i32 {
        self.vardata[x].level
    }

    fn unchecked_enqueue(&mut self, p: Lit, from: CRef) {
        debug_assert_eq!(self.value_lit(p), lbool::UNDEF);
        self.assigns[p.var()] = lbool::new(!p.sign());
        self.vardata[p.var()] = VarData::new(from, self.decision_level() as i32);
        self.trail.push(p);
    }

    /// Returns TRUE if a clause is a reason for some implication in the current state.
    fn locked(&self, ca: &ClauseAllocator, c: ClauseRef) -> bool {
        let reason = self.reason(c[0].var());
        self.value_lit(c[0]) == lbool::TRUE && reason != CRef::UNDEF && ca.get_ref(reason) == c
    }
    // inline bool     Solver::locked          (const Clause& c) const { return value(c[0]) == l_True && reason(var(c[0])) != CRef_Undef && ca.lea(reason(var(c[0]))) == &c; }
}

#[derive(Debug, Clone, Copy)]
struct VarData {
    reason: CRef,
    level: i32,
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
    fn new(reason: CRef, level: i32) -> Self {
        Self { reason, level }
    }
}

#[derive(Debug, Clone, Copy)]
struct Watcher {
    cref: CRef,
    blocker: Lit,
}

impl Watcher {
    fn new(cref: CRef, blocker: Lit) -> Self {
        Self { cref, blocker }
    }
}

impl PartialEq for Watcher {
    fn eq(&self, rhs: &Self) -> bool {
        self.cref == rhs.cref
    }
}
impl Eq for Watcher {}

struct VarOrder<'a> {
    activity: &'a VMap<f64>,
}

impl<'a> PartialComparator<Var> for VarOrder<'a> {
    fn partial_cmp(&self, lhs: &Var, rhs: &Var) -> Option<cmp::Ordering> {
        Some(self.cmp(lhs, rhs))
    }
}
impl<'a> Comparator<Var> for VarOrder<'a> {
    fn cmp(&self, lhs: &Var, rhs: &Var) -> cmp::Ordering {
        PartialOrd::partial_cmp(&self.activity[*rhs], &self.activity[*lhs]).expect("NaN activity")
    }
}

struct WatcherDeleted<'a> {
    ca: &'a ClauseAllocator,
}

impl<'a> DeletePred<Watcher> for WatcherDeleted<'a> {
    fn deleted(&self, w: &Watcher) -> bool {
        self.ca.get_ref(w.cref).mark() == 1
    }
}

struct ClauseDeleted<'a> {
    ca: &'a ClauseAllocator,
}

impl<'a> DeletePred<CRef> for ClauseDeleted<'a> {
    fn deleted(&self, cr: &CRef) -> bool {
        self.ca.get_ref(*cr).mark() == 1
    }
}

struct ElimOrder<'a> {
    n_occ: &'a LMap<i32>,
}

impl<'a> ElimOrder<'a> {
    fn cost(&self, x: Var) -> u64 {
        self.n_occ[Lit::new(x, false)] as u64 * self.n_occ[Lit::new(x, true)] as u64
    }
}

impl<'a> PartialComparator<Var> for ElimOrder<'a> {
    fn partial_cmp(&self, lhs: &Var, rhs: &Var) -> Option<cmp::Ordering> {
        Some(self.cmp(lhs, rhs))
    }
}
impl<'a> Comparator<Var> for ElimOrder<'a> {
    fn cmp(&self, lhs: &Var, rhs: &Var) -> cmp::Ordering {
        Ord::cmp(&self.cost(*lhs), &self.cost(*rhs))
    }
}

#[derive(Debug, Clone, Copy)]
struct ShrinkStackElem {
    i: u32,
    l: Lit,
}

impl ShrinkStackElem {
    fn new(i: u32, l: Lit) -> Self {
        Self { i, l }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
enum Seen {
    UNDEF,
    SOURCE,
    REMOVABLE,
    FAILED,
}

impl Default for Seen {
    fn default() -> Self {
        Seen::UNDEF
    }
}

impl Seen {
    fn is_seen(&self) -> bool {
        *self != Seen::UNDEF
    }
}

#[derive(Debug, Clone)]
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

    pub use_asymm: bool,
    pub use_rcheck: bool,
    pub use_elim: bool,
    pub grow: i32,
    pub clause_lim: i32,
    pub subsumption_lim: i32,
    pub simp_garbage_frac: f64,
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

            use_asymm: false,
            use_rcheck: false,
            use_elim: true,
            grow: 0,
            clause_lim: 20,
            subsumption_lim: 1000,
            simp_garbage_frac: 0.5,
        }
    }
}

impl SolverOpts {
    pub fn check(&self) -> bool {
        (0.0 < self.var_decay && self.var_decay < 1.0)
            && (0.0 < self.clause_decay && self.clause_decay < 1.0)
            && (0.0 <= self.random_var_freq && self.random_var_freq <= 1.0)
            && (0.0 < self.random_seed && self.random_seed < f64::INFINITY)
            && (0 <= self.ccmin_mode && self.ccmin_mode <= 2)
            && (0 <= self.phase_saving && self.phase_saving <= 2) && 1 <= self.restart_first
            && (1.0 < self.restart_inc && self.restart_inc < f64::INFINITY)
            && (0.0 < self.garbage_frac && self.garbage_frac < f64::INFINITY)
            && 0 <= self.min_learnts_lim && -1 <= self.clause_lim
            && -1 <= self.subsumption_lim && 0.0 < self.simp_garbage_frac
    }
}

/// Finite subsequences of the Luby-sequence:
///
/// ```
/// 0: 1
/// 1: 1 1 2
/// 2: 1 1 2 1 1 2 4
/// 3: 1 1 2 1 1 2 4 1 1 2 1 1 2 4 8
/// ...
/// ```
fn luby(y: f64, mut x: i32) -> f64 {
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
fn drand(seed: &mut f64) -> f64 {
    *seed *= 1389796.0;
    let q = (*seed / 2147483647.0) as i32;
    *seed -= q as f64 * 2147483647.0;
    return *seed / 2147483647.0;
}

/// Generate a random integer:
fn irand(seed: &mut f64, size: i32) -> i32 {
    (drand(seed) * size as f64) as i32
}
