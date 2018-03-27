use std::cmp;
use {lbool, Lit, Var};
use intmap::{Comparator, Heap, HeapData, PartialComparator};
use clause::{CRef, ClauseAllocator, DeletePred, LSet, OccLists, OccListsData, VMap};

#[derive(Debug)]
pub struct Solver {
    // Extra results: (read-only member variable)
    /// If problem is satisfiable, this vector contains the model (if any).
    model: Vec<lbool>,
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
    num_clauses: u64,
    num_learnts: u64,
    clauses_literals: u64,
    learnts_literals: u64,
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

    /// A heuristic measurement of the activity of a variable.
    activity: VMap<f64>,
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
    /// Amount to bump next variable with.
    var_inc: f64,
    /// Head of queue (as index into the trail -- no more explicit propagation queue in MiniSat).
    qhead: i32,
    /// Number of top-level assignments since last execution of 'simplify()'.
    simpDB_assigns: i32,
    /// Remaining number of propagations that must be made before next execution of 'simplify()'.
    simpDB_props: i64,
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
    seen: VMap<bool>,
    // analyze_stack: Vec<ShrinkStackElem>,
    analyze_toclear: Vec<Lit>,
    add_tmp: Vec<Lit>,

    max_learnts: f64,
    learntsize_adjust_confl: f64,
    learntsize_adjust_cnt: i32,

    // Resource contraints:
    conflict_budget: i64,
    propagation_budget: i64,
    asynch_interrupt: bool,

    v: SolverV,
}
#[derive(Debug)]
struct SolverV {
    /// The current assignments.
    assigns: VMap<lbool>,
    /// Assignment stack; stores all assigments made in the order they were made.
    trail: Vec<Lit>,
    /// Separator indices for different decision levels in 'trail'.
    trail_lim: Vec<i32>,
    /// Stores reason and level for each variable.
    vardata: VMap<VarData>,
}

impl Default for Solver {
    fn default() -> Self {
        Self {
            // Parameters (user settable):
            model: vec![],
            conflict: LSet::new(),
            verbosity: 0,
            var_decay: 0.95,
            clause_decay: 0.999,
            random_var_freq: 0.0,
            random_seed: 91648253.0,
            luby_restart: true,
            ccmin_mode: 2,
            phase_saving: 2,
            rnd_pol: false,
            rnd_init_act: false,
            garbage_frac: 0.20,
            min_learnts_lim: 0,
            restart_first: 100,
            restart_inc: 2.0,

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
            num_clauses: 0,
            num_learnts: 0,
            clauses_literals: 0,
            learnts_literals: 0,
            max_literals: 0,
            tot_literals: 0,

            clauses: vec![],
            learnts: vec![],
            // v.trail: vec![],
            // v.trail_lim: vec![],
            assumptions: vec![],
            activity: VMap::new(),
            // v.assigns: VMap::new(),
            polarity: VMap::new(),
            user_pol: VMap::new(),
            decision: VMap::new(),
            // v.vardata: VMap::new(),
            watches_data: OccListsData::new(),
            order_heap_data: HeapData::new(),
            ok: true,
            cla_inc: 1.0,
            var_inc: 1.0,
            qhead: 0,
            simpDB_assigns: -1,
            simpDB_props: 0,
            progress_estimate: 0.0,
            remove_satisfied: true,
            next_var: Var::from_idx(0),

            ca: ClauseAllocator::new(),
            released_vars: vec![],
            free_vars: vec![],
            seen: VMap::new(),
            // analyze_stack: vec![],
            analyze_toclear: vec![],
            add_tmp: vec![],
            max_learnts: 0.0,
            learntsize_adjust_confl: 0.0,
            learntsize_adjust_cnt: 0,

            // Resource constraints:
            conflict_budget: -1,
            propagation_budget: -1,
            asynch_interrupt: false,

            v: SolverV {
                assigns: VMap::new(),
                trail: vec![],
                trail_lim: vec![],
                vardata: VMap::new(),
            },
        }
    }
}

impl Solver {
    pub fn set_verbosity(&mut self, verbosity: i32) {
        debug_assert!(0 <= verbosity && verbosity <= 2);
        self.verbosity = verbosity;
    }
    pub fn num_clauses(&self) -> u32 {
        self.num_clauses as u32
    }
    pub fn verbosity(&self) -> i32 {
        self.verbosity
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

    pub fn num_vars(&self) -> u32 {
        self.next_var.idx()
    }

    /// Creates a new SAT variable in the solver. If 'decision' is cleared, variable will not be
    /// used as a decision variable (NOTE! This has effects on the meaning of a SATISFIABLE result).
    pub fn new_var(&mut self, upol: lbool, dvar: bool) -> Var {
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
            self.activity
                .insert_default(v, drand(&mut self.random_seed) * 0.00001);
        } else {
            self.activity.insert_default(v, 0.0);
        }
        self.seen.insert_default(v, false);
        self.polarity.insert_default(v, true);
        self.user_pol.insert_default(v, upol);
        self.decision.reserve_default(v);
        let len = self.v.trail.len();
        self.v.trail.reserve(v.idx() as usize + 1 - len);
        self.set_decision_var(v, dvar);
        v
    }

    pub fn new_var_default(&mut self) -> Var {
        self.new_var(lbool::UNDEF, true)
    }
    pub fn add_clause_reuse(&mut self, clause: &mut Vec<Lit>) -> bool {
        // eprintln!("add_clause({:?})", clause);
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

        if self.v.num_assigns() as i32 == self.simpDB_assigns || self.simpDB_props > 0 {
            return true;
        }

        // Remove satisfied clauses:
        self.remove_satisfied(true);

        // // Remove satisfied clauses:
        // removeSatisfied(learnts);
        // if (remove_satisfied){       // Can be turned off.
        //     removeSatisfied(clauses);

        //     // TODO: what todo in if 'remove_satisfied' is false?

        //     // Remove all released variables from the trail:
        //     for (int i = 0; i < released_vars.size(); i++){
        //         assert(seen[released_vars[i]] == 0);
        //         seen[released_vars[i]] = 1;
        //     }

        //     int i, j;
        //     for (i = j = 0; i < trail.size(); i++)
        //         if (seen[var(trail[i])] == 0)
        //             trail[j++] = trail[i];
        //     trail.shrink(i - j);
        //     //printf("trail.size()= %d, qhead = %d\n", trail.size(), qhead);
        //     qhead = trail.size();

        //     for (int i = 0; i < released_vars.size(); i++)
        //         seen[released_vars[i]] = 0;

        //     // Released variables are now ready to be reused:
        //     append(released_vars, free_vars);
        //     released_vars.clear();
        // }
        // checkGarbage();
        // rebuildOrderHeap();

        // simpDB_assigns = nAssigns();
        // simpDB_props   = clauses_literals + learnts_literals;   // (shouldn't depend on stats really, but it will do for now)

        true
    }

    /// Shrink 'cs' to contain only non-satisfied clauses.
    // fn remove_satisfied(&mut self, cs: &mut Vec<CRef>) {
    fn remove_satisfied(&mut self, shrink_learnts: bool) {
        macro_rules! satisfied_v {
            ($self_v:expr, $c:expr) => {{
                // $self.satisfied($c)
                $c.iter().any(|&lit| $self_v.value_lit(lit) == lbool::TRUE)
            }};
        }
        let cs: &mut Vec<CRef> = if shrink_learnts {
            &mut self.learnts
        } else {
            &mut self.clauses
        };
        let mut j = 0;
        let ca = &mut self.ca;
        let self_v = &self.v;
        cs.retain(|&cr| {
            let mut c = ca.get_mut(cr);
            if satisfied_v!(self_v, c.as_clause_ref()) {
            } else {
            }
            false
        });

        // int i, j;
        // for (i = j = 0; i < cs.size(); i++){
        //     Clause& c = ca[cs[i]];
        //     if (satisfied(c))
        //         removeClause(cs[i]);
        //     else{
        //         // Trim clause:
        //         assert(value(c[0]) == l_Undef && value(c[1]) == l_Undef);
        //         for (int k = 2; k < c.size(); k++)
        //             if (value(c[k]) == l_False){
        //                 c[k--] = c[c.size()-1];
        //                 c.pop();
        //             }
        //         cs[j++] = cs[i];
        //     }
        // }
        // cs.shrink(i - j);
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
            self.num_learnts += 1;
            self.learnts_literals += size as u64;
        } else {
            self.num_clauses += 1;
            self.clauses_literals += size as u64;
        }
    }

    /// Propagates all enqueued facts. If a conflict arises, the conflicting clause is returned,
    /// otherwise CRef_Undef.
    ///
    /// # Post-conditions:
    ///
    /// - the propagation queue is empty, even if there was a conflict.
    fn propagate(&mut self) -> CRef {
        // These macros are to avoid false sharing of references.
        let mut confl = CRef::UNDEF;
        let mut num_props: u32 = 0;

        while (self.qhead as usize) < self.v.trail.len() {
            // 'p' is enqueued fact to propagate.
            let p = self.v.trail[self.qhead as usize];
            self.qhead += 1;
            let watches_data_ptr: *mut OccListsData<_, _> = &mut self.watches_data;
            // let ws = self.watches().lookup_mut(p);
            let ws = self.watches_data
                .lookup_mut_pred(p, &WatcherDeleted { ca: &self.ca });
            let mut i: usize = 0;
            let mut j: usize = 0;
            let end: usize = ws.len();
            num_props += 1;
            while i < end {
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
                    }
                }

                // Did not find watch -- clause is unit under assignment:
                ws[j] = w;
                j += 1;
                if self.v.value_lit(first) == lbool::FALSE {
                    confl = cr;
                    self.qhead = self.v.trail.len() as i32;
                    // Copy the remaining watches:
                    while i < end {
                        ws[j] = ws[i];
                        j += 1;
                        i += 1;
                    }
                } else {
                    self.v.unchecked_enqueue(first, cr);
                }
            }
            let dummy = Watcher {
                cref: CRef::UNDEF,
                blocker: Lit::UNDEF,
            };
            ws.resize(i - j, dummy);
        }
        self.propagations += num_props as u64;
        self.simpDB_props -= num_props as i64;

        confl
    }

    fn order_heap(&mut self) -> Heap<Var, VarOrder> {
        self.order_heap_data.promote(VarOrder {
            activity: &self.activity,
        })
    }
    fn watches(&mut self) -> OccLists<Lit, Watcher, WatcherDeleted> {
        self.watches_data.promote(WatcherDeleted { ca: &self.ca })
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

    pub fn decision_level(&self) -> u32 {
        self.trail_lim.len() as u32
    }

    fn unchecked_enqueue(&mut self, p: Lit, from: CRef) {
        debug_assert_eq!(self.value_lit(p), lbool::UNDEF);
        self.assigns[p.var()] = lbool::new(!p.sign());
        self.vardata[p.var()] = VarData::new(from, self.decision_level() as i32);
        self.trail.push(p);
    }
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

/// Generate a random double:
fn drand(seed: &mut f64) -> f64 {
    *seed *= 1389796.0;
    let q = (*seed / 2147483647.0) as i32;
    *seed -= q as f64 * 2147483647.0;
    return *seed / 2147483647.0;
}
