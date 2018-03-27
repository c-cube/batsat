use {lbool, Lit, Var};
use clause::{CRef, ClauseAllocator, LSet, VMap};

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
    clause_literals: u64,
    learnt_literals: u64,
    max_literals: u64,
    tot_literals: u64,

    // Solver state:
    /// List of problem clauses.
    clauses: Vec<CRef>,
    /// List of learnt clauses.
    learnts: Vec<CRef>,
    /// Assignment stack; stores all assigments made in the order they were made.
    trail: Vec<Lit>,
    /// Separator indices for different decision levels in 'trail'.
    trail_lim: Vec<i32>,
    /// Current set of assumptions provided to solve by the user.
    assumptions: Vec<Lit>,

    /// A heuristic measurement of the activity of a variable.
    activity: VMap<f64>,
    /// The current assignments.
    assigns: VMap<lbool>,
    /// The preferred polarity of each variable.
    polarity: VMap<bool>,
    /// The users preferred polarity of each variable.
    user_pol: VMap<lbool>,
    /// Declares if a variable is eligible for selection in the decision heuristic.
    decision: VMap<bool>,
    // /// Stores reason and level for each variable.
    // vardata: VMap<VarData>,
    // /// 'watches[lit]' is a list of constraints watching 'lit' (will go there if literal becomes true).
    // watches: OccLists<Lit, Vec<Watcher>, WatcherDeleted>

    // /// A priority queue of variables ordered with respect to the variable activity.
    // order_heap: Heap<Var>
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
            clause_literals: 0,
            learnt_literals: 0,
            max_literals: 0,
            tot_literals: 0,

            clauses: vec![],
            learnts: vec![],
            trail: vec![],
            trail_lim: vec![],
            assumptions: vec![],
            activity: VMap::new(),
            assigns: VMap::new(),
            polarity: VMap::new(),
            user_pol: VMap::new(),
            decision: VMap::new(),
            // vardata: VMap::new(),

            // watches: OccLists::new(WatcherDeleted(ca)),
            // order_heap: Heap::new(),
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
        // self.watches.init(mkLit(v, false));
        // self.watches.init(mkLit(v, true));
        self.assigns.insert_default(v, lbool::UNDEF);
        // self.vardata.insert_default(v, mkVarData(CRef::UNDEF, 0));
        if self.rnd_init_act {
            // self.activity.insert_default(v, drand(self.random_seed) * 0.00001);
        } else {
            self.activity.insert_default(v, 0.0);
        }
        self.seen.insert_default(v, false);
        self.polarity.insert_default(v, true);
        self.user_pol.insert_default(v, upol);
        self.decision.reserve_default(v);
        let len = self.trail.len();
        self.trail.reserve(v.idx() as usize + 1 - len);
        // self.set_decision_var(v, dvar);
        v
    }

    pub fn new_var_default(&mut self) -> Var {
        self.new_var(lbool::UNDEF, true)
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
            // self.clauses.push(clause.to_vec());
            // self.attach_clause(clause);
        }

        true
    }
    pub fn decision_level(&self) -> u32 {
        self.trail_lim.len() as u32
    }
}
