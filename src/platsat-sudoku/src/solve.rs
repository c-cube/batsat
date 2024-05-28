//! A sudoku solver.

use platsat::core::ExplainTheoryArg;
use {
    crate::{
        grid::{Cell, CellValue, Grid, Position},
        BRef,
    },
    platsat::{self as sat, lbool, theory, Lit as BLit, SolverInterface},
    std::collections::HashMap,
};

/// A sudoku solver, using SAT
pub struct Solver {
    // initial grid
    grid0: Grid,
    sat: SAT,
    s0: Solver0,
}

type SAT = sat::Solver<sat::StatsCallbacks>;

/// Given position = given number
type Predicate = (Position, CellValue);

/// Internal solver.
struct Solver0 {
    // if true, do lit propagation
    propagate: bool,
    status: Status,
    lm: LitMap,
    lits: Vec<BLit>, // temporary
    grid: BRef<Grid>,
    solution: Option<Grid>, // copy of solution, if any
    trail_len: BRef<usize>, // part of the trail we've seen
}

struct Status {
    ok: bool,
    confl: Vec<BLit>,
}

/// Bidirectional mapping literal/constraint.
struct LitMap {
    lit_to_pred: sat::VMap<Predicate>,
    pred_to_lit: HashMap<Predicate, BLit>,
}

impl Solver {
    /// New solver.
    pub fn new(grid: Grid) -> Self {
        let mut s0 = Solver0::new(grid.clone());
        let mut opts = sat::SolverOpts::default();
        opts.luby_restart = false;
        opts.restart_first = 1000;
        opts.restart_inc = 15.;
        //opts.ccmin_mode = 1; // NOTE: this can trigger various bugs
        opts.min_learnts_lim = 1_200; // min number of learnt clauses
        let mut sat = SAT::new_with(opts, Default::default());
        s0.create_lits(&mut sat); // be sure to create literals to decide
        Solver {
            grid0: grid,
            sat,
            s0,
        }
    }

    /// Enable/disable propagation.
    pub fn set_propagate(&mut self, b: bool) {
        self.s0.propagate = b;
    }

    fn assumptions(&self) -> Vec<BLit> {
        let mut res = vec![];
        for (c, pos) in self.grid0.iter() {
            if let Cell::Full(n) = c {
                let lit = self.s0.lm.find((pos, *n));
                res.push(lit);
            }
        }
        res
    }

    /// Solve the grid given at construction.
    ///
    /// Returns:
    /// - `Some(sol)` where `sol` is the completed grid, if satisfiable.
    /// - `None` if the grid can't be solved.
    pub fn solve(&mut self) -> &Option<Grid> {
        let assumptions = self.assumptions();
        self.s0.solution = None;
        let now = std::time::Instant::now();
        info!(
            "solve with {} assumptions, corresponding to initial grid",
            assumptions.len()
        );
        let res = self.sat.solve_limited_th(&mut self.s0, &assumptions[..]);

        info!("solving done ({:.3}s).", {
            let dur = now.elapsed();
            dur.as_secs() as f64 + dur.subsec_millis() as f64 * 1e-3
        });
        info!(
            "sat stats: decisions {}, propagations {}, conflicts {}, {}",
            self.sat.num_decisions(),
            self.sat.num_propagations(),
            self.sat.num_conflicts(),
            self.sat.cb()
        );

        if res == lbool::TRUE {
            assert!(self.s0.solution.is_some());
            &self.s0.solution
        } else {
            assert_eq!(lbool::FALSE, res);
            &None
        }
    }
}

impl Solver0 {
    fn new(grid: Grid) -> Self {
        Solver0 {
            propagate: false,
            lm: LitMap::new(),
            grid: BRef::new(grid),
            lits: vec![],
            trail_len: BRef::new(0),
            status: Status::new(),
            solution: None,
        }
    }

    #[inline(always)]
    fn ok(&self) -> bool {
        self.status.ok
    }

    /// Create literals in `SAT`.
    fn create_lits(&mut self, sat: &mut SAT) {
        let pred_sentinel: Predicate = ((0, 0), 0);
        for (_c, pos) in self.grid.iter() {
            for n in 1..=9 {
                // variable for `pos=n`
                let var = sat.new_var_default();
                self.lm.pred_to_lit.insert((pos, n), BLit::new(var, true));
                self.lm.lit_to_pred.insert(var, (pos, n), pred_sentinel);
            }
        }
    }

    /// update grid using `trail`.
    fn update_grid(&mut self, trail: &[BLit]) {
        if !self.ok() {
            return;
        }

        // update `self.grid`, producing conflict in case of incompatible assignments
        for &lit in trail.iter() {
            if lit.sign() {
                let (pos, n) = self.lm.lit_to_pred[lit.var()];

                match self.grid[pos] {
                    Cell::Empty => {
                        self.grid[pos] = Cell::Full(n);

                        /* TODO: propagate that the other values are now impossible
                        if self.propagate {
                            // propagate `¬pos=n2` for n!=n2
                            for n2 in 1..=9 {
                                if n2 == n { continue }

                                let lit2 = self.lm.find((pos,n2));
                                arg.propagate(!lit2);
                            }
                        }
                        */
                    }
                    Cell::Full(n2) if n == n2 => (),
                    Cell::Full(n2) => {
                        // conflict: incompatible assignments
                        self.status.mk_conflict(&[!lit, !self.lm.find((pos, n2))]);
                        return;
                    }
                }
            }
        }
    }

    // check constraints, possibly propagating literals or creating a conflict.
    fn check_constraints(&mut self, arg: &mut theory::TheoryArg) {
        // check unicity in columns
        for col in 0..9 {
            let mut n_assigned = 0;

            for i in 0..9 {
                let p1 = (i, col);

                let n = match self.grid[p1] {
                    Cell::Empty => continue,
                    Cell::Full(n) => {
                        n_assigned += 1;
                        n
                    }
                };

                for j in i + 1..9 {
                    let p2 = (j, col);
                    if self.grid[p2] == n {
                        trace!("col conflict for {:?} and {:?} (val {})", p1, p2, n);
                        self.status
                            .mk_conflict(&[!self.lm.find((p1, n)), !self.lm.find((p2, n))]);
                        return;
                    }
                }
            }

            if n_assigned == 8 && self.propagate {
                // propagate the only line and value that are missing.
                // TODO: use bits of a single integer instead?
                let mut unused_value = [true; 10];
                let mut unused_pos = [true; 9];
                for i in 0..9 {
                    if let Cell::Full(n) = self.grid[(i, col)] {
                        unused_value[n as usize] = false;
                        unused_pos[i as usize] = false;
                    }
                }

                debug_assert!(unused_value[1..].iter().any(|b| *b));
                debug_assert!(unused_pos.iter().any(|b| *b));
                let value = (1..=9).find(|&i| unused_value[i as usize]).unwrap();
                let line = (0..9).find(|&i| unused_pos[i as usize]).unwrap();
                let pos = (line, col);

                trace!("propagate only unassigned pos {:?} to {}", pos, value);
                trace!("current grid:\n{}", self.grid.render());
                let lit = self.lm.find((pos, value));
                arg.propagate(lit);
            }
        }
        // TODO: if column almost full, propagate

        // check unicity in lines
        for line in 0..9 {
            let mut n_assigned = 0;

            for i in 0..9 {
                let p1 = (line, i);

                let n = match self.grid[p1] {
                    Cell::Empty => continue,
                    Cell::Full(n) => {
                        n_assigned += 1;
                        n
                    }
                };

                for j in i + 1..9 {
                    let p2 = (line, j);
                    if self.grid[p2] == n {
                        trace!("line conflict for {:?} and {:?} (val {})", p1, p2, n);
                        self.status
                            .mk_conflict(&[!self.lm.find((p1, n)), !self.lm.find((p2, n))]);
                        return;
                    }
                }
            }

            if n_assigned == 8 && self.propagate {
                // TODO: propagate missing one
            }
        }
        // TODO: if line almost full, propagate

        // check unicity in squares
        for ((p1, c1), (p2, c2)) in self.grid.iter_square_pairs() {
            match (c1, c2) {
                (Cell::Full(n), Cell::Full(n2)) if n == n2 => {
                    assert_ne!(p1, p2);
                    trace!("square conflict for {:?} and {:?} (val {})", p1, p2, n);
                    self.status
                        .mk_conflict(&[!self.lm.find((p1, *n)), !self.lm.find((p2, *n))]);
                    return;
                }
                _ => (),
            }
        }
    }

    fn check_full(&mut self) {
        if !self.ok() {
            return;
        }

        // check that all cells are full
        for (c, pos) in self.grid.iter() {
            if let Cell::Empty = c {
                let Solver0 {
                    lm, ref mut status, ..
                } = self;
                // conflict: `∨_i pos=i`
                trace!("conflict: cell {:?} must be filled", pos);
                let c = (1..=9).map(|i| lm.find((pos, i)));
                status.mk_conflict_iter(c);
                break;
            }
        }
    }

    // convert internal state back to what SAT expects
    fn return_res(&mut self, arg: &mut theory::TheoryArg) {
        if self.ok() {
            self.solution = Some((*self.grid).clone());
        } else {
            assert!(self.status.confl.len() >= 2);
            arg.raise_conflict(&mut self.status.confl, true);
        }
    }
}

impl sat::Theory for Solver0 {
    fn final_check(&mut self, arg: &mut theory::TheoryArg) {
        debug!("final-check");
        assert!(self.ok());
        let trail = &arg.model()[..];
        self.update_grid(trail);
        self.check_full();

        trace!("fully updated grid:\n{}", self.grid.render());
        self.check_constraints(arg);

        self.return_res(arg)
    }
    #[inline]
    fn create_level(&mut self) {
        self.grid.push_level();
        self.trail_len.push_level();
    }
    #[inline]
    fn pop_levels(&mut self, n: usize) {
        if n > 0 {
            trace!("pop {} level(s)", n);
            self.status.ok = true;
            self.grid.pop_levels(n);
            self.trail_len.pop_levels(n);
        }
    }

    #[inline]
    fn n_levels(&self) -> usize {
        self.grid.n_levels()
    }

    fn partial_check(&mut self, arg: &mut theory::TheoryArg) {
        debug!("partial-check");
        assert!(self.ok());
        let m = arg.model();
        if m.len() <= *self.trail_len {
            return;
        }

        let trail = &m[*self.trail_len..];
        *self.trail_len = m.len();
        self.update_grid(trail);

        self.check_constraints(arg);
        self.return_res(arg)
    }

    fn explain_propagation_clause(&mut self, p: BLit, _: &mut ExplainTheoryArg) -> &[BLit] {
        assert!(self.propagate);
        let ((line, col), _n) = self.lm.lit_to_pred[p.var()];

        if p.sign() {
            // check if it's in column
            let col_full = (0..9).all(|i| i == line || self.grid[(i, col)].full());

            if col_full {
                // we can explain propagation using the whole column
                self.lits.clear();
                self.lits.push(p);
                for i in (0..9).filter(|&j| j != line) {
                    let pos = (i, col);
                    if let Cell::Full(n) = self.grid[pos] {
                        self.lits.push(!self.lm.find((pos, n)));
                    } else {
                        unreachable!()
                    }
                }
                trace!("explain propagation of {:?} using {:?}", p, &self.lits[..]);
                return &self.lits;
            }

            panic!("cannot explain propagation of {:?}", p)
        } else {
            unimplemented!("negative propagations");
            // TODO: handle propagation of `((line,col)!=n` because `((line,col)=n2`
            // - find the actual cell value
            // - explain that `(line,col)=n2 ==> (line,col)!=n`
        }
    }
}

impl Status {
    fn new() -> Self {
        Status {
            confl: vec![],
            ok: true,
        }
    }

    fn mk_conflict(&mut self, c: &[BLit]) {
        if !self.ok {
            return;
        }

        self.ok = false;
        self.confl.clear();
        self.confl.extend_from_slice(c);
    }

    /// Create a conflict from the given iterator.
    fn mk_conflict_iter<I>(&mut self, i: I)
    where
        I: Iterator<Item = BLit>,
    {
        if !self.ok {
            return;
        }

        self.ok = false;
        self.confl.clear();
        self.confl.extend(i);
    }
}

impl LitMap {
    fn new() -> Self {
        LitMap {
            pred_to_lit: HashMap::default(),
            lit_to_pred: sat::VMap::new(),
        }
    }

    /// Map the given predicate to a boolean literal.
    #[inline(always)]
    fn find(&self, pred: Predicate) -> BLit {
        self.pred_to_lit[&pred]
    }
}
