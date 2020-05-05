/*****************************************************************************************[lib.rs]
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

//======== LOG ============

// stubs when logging is not enabled
#[cfg(not(feature = "logging"))]
#[macro_use]
pub(crate) mod log {
    macro_rules! trace {
        ($( $x:expr ),*) => {};
    }
    macro_rules! debug {
        ($( $x:expr ),*) => {};
    }
    macro_rules! info {
        ($( $x:expr ),*) => {};
    }
}

#[cfg(feature = "logging")]
#[macro_use]
pub extern crate log;

//======== PUBLIC INTERFACE ============

pub mod alloc;
pub mod callbacks;
pub mod clause;
pub mod core;
pub mod dimacs;
pub mod drat;
pub mod interface;
pub mod intmap;
pub mod theory;

pub use crate::{
    callbacks::{Basic as BasicCallbacks, Callbacks, ProgressStatus, Stats as StatsCallbacks},
    clause::{display::Print, lbool, Kind as ClauseKind, LMap, LSet, Lit, VMap, Var},
    core::{Solver, SolverOpts},
    interface::SolverInterface,
    theory::{EmptyTheory, Theory, TheoryArg},
};

/// Basic solver, with basic callbacks and no theory
pub type BasicSolver = Solver<BasicCallbacks>;
