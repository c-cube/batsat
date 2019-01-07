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
#[cfg(not(feature="logging"))]
#[macro_use]
pub(crate) mod log {
    macro_rules! trace {
        ($( $x:expr ),*) => {}
    }
    macro_rules! debug {
        ($( $x:expr ),*) => {}
    }
    macro_rules! info {
        ($( $x:expr ),*) => {}
    }
}

#[cfg(feature="logging")]
#[macro_use]
pub extern crate log;

extern crate smallvec;
extern crate bit_vec;

//======== PUBLIC INTERFACE ============

pub mod alloc;
pub mod intmap;
pub mod clause;
pub mod dimacs;
pub mod core;
pub mod interface;
pub mod callbacks;
pub mod theory;
pub mod drat;

pub use crate::{
    theory::{TheoryArgument,Theory,EmptyTheory},
    interface::SolverInterface,
    callbacks::{Callbacks,Basic as BasicCallbacks,Stats as StatsCallbacks, ProgressStatus},
    core::{Solver, SolverOpts},
    clause::{
        lbool, Lit, Var, LMap, LSet, VMap, display::Print,
        Kind as ClauseKind,
    },
};

/// Basic solver, with basic callbacks and no theory
pub type BasicSolver = Solver<BasicCallbacks>;
