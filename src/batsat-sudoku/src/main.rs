
//! A SMT-style sudoku solver.
//!
//! It relies on the SAT solver for exploring models, but creates clauses
//! dynamically.

// benchmarks from https://github.com/attractivechaos/plb/tree/ca35a7dfb2a235fa00fce58f7d1d426d69c6123a/sudoku/incoming

#[macro_use] extern crate log;

mod grid;
mod solve;
mod parse;
mod bref;

use {
    crate::{
        bref::Ref as BRef,
        grid::{Grid, Cell, }, solve::Solver, },
};

/// Result type.
pub type Result<T> = std::result::Result<T, Box<std::error::Error>>;

fn main() -> Result<()> {
    env_logger::init();
    // parse arguments
    let args = std::env::args().skip(1);

    let sep: String = "=".chars().cycle().take(70).collect();

    let propagate = match std::env::var("PROPAGATE") {
        Ok(s) => s.trim() == "1",
        Err(_) => false
    };
    if propagate {
        println!("note: using propagation");
    }

    for file in args {
        info!("process sudoku file {:?}", file);

        let file = std::fs::File::open(file)?;
        let grids = parse::parse(file)?;

        println!("parsed {} grid(s)", grids.len());

        for grid in grids {
            println!("{}\nsolve grid\n{}", sep, grid.render());

            let mut s = Solver::new(grid);
            s.set_propagate(propagate);

            match s.solve() {
                None => println!("grid can't be solved"),
                Some(sol) => {
                    println!("solution:\n{}", sol.render());

                    if ! sol.full() {
                        return Err("solution not completed".into())
                    } else if ! sol.is_correct() {
                        return Err("solution not correct".into())
                    }
                },
            }
        }
    }
    Ok(())
}
