
//! DRAT proofs

use {
    std::{i32, fmt},
    crate::{clause::ClauseIterable, Lit, },
};

/// A serialized DRAT proof.
#[derive(Debug,Clone)]
pub struct Proof(Vec<i32>);

mod proof {
    use {super::*, std::fmt::Write};

    impl fmt::Display for Proof {
        fn fmt(&self, out: &mut fmt::Formatter) -> fmt::Result {
            for &i in &self.0 {
                if i == i32::MAX { out.write_char('d')? }
                else if i == 0 { out.write_str(" 0\n")? }
                else { write!(out, " {}", i)? }
            }
            write!(out, "0")?; // final 0
            Ok(())
        }
    }

    impl Proof {
        /// New proof recording structure.
        pub fn new() -> Self { Proof(Vec::new()) }

        fn push_lit(&mut self, lit: Lit) {
            let i: i32 = (if lit.sign() {1} else {-1}) * ((lit.var().idx()+1) as i32);
            self.0.push(i)
        }

        /// Register clause creation.
        pub fn create_clause<C>(& mut self, c: & C) where C : ClauseIterable {
            for lit in c.items() { self.push_lit((*lit).into()); }
            self.0.push(0);
        }

        /// Register clause deletion.
        pub fn delete_clause<C>(&mut self, c: &C) where C : ClauseIterable {
            // display deletion of clause if proof production is enabled
            self.0.push(i32::MAX);
            for lit in c.items() { self.push_lit((*lit).into()); }
            self.0.push(0);
        }
    }
}

// TODO:
// - define `Proof` struct here
// - remove proof handling from core
// - use it in main in callbacks to optionally record proofs (with `on_axiom` + `on_learnt`)
