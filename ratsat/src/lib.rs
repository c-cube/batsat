pub mod alloc;
pub mod intmap;
pub mod clause;
pub mod dimacs;
pub mod core;

pub use core::Solver;
pub use clause::{lbool, Lit, Var};

#[cfg(test)]
mod tests {
    #[test]
    fn it_works() {
        assert_eq!(2 + 2, 4);
    }
}
