
//! Term representation

use std::fmt;
use super::{fun,value,manager};

/// A single term.
///
/// A term is either:
/// - a semantic value, or
/// - a symbol application
#[derive(Copy,Clone,Eq,PartialEq,Hash)]
pub enum Term {
    Value(value::Value),
    App(ID),
}

/// Terms that are function applications
pub struct ApplyTerm {
    /// unique identifier for this term
    pub id: ID,
    /// Function symbol
    pub fun: fun::Fun,
    /// Flags
    pub flags: Flags,
    /// Arguments of the function
    pub args: Vec<Term>,
}

/// Direct conversion from values
impl From<value::Value> for Term {
    fn from(v: value::Value) -> Term {
        Term::Value(v)
    }
}


/// What a term looks like, at the root.
///
/// A `View` is used to get a glance at a term-like structure.
pub enum View<'a, Subterm> where Subterm : 'a {
    Value(value::Value),
    Apply {
        fun: fun::Fun,
        args: &'a [Subterm],
    }
}

/// Term-like structures must provide a `view` into their root
trait HasView {
    type Subterm;

    /// Obtain a view of the root of this term
    fn get_view<'a>(&'a self, m: &'a manager::Manager) -> View<'a, Self::Subterm>;
}

impl HasView for Term {
    type Subterm = Term;

    fn get_view<'a>(&'a self, m: &'a manager::Manager) -> View<'a, Term> {
        match self {
            Term::Value(v) => View::Value(*v),
            Term::App(id) => {
                let app = m.get_apply(*id);
                View::Apply { fun: app.fun, args: &app.args }
            },
        }
    }
}

/// Unique ID of a term
#[derive(Copy,Clone,PartialEq,Eq,PartialOrd,Ord,Hash,Debug)]
pub struct ID(pub i32);

bitflags! {
    /// Flags that can apply to a term
    pub struct Flags : u16 {
        const USER_1 = 0b00100; // multi-purpose
        const USER_2 = 0b01000; // multi-purpose
    }
}

/// External reference to a term
pub struct TRef<'a>(pub Term, pub &'a manager::Manager);

impl<'a> fmt::Debug for TRef<'a> {
    fn fmt(&self, fmt: &mut fmt::Formatter) -> fmt::Result {
        self.1.pp_term(fmt, self.0)
    }
}

