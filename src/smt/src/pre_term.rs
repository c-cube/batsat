
///! Pre-terms
///
/// Pre-terms are terms that are easy and cheap to create, but that
/// are not very useful until they are converted into proper terms.

use std::rc::Rc;
use std::vec::Vec;
use super::{term,fun,value};
use term::Term;

/// A pre-term, i.e. a temporary representation of a term
pub struct PreTerm(PTRef);

/// Automatic conversion from `term::Term` to `PreTerm`
impl From<term::Term> for PreTerm {
    fn from(t: term::Term) -> PreTerm {
        PreTerm(PTRef::Term(t))
    }
}

/* FIXME: how to get the term's view?
impl PreTerm {
    /// Look at the root of the term
    pub fn get_view<'a>(&'a self) -> term::View<'a, PreTerm> {
        match self.0 {
            PTRef::Term(t) =>
        }


}
*/

/// A `PreTermRef` is either a normal term, or an offset in a bank
enum PTRef {
    /// A pointer to a normal term
    Term(term::Term),
    /// A local definition in the given bank
    LocalApp {
        bank: Bank,
        id: offset,
    }
}

type offset = u32; // offset in the internal vector

/// Local application
struct LocalApp {
    /// Function symbol
    fun: fun::Fun,
    /// Arguments of the function
    args: Vec<InternalArg>,
}

/// Argument of a local application. It can point to another bank or
/// to the same bank, or to a normal term.
enum InternalArg {
    Term(term::Term),
    SameBank(offset),
    OtherBank(Bank, offset),
}

/// A refcounted reference to another term bank
pub struct Bank(Rc<BankInternal>);

/// A temporary store for a bunch of pre-terms. Creating new pre-terms from
/// this bank is fast, but they cannot be de-allocated nor compared.
struct BankInternal {
    cells: Vec<LocalApp>,
}

impl Clone for Bank {
    fn clone(&self) -> Bank { Bank(self.0.clone()) }
}

impl Bank {
    /// Create a new bank of terms
    pub fn new() -> Bank {
        Bank(Rc::new(BankInternal { cells: Vec::new() }))
    }

    /// Make a pre-term from a value
    #[inline]
    pub fn mk_value(&mut self, v: value::Value) -> PreTerm {
        PreTerm(PTRef::Term(Term::from(v)))
    }

    /// Make a new application
    pub fn mk_apply(&mut self, f: fun::Fun, args: &[PreTerm]) -> PreTerm {
        let args = {
            args.iter()
            .map(|t| match & t.0 {
                &PTRef::Term(t) => InternalArg::Term(t),
                &PTRef::LocalApp{ref bank, id} => {
                    /*
                    if &*bank.0 as * const BankInternal as * const _ == &*self.0 {
                        // same bank (physically), just use offset
                        InternalArg::SameBank(id)
                    } else {
                    */
                        let bank = bank.clone();
                        InternalArg::OtherBank(bank,id)
                }
            })
            .collect::<Vec<_>>()
        };
        let local_app = LocalApp { fun: f, args };
        let mut bi = self.0.ptr
        self.0.cells.push(local_app);
        let id = self.0.cells.len() as u32;
        PreTerm(PTRef::LocalApp {bank:self.clone(), id})
    }
}

