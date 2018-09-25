
///! Manager
///
/// An AST manager, parametrized by the cells composing the nodes of
/// the DAG structure it is responsible for maintaining.
///

use std::{hash::Hash,u32,fmt};
use typed_arena::Arena;
use std::vec::Vec;
use fnv::FnvHashMap as HM;
use std::borrow::Borrow;
use std::hash::Hasher;
use std::marker::PhantomData;
use std::cell::{RefCell as MCell,Ref as MRef};

/// A Handle on some AST node.
#[allow(non_camel_case_types)]
#[derive(Copy,Clone,PartialEq,Eq,PartialOrd,Ord,Hash)]
pub struct AST(u32);

impl fmt::Debug for AST {
    fn fmt(&self, out: &mut fmt::Formatter) -> fmt::Result {
        self.0.fmt(out)
    }
}

pub trait KeyT : Eq + Hash {}

pub trait Cell<Key : KeyT> : Borrow<Key> {
    /// Iterate on immediate subterms
    fn iter_sub<F>(&self, F) where F: Fn(AST);
}

/// A `PreCell` is a value that can be turned into a proper `Cell`.
///
/// It typically lives on the stack with local parameters, and is promoted
/// to a cell by getting to own its array/vec/smallvec of subterms.
pub trait PreCell<Key : KeyT> : Borrow<Key> {
    type Output : Cell<Key>;

    /// Transform itself into a managed version
    fn into_cell(&self) -> Self::Output;
}

/// A key in the hashtable, that doesn't own the cell itself, only an index
struct HKey<K:KeyT, C : Cell<K>> {
    k: *const C,
    _mark: PhantomData<K>,
}

impl<K:KeyT, C:Cell<K>, Other: Hash+Borrow<K>> PartialEq<Other> for HKey<K, C> {
    fn eq(&self, other: &Other) -> bool {
        let c1 = unsafe { &* self.k as &C }.borrow();
        let c2 = other.borrow();
        c1 == c2
    }
}

impl<K:KeyT, C:Cell<K>> Eq for HKey<K, C> {}

impl<K:KeyT, C:Cell<K>> Hash for HKey<K, C> {
    fn hash<H:Hasher>(&self, out: &mut H) {
        let c = unsafe { &* self.k as &C }.borrow();
        c.hash(out)
    }
}

impl<K:KeyT, C:Cell<K>> Borrow<K> for HKey<K, C> {
    fn borrow(&self) -> &K {
        let c = unsafe { &* self.k as &C }.borrow();
        c.borrow()
    }
}

/// An AST manager. It is responsible for storing AST nodes.
///
/// It stores the AST nodes and their arguments.
pub struct AstManager<K : KeyT, C : Cell<K>> {
    m: MCell<AstManagerImpl<K,C>>,
}

struct AstManagerImpl<K : KeyT, C : Cell<K>> {
    arena: Arena<C>,  // vector of nodes. NOTE: must never move.
    cells: Vec<* const C>, // ptrs into arena
    tbl: HM<HKey<K, C>, u32>, // hashmap of offsets into `cells`
    _mark: PhantomData<K>,
}

impl<K : KeyT, C:Cell<K>> AstManager<K, C> {
    /// Create a new AST Manager
    pub fn new() -> Self {
        Self {
            m: MCell::new(AstManagerImpl {
                arena: Arena::with_capacity(2_048),
                cells: Vec::with_capacity(2_048),
                tbl: HM::default(),
                _mark: PhantomData::default(),
            })
        }
    }
}

impl<K: KeyT, C: Cell<K>> AstManager<K, C> {
    /// View the content of the node for this given AST
    #[inline]
    pub fn view(&self, a: AST) -> MRef<C> {
        MRef::map(self.m.borrow(), |m| unsafe { &*m.cells[a.0 as usize] as &C})
    }

    /// Insert a new AST node built from pre-node `b`
    pub fn insert<PC: PreCell<K, Output=C>>(&self, b: &PC) -> AST {
        // lookup by key
        let key : &K = b.borrow();
        // local borrow
        let AstManagerImpl {
            ref mut cells, ref mut tbl, ref arena, ..
        } = *self.m.borrow_mut();
        match tbl.get(key) {
            Some(&id) => {
                AST(id) // found!
            },
            None => {
                // allocate a new slot for this sort.
                let id = cells.len() as u32;
                let ast = AST(id);

                // make the final cell, owned by the vec
                let new_cell = arena.alloc(b.into_cell());
                cells.push(&* new_cell as *const C);

                // also insert into the hashtable
                let new_key = HKey {
                    k: &* new_cell as *const C,
                    _mark: PhantomData::default(),
                };

                let _present = tbl.insert(new_key, id);
                assert!(_present.is_none());

                ast
            }
        }
    }

    /// Temporary self-contained reference
    pub fn get_ref<'a>(&'a self, ast: AST) -> AST_ref<'a, K, C> {
        AST_ref { m: &self, ast }
    }
}

impl<K : KeyT, C: Cell<K>> Drop for AstManager<K,C> {
    fn drop(&mut self) {
        // just clean tables
        let mut m = self.m.borrow_mut();
        m.tbl.clear();
        m.cells.clear();
    }
}

/// Temporary reference to the definition of an AST node
///
/// Can be used to pretty-print a term conveniently, or similar things.
#[allow(non_camel_case_types)]
pub struct AST_ref<'a, K : 'a+KeyT, C:'a+Cell<K>> {
    m: &'a AstManager<K, C>,
    ast: AST,
}

impl<'a, K : 'a+KeyT, C:'a+Cell<K>> AST_ref<'a, K, C> {
    /// View the content
    pub fn view(&self) -> MRef<C> {
        self.m.view(self.ast)
    }
}

#[cfg(test)]
#[allow(dead_code)]
mod test {
    use std::ops;
    use super::*;
    use std::fmt::Debug;

    #[derive(Clone,PartialEq,Eq,Hash,Debug)]
    pub enum TermCell {
        Const(i32),
        Add(Term, Term),
        App(String, Vec<Term>),
    }

    type Term = AST;

    impl KeyT for TermCell {}

    impl Cell<Self> for TermCell {
        fn iter_sub<F:Fn(Term)>(&self, f: F) {
            match self {
                TermCell::Const(_) => {},
                TermCell::Add(t1, t2) => {
                    f(*t1);
                    f(*t2)
                },
                TermCell::App(_, terms) => {
                    for t in terms.iter() { f(*t) }
                },
            }
        }
    }

    // Pre terms: a cell with temporary slices (e.g. on the stack)
    impl PreCell<TermCell> for TermCell {
        type Output = TermCell;
        fn into_cell(&self) -> TermCell {
            self.clone()
        }
    }

    // Wrapper around the AST manager
    struct M {
        m: AstManager<TermCell, TermCell>,
        tmp: Vec<Term>, // local storage
    }

    impl M {
        fn new() -> Self {
            M { tmp: Vec::new(), m: AstManager::new() }
        }

        fn mk_const(&self, i:i32) -> Term { self.insert(&TermCell::Const(i)) }
        fn mk_add(&self, a: Term, b: Term) -> Term { self.insert(&TermCell::Add(a,b)) }
        fn mk_app(&self, f: &str, args: &[AST]) -> Term {
            let mut v = Vec::new();
            v.extend_from_slice(args);
            let cell = TermCell::App(f.to_owned(), v);
            self.insert(&cell)
        }
    }
    impl ops::Deref for M {
        type Target = AstManager<TermCell,TermCell>;
        fn deref(&self) -> &Self::Target { &self.m }
    }
    impl ops::DerefMut for M {
        fn deref_mut(&mut self) -> &mut Self::Target { &mut self.m }
    }


    /// Pretty-print a term
    pub fn pp_term(t: &AST_ref<TermCell,TermCell>, out: &mut fmt::Formatter) -> fmt::Result {
        match *t.view() {
            TermCell::Const(i) => i.fmt(out),
            TermCell::Add(a,b) => write!(out, "{:?} + {:?}", t.m.get_ref(a), t.m.get_ref(b)),
            TermCell::App(ref f,ref args) if args.len() == 0 => f.fmt(out),
            TermCell::App(ref f,ref args) =>
                write!(out, "{:?}({:?})", f,
                args.iter().map(|&i| t.m.get_ref(i))),
        }
    }

    impl<'a> Debug for AST_ref<'a, TermCell, TermCell> {
        fn fmt(&self, out: &mut fmt::Formatter) -> fmt::Result {
            pp_term(&self, out)
        }
    }

    #[test]
    fn test1() {
        let m = M::new();
        let t1 = m.mk_const(42);
        let t2 = m.mk_const(10);
        assert_ne!(t1,t2, "{:?} != {:?}", m.get_ref(t1), m.get_ref(t2));
        let t3 = m.mk_const(42);
        assert_eq!(t1,t3, "{:?} == {:?}", m.get_ref(t1), m.get_ref(t3));
        let t4 = m.mk_app("f", &vec![t1,t2]);
        let t5 = m.mk_app("f", &vec![t1,t2]);
        assert_eq!(t4,t5, "{:?} == {:?}", m.get_ref(t4), m.get_ref(t5));
    }

    #[test]
    fn test2() {
        let m = M::new();

        for i in 1..2_000 {
            for j in i+1 .. 2_000 {
                let t = m.mk_add(m.mk_const(i), m.mk_const(j));
                let u = m.mk_add(m.mk_const(j), m.mk_const(i));
                if i==j {
                    assert_eq!(t, u, "{:?} == {:?}", m.get_ref(t), m.get_ref(u));
                } else {
                    assert_ne!(t, u, "{:?} != {:?}", m.get_ref(t), m.get_ref(u));
                }
            }
        }
    }
}

