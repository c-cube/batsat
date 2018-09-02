
///! Manager
///
/// An AST manager, parametrized by the cells composing the nodes of
/// the DAG structure it is responsible for maintaining.
///

use std::{hash::Hash,u32,fmt};
use std::vec::Vec;
use std::marker::PhantomData;
use fnv::FnvHashMap as HM;

/// A Handle on some AST node.
#[allow(non_camel_case_types)]
#[derive(Copy,Clone,PartialEq,Eq,PartialOrd,Ord,Hash)]
pub struct AST(u32);

impl fmt::Debug for AST {
    fn fmt(&self, out: &mut fmt::Formatter) -> fmt::Result {
        write!(out, "T{}", self.0)
    }
}

/// An abstract slice of arguments that lives within a Manager.
#[derive(Copy,Clone,PartialEq,Eq,PartialOrd,Ord,Hash)]
pub struct ManagedSlice<T> {
    offset: u32,
    len: u32,
    _mark: PhantomData<T>, // covariant
}

impl<T> ManagedSlice<T> {
    /// Create a new slice offset
    #[inline]
    fn new(offset: u32, len: u32) -> Self {
        Self {offset, len, _mark: PhantomData}
    }

    #[inline]
    fn len(&self) -> usize { self.len as usize }

    /// Empty slice
    pub const EMPTY : Self = Self { offset:0, len:0, _mark:PhantomData };
}

/* TODO
struct ManagedSliceView<'a, C:'a+Cell> {
    slice: ManagedSlice<C>,
    m: &'a AstManager<C>,
}

impl<'a,T> ManagedSliceView<'a, C:'a+Cell> {
    /// Temporary view as a slice of arguments.
    ///
    /// The slice cannot outlive this view, which is what makes it safe.
    #[inline]
    pub fn as_slice(&self) -> &[T] {
        unsafe { slice::from_raw_parts(self.ptr, self.len as usize) }
    }
}


/// Allow to use a ManagedSlice as a normal slice
impl<T> ops::Deref for ManagedSlice<T> {
    type Target = [T];
    fn deref(& self) -> &[T] { &self.as_slice() }
}
*/

pub trait Cell : Clone {
    /// Key version, should use a slice of arguments
    type AsKey : Eq + Hash;

    /// Get a view on the immediate subterms of this term. Return the
    /// empty slice if the term has no arguments.
    #[inline]
    fn get_args(&self) -> ManagedSlice<AST>;

    fn as_key<'a, F>(&self, f: F) -> AsKey<'a>

    /* FIXME
    /// Iterate on immediate subterms.
    ///
    /// By default we assume the slice from `get_args` contains all the subterms.
    fn iter_subterms<F:Fn(AST)>(&self, f:F) {
        self.get_args().iter().for_each(|&x| f(x))
    }
    */

    /// Custom pretty printer (optional).
    ///
    /// The argument `F` is used to pretty-print sub-ASTs from a managed slice.
    /// It is called as `f(m, i, out)` and prints the `i`-th element of
    /// slice `m` into `out`.
    fn pp<F>(&self, out: &mut fmt::Formatter, _f: F) -> fmt::Result
    where F : Fn(ManagedSlice<AST>, usize, &mut fmt::Formatter) -> fmt::Result {
        write!(out, "AST")
    }
}

pub trait PreCell<C : Cell> {
    /// Get arguments
    fn get_args(&self) -> &[AST];

    /// Update itself to use the given managed slice
    fn into_cell(&self, args: ManagedSlice<AST>) -> C;
}

/// Argument given to pretty-printers
pub trait PrinterArg {
    fn pp_arg(&self, a: AST, &mut fmt::Formatter) -> fmt::Result;
    fn get_args(&self, m: ManagedSlice<AST>) -> &[AST];
}

/// An AST manager. It is responsible for storing AST nodes.
///
/// It stores the AST nodes and their arguments.
pub struct AstManager<C : Cell> {
    args: Vec<AST>,  // vector of arguments
    cells: Vec<C>,  // vector of nodes
    tbl: HM<C, u32>, // hashmap of offsets into `cells`
}

impl<C:Cell> AstManager<C> {
    /// Create a new AST Manager
    pub fn new() -> Self {
        Self {
            args: Vec::with_capacity(1_000),
            cells: Vec::with_capacity(256),
            tbl: HM::default(),
        }
    }
}

impl<C: Cell> AstManager<C> {
    /// View the content of the node for this given AST
    #[inline]
    pub fn view(&self, a: AST) -> &C {
        & self.cells[a.0 as usize]
    }

    /// Access the content of the given slice
    #[inline]
    pub fn slice(&self, m: ManagedSlice<AST>) -> &[AST] {
        & self.args[m.offset as usize .. m.len as usize]
    }

    /// Access the content of the given slice
    #[inline]
    pub fn slice_get(&self, m: ManagedSlice<AST>, i: usize) -> AST {
        self.args[m.offset as usize + i]
    }

    /// Get number of arguments
    pub fn n_args(&self, a: AST) -> usize {
        self.view(a).get_args().len()
    }

    /// Access `i`-th argument of given term
    pub fn get_arg_n(&self, a: AST, i: usize) -> AST {
        let m = self.view(a).get_args();
        self.slice_get(m, i)
    }

    /// Insert a new AST node built from pre-node `b`
    pub fn insert<PC: PreCell<C>>(&mut self, b: PC) -> AST {
        let args = b.get_args();
        let n_args = args.len();
        // temporarily push arguments
        let offset = self.args.len();
        self.args.extend_from_slice(args);
        let m_args = ManagedSlice::new(offset as u32, n_args as u32);

        let key = b.into_cell(m_args);

        match self.tbl.get(&key) {
            Some(&id) => {
                // found! remove temporary arguments
                self.args.truncate(offset);
                AST(id)
            },
            None => {
                assert!(n_args < u32::MAX as usize);
                // allocate a new slot for this sort.
                let ast = AST(self.cells.len() as u32);

                // make the final cell, owned by the vec
                let new_cell = b.into_cell(m_args);
                let new_key = new_cell.clone(); // and a copy for the table
                self.cells.push(new_cell);

                let _present = self.tbl.insert(new_key, ast.0);
                assert!(_present.is_none());

                ast
            }
        }
    }

    /// Temporary reference on the given AST.
    ///
    /// Useful for printing.
    pub fn pp(&self, a: AST) -> AST_ref<C> {
        AST_ref {m: &self, ast: a}
    }

    /// Pretty print the AST
    pub fn pp_ast(&self, a: AST, out: &mut fmt::Formatter) -> fmt::Result {
        let c = self.view(a);
        // use the printer to pretty-print subterms
        c.pp(out, |m, i, out| self.pp_ast(self.slice(m)[i], out))
    }

    /// Pretty print the AST in debug mode
    pub fn pp_ast_debug(&self, a: AST, out: &mut fmt::Formatter) -> fmt::Result {
        write!(out, "[{}]", a.0)?;
        let c = self.view(a);
        c.pp(out, |m, i, out| self.pp_ast_debug(self.slice(m)[i], out))
    }
}

impl<C: Cell> Drop for AstManager<C> {
    fn drop(&mut self) {
        // just clean tables
        self.tbl.clear();
        self.cells.clear();
        self.args.clear();
    }
}

/// Temporary reference to the definition of an AST node
///
/// Can be used to pretty-print a term conveniently.
#[allow(non_camel_case_types)]
pub struct AST_ref<'a, C:'a+Cell> {
    m: &'a AstManager<C>,
    ast: AST,
}

impl<'a, C:'a+Cell> fmt::Display for AST_ref<'a,C> {
    fn fmt(&self, out: &mut fmt::Formatter) -> fmt::Result {
        self.m.pp_ast(self.ast, out)
    }
}

impl<'a, C:'a+Cell> fmt::Debug for AST_ref<'a,C> {
    fn fmt(&self, out: &mut fmt::Formatter) -> fmt::Result {
        self.m.pp_ast_debug(self.ast, out)
    }
}

#[cfg(test)]
mod test {
    use std::ops;
    use super::*;

    #[derive(Clone,PartialEq,Eq,Hash,Debug)]
    enum TermCell<Args> {
        Const(i32),
        App(String, Args),
    }

    type Term = TermCell<ManagedSlice<AST>>;

    impl Cell for Term {
        fn get_args(&self) -> ManagedSlice<AST> {
            match self {
                TermCell::Const(_) => ManagedSlice::EMPTY,
                TermCell::App(_,a) => *a,
            }
        }

        fn pp<F>(&self, out: &mut fmt::Formatter, pp_arg: F) -> fmt::Result
        where F : Fn(ManagedSlice<AST>, usize, &mut fmt::Formatter) -> fmt::Result {
            match self {
                TermCell::Const(i) => write!(out, "{}", i),
                TermCell::App(f, args) if args.len() == 0 => write!(out, "{}", f),
                TermCell::App(f, args) => {
                    write!(out, "{}/{}(", f, args.len())?;
                    /*
                    for i in 0 .. args.len() {
                        if i>0 { write!(out, " ")? };
                        pp_arg(*args, i, out)?
                    };
                    */
                    write!(out, ")")
                }
            }
        }
    }

    // Pre terms: a cell with temporary slices (e.g. on the stack)
    impl<'a> PreCell<Term> for TermCell<&'a [AST]> {
        fn get_args(&self) -> &[AST] {
            match self {
                TermCell::Const(_) => &[],
                TermCell::App(_,a) => &a,
            }
        }

        fn into_cell(&self, m: ManagedSlice<AST>) -> Term {
            match self {
                TermCell::Const(i) => TermCell::Const(*i),
                TermCell::App(f,_) => TermCell::App(f.clone(), m),
            }

        }
    }

    // Wrapper around the AST manager
    struct M(AstManager<Term>);

    impl M {
        fn new() -> Self { M(AstManager::new()) }

        fn mk_const(&mut self, i:i32) -> AST { self.insert(TermCell::Const(i)) }
        fn mk_app(&mut self, f: &str, args: Vec<AST>) -> AST {
            self.insert(TermCell::App(f.to_owned(), args.as_slice()))
        }
    }
    impl ops::Deref for M {
        type Target = AstManager<Term>;
        fn deref(&self) -> &Self::Target { &self.0 }
    }
    impl ops::DerefMut for M {
        fn deref_mut(&mut self) -> &mut Self::Target { &mut self.0 }
    }


    #[test]
    fn test1() {
        let mut m = M::new();
        let t1 = m.mk_const(42);
        let t2 = m.mk_const(10);
        assert_ne!(t1,t2, "{:?} != {:?}", m.pp(t1), m.pp(t2));
        let t3 = m.mk_const(42);
        assert_eq!(t1,t3, "{:?} == {:?}", m.pp(t1), m.pp(t3));
        let t4 = m.mk_app("f", vec![t1,t2]);
        let t5 = m.mk_app("f", vec![t1,t2]);
        assert_eq!(t4,t5, "{:?} == {:?}", m.pp(t4), m.pp(t5));
    }
}

/* FIXME
/// Main manager structure
pub struct Manager<C : Cell> {

    /// apply terms
    apps: Vec<term::ApplyTerm>,

    /// Used to store the arguments of sorts
    sorts_args: Vec<sort::Sort>,

    /// Sorts, indexed by ID.
    sorts: Vec<SortInternal>,

    /// Map a sort cell (key) into the corresponding ID
    sorts_set: fnv::FnvHashMap<SortInternalRef, sort::ID>,

    /// Plugins
    plugins: Vec<Box<plugin::Plugin>>,
}

/// Internal representation of sorts
struct SortInternal {
    atom: sort::Atom,
    args: * const sort::Sort,
    n_args: usize,
}

/// A wrapped pointer to an internal sort. It is used as a key in the hashmap
struct SortInternalRef(* const SortInternal);

impl SortInternal {
    /// Obtain the sort's arguments as a slice
    #[inline]
    fn args_as_slice<'a>(&'a self) -> &'a [sort::Sort] {
        unsafe {slice::from_raw_parts(self.args, self.n_args)}
    }
}

impl PartialEq for SortInternalRef {
    // do not compare IDs yet
    fn eq(&self, other: &SortInternalRef) -> bool {
        let a1 = unsafe {&*self.0};
        let a2 = unsafe {&*other.0};
        a1.atom == a2.atom && a1.args_as_slice() == a2.args_as_slice()
    }
}
impl Eq for SortInternalRef {}

impl hash::Hash for SortInternalRef {
    fn hash<H>(&self, h:&mut H) where H : hash::Hasher {
        let a = unsafe {&*self.0};
        a.atom.hash(h);
        a.args_as_slice().hash(h)
    }
}

// used internally
const SORT_EMPTY : &'static [sort::Sort] = &[];
const TERM_EMPTY : &'static [term::Term] = &[];

impl Manager {
    pub fn new() -> Self {
        Manager {
            apps: Vec::with_capacity(1_024),
            sorts_args: Vec::with_capacity(64),
            sorts: Vec::with_capacity(32),
            sorts_set: fnv::FnvHashMap::default(),
            plugins: Vec::new(),
        }
    }

    /// Create a new plugin from a builder function
    pub fn add_plugin(&mut self, b: plugin::Builder) -> plugin::ID {
        let pid = self.plugins.len() as u8;
        if pid == u8::MAX {
            panic!("maximum number of plugins reached");
        }
        let pid = super::plugin::ID(pid);
        let plugin = b(pid, self); // build plugin
        self.plugins.push(plugin);
        pid
    }

    pub fn n_plugins(&self) -> usize {
        self.plugins.len()
    }

    #[inline]
    pub fn get_apply(& self, id: term::ID) -> & term::ApplyTerm {
        &self.apps[id.0 as usize]
    }

    /// `m.get_sort(s)` returns the description of sort `s`
    pub fn get_sort<'a>(&'a self, id: sort::ID) -> sort::SortCell<'a> {
        let s = & self.sorts[id.0 as usize];
        // rebuild from parts
        let args = unsafe { slice::from_raw_parts(s.args, s.n_args) };
        sort::SortCell { id, atom: s.atom, args }
    }

    #[inline]
    pub fn get_plugin(& self, id: plugin::ID) -> & plugin::Plugin {
        &*self.plugins[id.0 as usize]
    }

    /// Iterate on the plugins
    #[inline]
    pub fn iter_plugins<'b>(&'b self) -> impl Iterator<Item=&'b plugin::Plugin> {
        self.plugins.iter().map(|p| &**p)
    }

    /// Create a new term
    pub fn mk_apply<'b>(&mut self, fun: fun::Fun, t_args: &'b [term::Term]) -> term::Term {
        let id = term::ID(self.apps.len() as i32);
        // copy args into the local array
        let args =
            if t_args.len() == 0 { Vec::new() }
            else {
                let mut v = Vec::with_capacity(t_args.len());
                v.extend_from_slice(t_args);
                v
            };
        let app = term::ApplyTerm { id, args, fun, flags: term::Flags::empty(), };
        self.apps.push(app);
        term::Term::App(id) // make a new term
    }

    /// Create a constant term
    #[inline]
    pub fn mk_const(&mut self, f: fun::Fun) -> term::Term {
        self.mk_apply(f, TERM_EMPTY)
    }

    /// Create a sort
    ///
    /// `mk_sort(atom, args)` returns the hashconsed version of this sort.
    pub fn mk_sort<'a>(&mut self, a: sort::Atom, args: &'a [sort::Sort]) -> sort::Sort {
        // build a key for lookup
        let key = SortInternal { atom: a, args: args.as_ptr(), n_args: args.len() };
        let key = SortInternalRef(& key as *const _);
        // query using the local key
        match self.sorts_set.get(&key) {
            Some(&id) => sort::Sort(id),
            None => {
                // allocate a new slot for this sort.
                let id = sort::ID(self.sorts.len() as u32);
                let offset = self.sorts_args.len();
                // allocate arguments of the slice
                self.sorts_args.extend_from_slice(args);
                let n = args.len();
                let v_args = & self.sorts_args[offset .. n];
                let s = SortInternal { atom: a, args: v_args.as_ptr(), n_args: n };
                // The sort is owned by the vec, and pointed to by the hashmap
                self.sorts.push(s);
                // also add to the map
                let key2 = SortInternalRef(self.sorts.last().unwrap() as *const _);
                let present = self.sorts_set.insert(key2, id);
                assert!(present.is_none());
                sort::Sort(id)
            }
        }
    }

    #[inline]
    pub fn mk_const_sort(&mut self, a: sort::Atom) -> sort::Sort {
        self.mk_sort(a, SORT_EMPTY)
    }

    /// Check equality of terms
    pub fn eq_term(&self, t1: term::Term, t2: term::Term) -> bool {
        // traverse terms as a DAG
        let mut tbl : fnv::FnvHashSet<(term::Term, term::Term)> = fnv::FnvHashSet::default();
        let mut q = Vec::new();
        q.push((t1,t2));
        while let Some (pair) = q.pop() {
            use term::Term::*;
            match pair {
                (Value(v1), Value(v2)) => if v1 != v2 { return false },
                (Value(_), App(_)) => return false,
                (App(_), Value(_)) => return false,
                (App(f1), App(f2)) => {
                    let t1 = self.get_apply(f1);
                    let t2 = self.get_apply(f2);
                    // check function and arity
                    if t1.fun != t2.fun || t1.args.len() != t2.args.len() { return false }
                    if t1.args.len() == 0 { continue; }
                    if ! tbl.contains(&pair) {
                        tbl.insert(pair);
                        // check sub-terms recursively
                        for i in 0 .. t1.args.len() {
                            q.push((t1.args[i], t2.args[i]))
                        }
                    }
                },
            }
        }
        true
    }

    /// Obtain the ID of a plugin by its name
    pub fn get_plugin_by_name(&self, name: &str) -> plugin::ID {
        for p in self.plugins.iter() {
            if p.name() == name { return p.id() }
        }
        panic!("get_dependency: no plugin named {}", name);
    }

    /// Pretty-print a term
    pub fn pp_term(&self, fmt: &mut fmt::Formatter, t: term::Term) -> fmt::Result {
        match t {
            term::Term::Value(v) => v.fmt(fmt),
            term::Term::App(id) => {
                let app = self.get_apply(id);
                let plugin = self.get_plugin(app.fun.plugin);
                fun::Manager::pp_apply(plugin, fmt, self, app.fun.id, &app.args)
            }
        }
    }

    /// Pretty-print a sort
    pub fn pp_sort(&self, fmt: &mut fmt::Formatter, s: sort::Sort) -> fmt::Result {
        let c = self.get_sort(s.0);
        let plugin = self.get_plugin(c.atom.plugin);
        if c.args.len() == 0 {
            plugin.pp_atom(fmt, c.atom.id)
        } else {
            write!(fmt, "(")?;
            plugin.pp_atom(fmt, c.atom.id)?;
            for x in c.args.iter() {
                write!(fmt, " ")?;
                self.pp_sort(fmt, *x)?;
            };
            write!(fmt,")")
        }
    }

    /// Install all plugins to the manager
    pub fn load_all_theories(&mut self) {
        for b in theories::ALL.iter() {
            let _ = self.add_plugin(b);
        }
    }
}

/// When a manager is dropped, we can reclaim all memory
impl Drop for Manager {
    fn drop(& mut self) {
        for p in self.plugins.drain(..) {
            drop(p)
        }
        // cleanup sort table
        self.sorts_set.clear();
        self.sorts.clear();
        self.sorts_args.clear();
    }
}

#[cfg(test)]
pub mod tests {
    use super::*;
    use term::TRef;

    macro_rules!ppt {
        ($t:expr, $m: expr) => {
            TRef($t as term::Term, &$m)
        }
    }

    fn get_manager() -> Manager {
        let mut m = Manager::new();
        m.load_all_theories();
        m
    }

    // test that we have one plugin, and that we can access it
    #[test]
    fn test_manager() {
        let m = get_manager();
        assert!(m.n_plugins() >= 1);
        let p1 = m.get_plugin(plugin::ID(0));
        assert_eq!(p1.id(), plugin::ID(0));
    }

    #[test]
    fn test_apply1() {
        let mut m = get_manager();
        let pid = m.get_plugin(plugin::ID(0)).id();
        let f = fun::Fun {plugin: pid, id: fun::ID(0)};
        {
            let t1 = m.mk_apply(f, &vec![]);
            let t2 = m.mk_apply(f, &vec![]);
            assert!(t1 != t2, format!("{:?} !== {:?}", ppt!(t1,m), ppt!(t2,m)));
            assert!(m.eq_term(t1, t2), format!("{:?} = {:?}", ppt!(t1,m), ppt!(t2,m)));
        }
    }
}
*/
