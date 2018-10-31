/*****************************************************************************************[clause.rs]
Copyright (c) 2003-2006, Niklas Een, Niklas Sorensson (MiniSat)
Copyright (c) 2007-2010, Niklas Sorensson (MiniSat)
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

use std::fmt;
use std::iter::DoubleEndedIterator;
use std::collections::HashMap;
use std::ops;
use std::u32;
use smallvec::SmallVec;
use intmap::{AsIndex, IntMap, IntSet, IntMapBool};

#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct Var(u32);

impl fmt::Debug for Var {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        if self.0 == !0 {
            write!(f, "UNDEF")
        } else {
            write!(f, "{}", self.0+1)
        }
    }
}

impl Var {
    pub const UNDEF: Var = Var(!0);
    #[inline(always)]
    pub(crate) fn from_idx(idx: u32) -> Self {
        debug_assert!(idx < u32::MAX / 2, "Var::from_idx: index too large");
        Var(idx)
    }
    #[inline(always)]
    pub fn idx(&self) -> u32 {
        self.0
    }
}

impl AsIndex for Var {
    fn as_index(self) -> usize {
        self.0 as usize
    }
    fn from_index(index: usize) -> Self {
        Var(index as u32)
    }
}

pub type VMap<V> = IntMap<Var, V>;

#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct Lit(u32);

impl Lit {
    pub const UNDEF: Lit = Lit(!1);
    pub const ERROR: Lit = Lit(!0);

    #[inline(always)]
    pub fn new(var: Var, sign: bool) -> Self {
        Lit(var.0 * 2 + (!sign) as u32)
    }
    #[inline(always)]
    pub(crate) fn from_idx(idx: u32) -> Self {
        Lit(idx)
    }
    #[inline(always)]
    pub fn idx(&self) -> u32 {
        self.0
    }
    #[inline(always)]
    pub fn sign(&self) -> bool {
        (self.0 & 1) == 0
    }
    #[inline(always)]
    pub fn var(&self) -> Var {
        Var(self.0 >> 1)
    }
}

impl fmt::Debug for Lit {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        if self.0 == !0 {
            write!(f, "ERROR")
        } else if self.0 == !1 {
            write!(f, "UNDEF")
        } else {
            write!(f, "{}{}", if self.sign() {""} else {"-"}, self.0 / 2 + 1)
        }
    }
}

impl ops::Not for Lit {
    type Output = Self;
    #[inline(always)]
    fn not(self) -> Self {
        Lit(self.0 ^ 1)
    }
}
impl ops::BitXor<bool> for Lit {
    type Output = Self;
    fn bitxor(self, rhs: bool) -> Self {
        Lit(self.0 ^ rhs as u32)
    }
}
impl ops::BitXorAssign<bool> for Lit {
    fn bitxor_assign(&mut self, rhs: bool) {
        *self = *self ^ rhs;
    }
}

impl AsIndex for Lit {
    #[inline(always)]
    fn as_index(self) -> usize {
        self.0 as usize
    }
    #[inline(always)]
    fn from_index(index: usize) -> Self {
        Lit(index as u32)
    }
}

pub type LMap<V> = IntMap<Lit, V>;
pub type LSet = IntSet<Lit>;

#[allow(non_camel_case_types)]
#[derive(Clone, Copy)]
/// A ternary boolean (true, false, undefined) used for partial assignments.
pub struct lbool(u8);

impl fmt::Debug for lbool {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        if self.0 == 0 {
            write!(f, "TRUE")
        } else if self.0 == 1 {
            write!(f, "FALSE")
        } else if self.0 <= 3 {
            write!(f, "UNDEF")
        } else {
            // unreachable
            write!(f, "lbool({})", self.0)
        }
    }
}
impl Default for lbool {
    fn default() -> Self {
        lbool(0)
    }
}

impl lbool {
    pub const TRUE: lbool = lbool(0);
    pub const FALSE: lbool = lbool(1);
    pub const UNDEF: lbool = lbool(2);
    pub fn from_u8(v: u8) -> Self {
        debug_assert!(v == (v & 3), "lbool::from_u8: invalid value");
        lbool(v)
    }
    #[inline(always)]
    pub fn new(v: bool) -> Self {
        lbool((!v) as u8)
    }
    #[inline(always)]
    pub fn to_u8(&self) -> u8 {
        self.0
    }
}

// from minisat:
// bool operator == (lbool b) const { return ((b.value&2) & (value&2)) | (!(b.value&2)&(value == b.value)); }
impl PartialEq for lbool {
    #[inline(always)]
    fn eq(&self, rhs: &Self) -> bool {
        self.0 == rhs.0 || (self.0 & rhs.0 & 2) != 0
    }
}

impl Eq for lbool {}

impl ops::Neg for lbool {
    type Output = lbool;

    /// Negation of a `lbool`
    fn neg(self) -> Self {
        lbool(self.0 ^ 1)
    }
}

impl ops::BitXor<bool> for lbool {
    type Output = lbool;

    /// Xor of a lbool with a boolean.
    fn bitxor(self, rhs: bool) -> Self {
        lbool(self.0 ^ rhs as u8)
    }
}
impl ops::BitXorAssign<bool> for lbool {
    fn bitxor_assign(&mut self, rhs: bool) {
        *self = *self ^ rhs;
    }
}

impl ops::BitAnd for lbool {
    type Output = Self;
    fn bitand(self, rhs: Self) -> Self {
        // if self.0 == 1 || rhs.0 == 1 {
        //     1
        // } else if self.0 >= 2 || rhs.0 >= 2 {
        //     3
        // } else {
        //     0
        // }
        let sel = (self.0 << 1) | (rhs.0 << 3);
        let v = (0xF7F755F4_u32 >> sel) & 3;
        lbool(v as u8)
    }
}
impl ops::BitAndAssign for lbool {
    fn bitand_assign(&mut self, rhs: Self) {
        *self = *self & rhs;
    }
}

impl ops::BitOr for lbool {
    type Output = Self;
    fn bitor(self, rhs: Self) -> Self {
        // if self.0 == 0 || rhs.0 == 0 {
        //     0
        // } else if self.0 >= 2 || rhs.0 >= 2 {
        //     3
        // } else {
        //     0
        // }
        let sel = (self.0 << 1) | (rhs.0 << 3);
        let v = (0xFCFCF400_u32 >> sel) & 3;
        lbool(v as u8)
    }
}
impl ops::BitOrAssign for lbool {
    fn bitor_assign(&mut self, rhs: Self) {
        *self = *self | rhs;
    }
}

#[derive(Debug, Clone, Copy)]
/// A reference to some clause
pub(crate) struct ClauseRef<'a> {
    cref: CRef,
    header: ClauseHeader, // fast access
    alloc: &'a ClauseAllocator,
}
#[derive(Debug)]
/// A mutable reference to some clause, with a temporary lifetime
pub(crate) struct ClauseMut<'a> {
    cref: CRef,
    header: ClauseHeader, // fast access
    alloc: &'a mut ClauseAllocator,
}

impl<'a, 'b> PartialEq<ClauseRef<'b>> for ClauseRef<'a> {
    fn eq(&self, rhs: &ClauseRef<'b>) -> bool {
        self.cref == rhs.cref
    }
}
impl<'a> Eq for ClauseRef<'a> {}

impl<'a> ClauseRef<'a> {
    #[inline(always)]
    pub fn mark(&self) -> u32 {
        self.header.mark()
    }
    #[inline(always)]
    pub fn learnt(&self) -> bool {
        self.header.learnt()
    }
    #[inline(always)]
    #[allow(dead_code)]
    pub fn has_extra(&self) -> bool {
        self.header.has_extra()
    }
    #[inline(always)]
    pub fn reloced(&self) -> bool {
        self.header.reloced()
    }
    #[inline(always)]
    pub fn size(&self) -> u32 {
        self.header.size() as u32
    }
    #[inline(always)]
    pub fn activity(&self) -> f32 {
        self.alloc.activity[self.cref.0 as usize]
    }
    #[inline(always)]
    pub fn lits(&self) -> &'a [Lit] {
        let len = self.size() as usize;
        let offset = unsafe {self.alloc.offsets[self.cref.0 as usize].lit_idx} as usize;
        &self.alloc.lits[offset .. offset + len]
    }
    #[inline(always)]
    pub fn iter(& self) -> impl DoubleEndedIterator<Item=&'a Lit> {
        self.lits().iter()
    }
    pub fn extra(&self) -> Option<&u32> {
        self.alloc.extra.get(&self.cref)
    }
}

/// Anything that can be considered as a list of literals.
///
/// We use `Into` to have more flexibility for `ClauseRef`, which contains
/// a slice of a `union` type rather than pure literals
pub trait ClauseIterable: fmt::Debug {
    type Item : Copy + Into<Lit>;
    fn items(& self) -> &[Self::Item];
}

/// Any iterable clause can be printed in DIMACS
impl<T: ClauseIterable> display::Print for T {
    // display as DIMACS
    fn fmt_dimacs(&self, out: &mut fmt::Formatter) -> fmt::Result {
        for &x in self.items().iter() {
            let lit: Lit = x.into();
            write!(out, "{}{} ", (if lit.sign() {""} else {"-"}), lit.var().idx()+1)?;
        }
        write!(out, "0")?;
        Ok(())
    }
}

impl<'a> ClauseIterable for ClauseRef<'a> {
    type Item = Lit;
    fn items(& self) -> &[Self::Item] { self.lits() }
}

impl<'a> ClauseIterable for ClauseMut<'a> {
    type Item = Lit;
    fn items(& self) -> &[Self::Item] { self.lits() }
}

impl<'a> ClauseIterable for &'a [Lit] {
    type Item = Lit;
    fn items(&self) -> & [Self::Item] { &self }
}

impl ClauseIterable for Vec<Lit> {
    type Item = Lit;
    fn items(self: &Vec<Lit>) -> &[Self::Item] { &self }
}

impl ClauseIterable for IntSet<Lit> {
    type Item = Lit;
    fn items(&self) -> &[Self::Item] { self.as_slice() }
}

impl<'a> ClauseMut<'a> {
    #[inline(always)]
    pub fn reloced(&self) -> bool {
        self.header.reloced()
    }
    #[inline(always)]
    pub fn size(&self) -> u32 {
        self.header.size()
    }
    #[inline(always)]
    pub fn set_mark(&mut self, mark: u32) {
        debug_assert!(mark < 4);
        self.header.set_mark(mark);
    }
    #[inline(always)]
    pub fn set_reloced(&mut self, reloced: bool) {
        self.header.set_reloced(reloced);
    }
    #[inline(always)]
    pub fn activity(&self) -> f32 {
        self.alloc.activity[self.cref.0 as usize]
    }
    #[inline(always)]
    pub fn set_activity(&mut self, activity: f32) {
        self.alloc.activity[self.cref.0 as usize] = activity;
    }
    pub fn relocation(&self) -> CRef {
        debug_assert!(self.reloced());
        unsafe { self.alloc.offsets[self.cref.0 as usize].reloced }
    }
    pub fn relocate(mut self, c: CRef) {
        debug_assert!(!self.reloced());
        self.set_reloced(true);
        self.alloc.offsets[self.cref.0 as usize].reloced = c;
    }
    #[inline(always)]
    pub fn lits(&self) -> &[Lit] {
        let len = self.size() as usize;
        let offset = unsafe {self.alloc.offsets[self.cref.0 as usize].lit_idx as usize};
        &self.alloc.lits[offset .. offset + len]
    }
    pub fn lits_mut(&mut self) -> &mut [Lit] {
        let len = self.size() as usize;
        let offset = unsafe {self.alloc.offsets[self.cref.0 as usize].lit_idx as usize};
        &mut self.alloc.lits[offset .. offset + len]
    }
    pub fn iter(&self) -> impl DoubleEndedIterator<Item=&Lit> {
        self.lits().iter()
    }
    pub fn shrink(&mut self, new_size: u32) {
        debug_assert!(2 <= new_size);
        debug_assert!(new_size <= self.size());
        if new_size < self.size() {
            self.header.set_size(new_size);
        }
    }
    pub fn as_clause_ref(&mut self) -> ClauseRef {
        ClauseRef { cref: self.cref, header: self.header, alloc: self.alloc, }
    }
}

impl<'a> ops::Index<u32> for ClauseRef<'a> {
    type Output = Lit;
    fn index(&self, index: u32) -> &Self::Output {
        &self.lits()[index as usize]
    }
}
impl<'a> ops::Index<u32> for ClauseMut<'a> {
    type Output = Lit;
    fn index(&self, index: u32) -> &Self::Output {
        &self.lits()[index as usize]
    }
}
impl<'a> ops::IndexMut<u32> for ClauseMut<'a> {
    #[inline(always)]
    fn index_mut(&mut self, index: u32) -> &mut Self::Output {
        &mut self.lits_mut()[index as usize]
    }
}

/// Metadata of a clause
///
/// Layout:
/// unsigned mark      : 2;
/// unsigned learnt    : 1;
/// unsigned has_extra : 1;
/// unsigned reloced   : 1;
/// unsigned size      : 27;
#[derive(Clone, Copy)]
pub struct ClauseHeader(u32);

impl fmt::Debug for ClauseHeader {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        f.debug_struct("ClauseHeader")
            .field("mark", &self.mark())
            .field("learnt", &self.learnt())
            .field("has_extra", &self.has_extra())
            .field("reloced", &self.reloced())
            .field("size", &self.size())
            .finish()
    }
}

impl ClauseHeader {
    pub fn new(mark: u32, learnt: bool, has_extra: bool, reloced: bool, size: u32) -> Self {
        debug_assert!(mark < 4);
        debug_assert!(size < (1 << 27));
        ClauseHeader(
            (mark << 30) | ((learnt as u32) << 29) | ((has_extra as u32) << 28)
                | ((reloced as u32) << 27) | size,
        )
    }
    #[inline(always)]
    pub fn mark(&self) -> u32 {
        self.0 >> 30
    }
    #[inline(always)]
    pub fn learnt(&self) -> bool {
        (self.0 & (1 << 29)) != 0
    }
    #[inline(always)]
    pub fn has_extra(&self) -> bool {
        (self.0 & (1 << 28)) != 0
    }
    #[inline(always)]
    pub fn reloced(&self) -> bool {
        (self.0 & (1 << 27)) != 0
    }
    #[inline(always)]
    pub fn size(&self) -> u32 {
        self.0 & ((1 << 27) - 1)
    }
    pub fn set_mark(&mut self, mark: u32) {
        debug_assert!(mark < 4);
        self.0 = (self.0 & !(3 << 30)) | (mark << 30);
    }
    pub fn set_learnt(&mut self, learnt: bool) {
        self.0 = (self.0 & !(1 << 29)) | ((learnt as u32) << 29);
    }
    pub fn set_has_extra(&mut self, has_extra: bool) {
        self.0 = (self.0 & !(1 << 28)) | ((has_extra as u32) << 28);
    }
    pub fn set_reloced(&mut self, reloced: bool) {
        self.0 = (self.0 & !(1 << 27)) | ((reloced as u32) << 27);
    }
    pub fn set_size(&mut self, size: u32) {
        debug_assert!(size < (1 << 27));
        self.0 = (self.0 & !((1 << 27) - 1)) | size;
    }
}

impl AsIndex for CRef {
    #[inline(always)]
    fn as_index(self) -> usize { self.0 as usize }
    fn from_index(i:usize) -> Self { CRef(i as u32) }
}

impl CRef {
    pub const UNDEF : Self = CRef(0);
}

/// Main clause allocator. It stores a set of clauses efficiently.
#[derive(Debug)]
pub struct ClauseAllocator {
    headers: Vec<ClauseHeader>,
    offsets: Vec<OffsetData>, // offset in lits, or relocation address
    lits: Vec<Lit>,
    activity: Vec<f32>,
    extra: HashMap<CRef, u32>,
    extra_clause_field: bool,
    wasted: usize,
}

union OffsetData {
    lit_idx: u32,
    reloced: CRef,
}

impl fmt::Debug for OffsetData {
    fn fmt(&self, fmt: &mut fmt::Formatter) -> fmt::Result {
        write!(fmt, "offset_data")
    }
}


impl ClauseAllocator {
    pub const UNIT_SIZE: u32 = 32;
    pub fn with_start_cap(n: usize) -> Self {
        Self {
            headers: Vec::with_capacity(n),
            offsets: Vec::with_capacity(n),
            lits: Vec::with_capacity(n),
            activity: Vec::with_capacity(n),
            extra: HashMap::new(),
            extra_clause_field: false,
            wasted: 0,
        }
    }
    fn invariants(&self) -> bool {
        let len = self.headers.len();
        len == self.offsets.len() &&
        len == self.activity.len() &&
        self.lits.len() >= self.wasted
    }

    pub fn new() -> Self {
        Self::with_start_cap(1024 * 1024)
    }
    #[inline(always)]
    pub fn len(&self) -> usize {
        self.lits.len()
    }
    pub fn wasted(&self) -> usize {
        self.wasted
    }

    fn alloc_internal(&mut self, clause: &[Lit], h: ClauseHeader) -> CRef {
        debug_assert!(self.invariants());
        let cid = self.headers.len();
        let offset = self.lits.len();

        self.headers.push(h);
        self.offsets.push(OffsetData{lit_idx: offset as u32});
        self.activity.push(0.);
        self.lits.extend_from_slice(clause);

        let cref = CRef(cid as u32);

        if h.has_extra() {
            // NOTE: not used right now, but can be used to accelerate `lit_redundant`
            let mut abstraction: u32 = 0;
            for &lit in clause {
                abstraction |= 1 << (lit.var().idx() & 31);
            }
            self.extra.insert(cref, abstraction);
        }

        cref
    }

    pub(crate) fn alloc_with_learnt(&mut self, clause: &[Lit], learnt: bool) -> CRef {
        let use_extra = self.extra_clause_field;
        let h = ClauseHeader::new(0, learnt, use_extra, false, clause.len() as u32);
        self.alloc_internal(clause, h)
    }

    pub(crate) fn alloc_copy(&mut self, from: ClauseRef) -> CRef {
        let c = self.alloc_internal(from.lits(), from.header);
        if from.header.has_extra() {
            self.extra.insert(c, * from.extra().unwrap());
        }
        c
    }

    pub(crate) fn free(&mut self, cr: CRef) {
        let size = {
            let c = self.get_ref(cr);
            c.size() as usize
        };
        self.wasted += size;
    }

    pub fn free_amount(&mut self, size: usize) {
        self.wasted += size;
    }

    /// Relocate clause `cr` into allocator `to`.
    ///
    /// post condition: `*cr` now contains the index of the copy in `to`
    pub(crate) fn reloc(&mut self, cr: &mut CRef, to: &mut ClauseAllocator) {
        let mut c = self.get_mut(*cr);

        if c.reloced() {
            *cr = c.relocation();
            return;
        }

        *cr = to.alloc_copy(c.as_clause_ref());
        c.relocate(*cr);
    }

    /// Get a reference on the clause `cref` points to
    #[inline]
    pub(crate) fn get_ref<'a>(&'a self, cref: CRef) -> ClauseRef<'a> {
        let header = self.headers[cref.0 as usize];
        ClauseRef { alloc: self, cref, header, }
    }

    /// Get a mutable reference on the clause `cref` points to
    pub(crate) fn get_mut(&mut self, cref: CRef) -> ClauseMut {
        let header = self.headers[cref.0 as usize];
        ClauseMut { alloc: self, cref, header, }
    }
}

/// A clause is a reference into the allocator
#[derive(Debug,Clone,Copy,PartialEq,Eq,Hash)]
pub(crate) struct CRef(u32);

/// Predicate that decides whether a value `V` is deleted or not
pub trait DeletePred<V> {
    fn deleted(&self, &V) -> bool;
}

pub type OccVec<V> = SmallVec<[V;4]>;

#[derive(Debug, Clone)]
/// List of occurrences of objects of type `K` (e.g. literals) in values
/// of type `V` (e.g. clauses)
pub struct OccListsData<K: AsIndex, V> {
    occs: IntMap<K, OccVec<V>>,
    dirty: IntMapBool<K>,
    dirties: Vec<K>, // to know what keys to examine in `clean_all_pred`
}

impl<K: AsIndex, V> OccListsData<K, V> {
    pub fn new() -> Self {
        Self {
            occs: IntMap::new(),
            dirty: IntMapBool::new(),
            dirties: Vec::new(),
        }
    }

    /// Initialize occurrence list for the given `idx`
    pub fn init(&mut self, idx: K) {
        self.occs.reserve_default(idx);
        self.occs[idx].clear();
        self.dirty.reserve(idx);
    }

    /// Obtain a fully usable occurrence list using the given predicate
    pub fn promote<P: DeletePred<V>>(&mut self, pred: P) -> OccLists<K, V, P> {
        OccLists { data: self, pred: pred, }
    }

    /// `oclist.lookup_mut_pred(idx, p)` returns an up-to-date list of occurrences
    /// for `idx`. It will clean up the occurrence list with `p` if it's dirty.
    pub fn lookup_mut_pred<P: DeletePred<V>>(&mut self, idx: K, pred: &P) -> &mut OccVec<V> {
        if self.dirty[idx] {
            self.clean_pred(idx, pred);
        }
        &mut self.occs[idx]
    }

    /// Cleanup entries marked as `dirty` (remove elements for which the predicate
    /// specifies they're deleted)
    pub fn clean_all_pred<P: DeletePred<V>>(&mut self, pred: &P) {
        for &x in &self.dirties {
            // Dirties may contain duplicates so check here if a variable is already cleaned:
            if self.dirty[x] {
                self.occs[x].retain(|x| !pred.deleted(x));
                self.dirty.set(x, false);
            }
        }
        self.dirties.clear();
    }

    /// Cleanup entry at `idx`
    pub fn clean_pred<P: DeletePred<V>>(&mut self, idx: K, pred: &P) {
        self.occs[idx].retain(|x| !pred.deleted(x));
        self.dirty.set(idx, false);
    }

    /// Mark index `K` as dirty, so it can be cleaned up later
    pub fn smudge(&mut self, idx: K) {
        if !self.dirty[idx] {
            self.dirty.insert(idx);
            self.dirties.push(idx);
        }
    }

    /// Reset internal data
    pub fn clear(&mut self) {
        self.occs.clear();
        self.dirty.clear();
        self.dirties.clear();
    }

    /// Reset internal data and free memory
    pub fn free(&mut self) {
        self.occs.free();
        self.dirty.free();
        self.dirties.clear();
        self.dirties.shrink_to_fit();
    }
}

impl<K: AsIndex, V> ops::Index<K> for OccListsData<K, V> {
    type Output = OccVec<V>;
    fn index(&self, index: K) -> &Self::Output {
        &self.occs[index]
    }
}
impl<K: AsIndex, V> ops::IndexMut<K> for OccListsData<K, V> {
    fn index_mut(&mut self, index: K) -> &mut Self::Output {
        &mut self.occs[index]
    }
}

/// Packs together an occurrence list and the filtering predicate
pub struct OccLists<'a, K: AsIndex + 'a, V: 'a, P: DeletePred<V>> {
    data: &'a mut OccListsData<K, V>,
    pred: P,
}

impl<'a, K: AsIndex + 'a, V: 'a, P: DeletePred<V>> OccLists<'a, K, V, P> {
    pub fn lookup_mut(&mut self, idx: K) -> &mut OccVec<V> {
        self.data.lookup_mut_pred(idx, &self.pred)
    }

    pub fn clean_all(&mut self) {
        self.data.clean_all_pred(&self.pred)
    }

    pub fn clean(&mut self, idx: K) {
        self.data.clean_pred(idx, &self.pred)
    }
}

impl<'a, K: AsIndex + 'a, V: 'a, P: DeletePred<V>> ops::Deref for OccLists<'a, K, V, P> {
    type Target = OccListsData<K, V>;
    fn deref(&self) -> &Self::Target {
        &self.data
    }
}

impl<'a, K: AsIndex + 'a, V: 'a, P: DeletePred<V>> ops::DerefMut for OccLists<'a, K, V, P> {
    fn deref_mut(&mut self) -> &mut Self::Target {
        &mut self.data
    }
}

/// Generic interface for objects printable in DIMACS
pub mod display {
    use std::fmt;

    /// Objects that can be printed in DIMACS syntax
    pub trait Print : Sized {
        fn fmt_dimacs(&self, out: &mut fmt::Formatter) -> fmt::Result;

        /// Any type implementing `T` can  be used in a format string by
        /// just using `x.pp_dimacs()` instead of `x`.
        ///
        /// ```
        /// use batsat::*;
        /// let v: Vec<Lit> = vec![];
        /// format!("as dimacs: {}", v.pp_dimacs());
        /// ```
        fn pp_dimacs(&self) -> PrintWrapper<Self> { PrintWrapper(&self) }
    }

    /// A wrapper that can be used to display objects in format strings
    pub struct PrintWrapper<'a, T:'a+Print>(&'a T);

    // Whenever `T` is printable in DIMACS, its wrapper implements Display
    impl<'a,T:Print> fmt::Display for PrintWrapper<'a,T> {
        fn fmt(&self, out: &mut fmt::Formatter) -> fmt::Result {
            self.0.fmt_dimacs(out)
        }
    }
}

#[cfg(test)]
mod test {

    /// test that ClauseData doesn't waste space
    #[test]
    fn test_size_clause_data() {
        use std::mem;
        assert_eq!(mem::size_of::<super::OffsetData>(), 4);
    }

    #[test]
    fn test_eq() {
        use super::lbool;
        for i in 0..4 {
            let a = lbool::from_u8(i);
            for j in 0..4 {
                let b = lbool::from_u8(j);
                let are_eq =
                    (i==0 && j==0) ||
                    (i==1 && j==1) ||
                    (i >= 2 && j >= 2);
                assert_eq!(are_eq, a==b, "{:?}[{}] == {:?}[{}] should be {}",
                           a, i, b, j, are_eq);
            }
        }
    }

    #[test]
    fn test_not() {
        use super::lbool;
        assert_eq!(- lbool::TRUE, lbool::FALSE);
        assert_eq!(- lbool::FALSE, lbool::TRUE);
        assert_eq!(- lbool::UNDEF, lbool::UNDEF);
    }

    #[test]
    fn test_bitxor() {
        use super::lbool;
        assert_eq!(lbool::TRUE ^ true, lbool::FALSE);
        assert_eq!(lbool::TRUE ^ false, lbool::TRUE);
        assert_eq!(lbool::FALSE ^ true, lbool::TRUE);
        assert_eq!(lbool::FALSE ^ false, lbool::FALSE);
        assert_eq!(lbool::UNDEF ^ true, lbool::UNDEF);
        assert_eq!(lbool::UNDEF ^ false, lbool::UNDEF);
    }

    #[test]
    fn test_bitand() {
        use super::lbool;
        assert_eq!(lbool::TRUE & lbool::TRUE, lbool::TRUE);
        assert_eq!(lbool::TRUE & lbool::FALSE, lbool::FALSE);
        assert_eq!(lbool::FALSE & lbool::TRUE, lbool::FALSE);
        assert_eq!(lbool::FALSE & lbool::FALSE, lbool::FALSE);
        assert_eq!(lbool::UNDEF & lbool::FALSE, lbool::FALSE);
        assert_eq!(lbool::FALSE & lbool::UNDEF, lbool::FALSE);
        assert_eq!(lbool::UNDEF & lbool::TRUE, lbool::UNDEF);
        assert_eq!(lbool::TRUE & lbool::UNDEF, lbool::UNDEF);
    }

    #[test]
    fn test_bitor() {
        use super::lbool;
        assert_eq!(lbool::TRUE | lbool::TRUE, lbool::TRUE);
        assert_eq!(lbool::TRUE | lbool::FALSE, lbool::TRUE);
        assert_eq!(lbool::FALSE | lbool::TRUE, lbool::TRUE);
        assert_eq!(lbool::FALSE | lbool::FALSE, lbool::FALSE);
        assert_eq!(lbool::UNDEF | lbool::FALSE, lbool::UNDEF);
        assert_eq!(lbool::FALSE | lbool::UNDEF, lbool::UNDEF);
        assert_eq!(lbool::UNDEF | lbool::TRUE, lbool::TRUE);
        assert_eq!(lbool::TRUE | lbool::UNDEF, lbool::TRUE);
    }
}

