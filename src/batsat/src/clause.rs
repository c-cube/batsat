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

use {
    crate::{
        alloc::{self, RegionAllocator},
        intmap::{AsIndex, IntMap, IntMapBool, IntSet},
    },
    std::{fmt, iter::DoubleEndedIterator, ops, slice, u32},
};

#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
#[repr(transparent)]
pub struct Var(u32);

impl fmt::Debug for Var {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        if self.0 == !0 {
            write!(f, "UNDEF")
        } else {
            write!(f, "{}", self.0 + 1)
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

    /// Make a variable from the index. This should only be used
    /// with integers obtained from an existing `v.idx()`
    #[inline]
    pub fn unsafe_from_idx(idx: u32) -> Self {
        Var::from_idx(idx)
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
#[repr(transparent)]
pub struct Lit(u32);

impl Lit {
    pub const UNDEF: Lit = Lit(!1);
    pub const ERROR: Lit = Lit(!0);

    #[inline(always)]
    pub fn new(var: Var, sign: bool) -> Self {
        Lit(var.0 * 2 + (!sign) as u32)
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

    /// `lit.apply_sign(b)` keeps the same sign if `b==true`, flips sign otherwise
    ///
    /// ```
    /// use batsat::*;
    /// let mut sat = BasicSolver::default();
    /// let lit1 = Lit::new(sat.new_var_default(), true);
    /// assert_eq!(lit1, lit1.apply_sign(true));
    /// assert_eq!(!lit1, lit1.apply_sign(false));
    /// let lit2 = Lit::new(sat.new_var_default(), false);
    /// assert_ne!(lit1.var(), lit2.var());
    /// assert_eq!(lit2, lit2.apply_sign(true));
    /// assert_eq!(!lit2, lit2.apply_sign(false));
    /// ```
    #[inline(always)]
    pub fn apply_sign(&self, sign: bool) -> Lit {
        if sign {
            *self
        } else {
            !*self
        }
    }
}

impl fmt::Debug for Lit {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        if self.0 == !0 {
            write!(f, "ERROR")
        } else if self.0 == !1 {
            write!(f, "UNDEF")
        } else {
            write!(f, "{}{:?}", if self.sign() { "" } else { "-" }, self.var())
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

impl From<bool> for lbool {
    fn from(x: bool) -> Self {
        if x {
            lbool::TRUE
        } else {
            lbool::FALSE
        }
    }
}

/// The source of a clause
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Kind {
    Axiom,
    Learnt,
    Theory,
}

#[derive(Debug, Clone, Copy)]
/// A reference to some clause
pub(crate) struct ClauseRef<'a> {
    header: ClauseHeader,
    data: &'a [ClauseData],
    extra: Option<ClauseData>,
}
#[derive(Debug)]
/// A mutable reference to some clause, with a temporary lifetime
pub(crate) struct ClauseMut<'a> {
    header: &'a mut ClauseHeader,
    data: &'a mut [ClauseData],
    extra: Option<&'a mut ClauseData>,
}

impl<'a, 'b> PartialEq<ClauseRef<'b>> for ClauseRef<'a> {
    fn eq(&self, rhs: &ClauseRef<'b>) -> bool {
        self.data.as_ptr() == rhs.data.as_ptr()
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
    pub fn has_extra(&self) -> bool {
        self.header.has_extra()
    }
    #[inline(always)]
    pub fn reloced(&self) -> bool {
        self.header.reloced()
    }
    #[inline(always)]
    pub fn size(&self) -> u32 {
        self.header.size()
    }
    #[inline(always)]
    pub fn activity(&self) -> f32 {
        debug_assert!(self.has_extra());
        unsafe { self.extra.expect("no extra field").f32 }
    }
    #[inline(always)]
    pub fn lits(&self) -> &'a [Lit] {
        let ptr = self.data.as_ptr() as *const ClauseData as *const Lit;
        unsafe { slice::from_raw_parts(ptr, self.data.len()) }
    }
    #[inline(always)]
    pub fn iter(&self) -> impl DoubleEndedIterator<Item = &'a Lit> {
        self.lits().iter()
    }
}

/// Anything that can be considered as a list of literals.
///
/// We use `Into` to have more flexibility for `ClauseRef`, which contains
/// a slice of a `union` type rather than pure literals
pub trait ClauseIterable: fmt::Debug {
    type Item: Copy + Into<Lit>;
    fn items(&self) -> &[Self::Item];
}

/// Any iterable clause can be printed in DIMACS
impl<T: ClauseIterable> display::Print for T {
    // display as DIMACS
    fn fmt_dimacs(&self, out: &mut fmt::Formatter) -> fmt::Result {
        for &x in self.items().iter() {
            let lit: Lit = x.into();
            write!(
                out,
                "{}{} ",
                (if lit.sign() { "" } else { "-" }),
                lit.var().idx() + 1
            )?;
        }
        write!(out, "0")?;
        Ok(())
    }
}

impl<'a> ClauseIterable for ClauseRef<'a> {
    type Item = Lit;
    fn items(&self) -> &[Self::Item] {
        unsafe { slice::from_raw_parts(self.data.as_ptr() as *const Lit, self.data.len()) }
    }
}

impl<'a> ClauseIterable for ClauseMut<'a> {
    type Item = Lit;
    fn items(&self) -> &[Self::Item] {
        unsafe { slice::from_raw_parts(self.data.as_ptr() as *const Lit, self.data.len()) }
    }
}

impl<'a> ClauseIterable for &'a [Lit] {
    type Item = Lit;
    fn items(&self) -> &[Self::Item] {
        &self
    }
}

impl ClauseIterable for Vec<Lit> {
    type Item = Lit;
    fn items(self: &Vec<Lit>) -> &[Self::Item] {
        &self
    }
}

impl ClauseIterable for IntSet<Lit> {
    type Item = Lit;
    fn items(&self) -> &[Self::Item] {
        self.as_slice()
    }
}

impl<'a> ClauseMut<'a> {
    #[inline(always)]
    pub fn has_extra(&self) -> bool {
        self.header.has_extra()
    }
    #[inline(always)]
    pub fn reloced(&self) -> bool {
        self.header.reloced()
    }
    #[inline(always)]
    pub fn size(&self) -> u32 {
        self.data.len() as u32
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
        debug_assert!(self.has_extra());
        unsafe { self.extra.as_ref().expect("no extra field").f32 }
    }
    #[inline(always)]
    pub fn set_activity(&mut self, activity: f32) {
        debug_assert!(self.has_extra());
        self.extra.as_mut().expect("no extra field").f32 = activity;
    }
    pub fn relocation(&self) -> CRef {
        debug_assert!(self.reloced());
        unsafe { self.data[0].cref }
    }
    pub fn relocate(mut self, c: CRef) {
        debug_assert!(!self.reloced());
        self.set_reloced(true);
        self.data[0].cref = c;
    }
    pub fn shrink(self, new_size: u32) {
        debug_assert!(2 <= new_size);
        debug_assert!(new_size <= self.size());
        if new_size < self.size() {
            self.header.set_size(new_size);
            if let Some(extra) = self.extra {
                self.data[new_size as usize] = *extra;
            }
        }
    }
    pub fn as_clause_ref(&mut self) -> ClauseRef {
        ClauseRef {
            header: *self.header,
            data: self.data,
            extra: self.extra.as_mut().map(|extra| **extra),
        }
    }
}

impl<'a> ops::Index<u32> for ClauseRef<'a> {
    type Output = Lit;
    #[inline(always)]
    fn index(&self, index: u32) -> &Self::Output {
        unsafe { &self.data[index as usize].lit }
    }
}
impl<'a> ops::Index<u32> for ClauseMut<'a> {
    type Output = Lit;
    #[inline(always)]
    fn index(&self, index: u32) -> &Self::Output {
        unsafe { &self.data[index as usize].lit }
    }
}
impl<'a> ops::IndexMut<u32> for ClauseMut<'a> {
    #[inline(always)]
    fn index_mut(&mut self, index: u32) -> &mut Self::Output {
        unsafe { &mut self.data[index as usize].lit }
    }
}

#[derive(Debug)]
/// Main clause allocator. It stores a set of clauses efficiently.
pub struct ClauseAllocator {
    ra: RegionAllocator<ClauseData>,
    extra_clause_field: bool,
}

#[repr(C)]
#[derive(Clone, Copy)]
/// Items used in the clause allocator. It should be compact enough that
/// we do no waste space.
pub(crate) union ClauseData {
    u32: u32,
    f32: f32,
    cref: CRef,
    header: ClauseHeader,
    lit: Lit,
}

impl Into<Lit> for ClauseData {
    fn into(self: ClauseData) -> Lit {
        unsafe { self.lit }
    }
}

impl Default for ClauseData {
    fn default() -> Self {
        ClauseData { u32: 0 }
    }
}
impl fmt::Debug for ClauseData {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "ClauseData({})", unsafe { self.u32 })
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
            (mark << 30)
                | ((learnt as u32) << 29)
                | ((has_extra as u32) << 28)
                | ((reloced as u32) << 27)
                | size,
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

impl ClauseAllocator {
    pub const UNIT_SIZE: u32 = 32;
    pub fn with_start_cap(start_cap: u32) -> Self {
        Self {
            ra: RegionAllocator::new(start_cap),
            extra_clause_field: false,
        }
    }
    pub fn new() -> Self {
        Self::with_start_cap(1024 * 1024)
    }
    #[inline(always)]
    pub fn len(&self) -> u32 {
        self.ra.len()
    }
    pub fn wasted(&self) -> u32 {
        self.ra.wasted()
    }
    pub(crate) fn alloc_with_learnt(&mut self, clause: &[Lit], learnt: bool) -> CRef {
        let use_extra = learnt | self.extra_clause_field;
        let cid = self.ra.alloc(1 + clause.len() as u32 + use_extra as u32);
        self.ra[cid].header = ClauseHeader::new(0, learnt, use_extra, false, clause.len() as u32);
        let clause_ptr = cid + 1;
        for (i, &lit) in clause.iter().enumerate() {
            self.ra[clause_ptr + i as u32].lit = lit;
        }
        if use_extra {
            if learnt {
                self.ra[clause_ptr + clause.len() as u32].f32 = 0.0;
            } else {
                // NOTE: not used right now, but can be used to accelerate `lit_redundant`
                let mut abstraction: u32 = 0;
                for &lit in clause {
                    abstraction |= 1 << (lit.var().idx() & 31);
                }
                self.ra[clause_ptr + clause.len() as u32].u32 = abstraction;
            }
        }

        cid
    }

    pub(crate) fn alloc_copy(&mut self, from: ClauseRef) -> CRef {
        let use_extra = from.learnt() | self.extra_clause_field;
        let cid = self.ra.alloc(1 + from.size() + use_extra as u32);
        self.ra[cid].header = from.header;
        // NOTE: the copied clause may lose the extra field.
        unsafe { &mut self.ra[cid].header }.set_has_extra(use_extra);
        for (i, &lit) in from.iter().enumerate() {
            self.ra[cid + 1 + i as u32].lit = lit;
        }
        if use_extra {
            self.ra[cid + 1 + from.size()] = from.extra.unwrap();
        }
        cid
    }

    pub(crate) fn free(&mut self, cr: CRef) {
        let size = {
            let c = self.get_ref(cr);
            1 + c.size() + c.has_extra() as u32
        };
        self.ra.free(size);
    }

    pub fn free_amount(&mut self, size: u32) {
        self.ra.free(size);
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

    /// Get a reference on the clause `cr` points to
    pub(crate) fn get_ref<'a>(&'a self, cr: CRef) -> ClauseRef<'a> {
        let header = unsafe { self.ra[cr].header };
        let has_extra = header.has_extra();
        let size = header.size();

        let data = self.ra.subslice(cr + 1, size);
        let extra = if has_extra {
            Some(self.ra[cr + 1 + size])
        } else {
            None
        };
        ClauseRef {
            header,
            data,
            extra,
        }
    }

    /// Get a mutable reference on the clause `cr` points to
    pub(crate) fn get_mut(&mut self, cr: CRef) -> ClauseMut {
        let header = unsafe { self.ra[cr].header };
        let has_extra = header.has_extra();
        let size = header.size();
        let len = 1 + size + has_extra as u32;

        let subslice = self.ra.subslice_mut(cr, len);
        let (subslice0, subslice) = subslice.split_at_mut(1);
        let (subslice1, subslice2) = subslice.split_at_mut(size as usize);
        ClauseMut {
            header: unsafe { &mut subslice0[0].header },
            data: subslice1,
            extra: subslice2.first_mut(),
        }
    }
}

pub(crate) type CRef = alloc::Ref<ClauseData>;

/// Predicate that decides whether a value `V` is deleted or not
pub trait DeletePred<V> {
    fn deleted(&self, v: &V) -> bool;
}

pub type OccVec<V> = Vec<V>;

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
        OccLists { data: self, pred }
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
    pub trait Print: Sized {
        fn fmt_dimacs(&self, out: &mut fmt::Formatter) -> fmt::Result;

        /// Any type implementing `T` can  be used in a format string by
        /// just using `x.pp_dimacs()` instead of `x`.
        ///
        /// ```
        /// use batsat::*;
        /// let v: Vec<Lit> = vec![];
        /// format!("as dimacs: {}", v.pp_dimacs());
        /// ```
        fn pp_dimacs(&self) -> PrintWrapper<Self> {
            PrintWrapper(&self)
        }
    }

    /// A wrapper that can be used to display objects in format strings
    pub struct PrintWrapper<'a, T: 'a + Print>(&'a T);

    // Whenever `T` is printable in DIMACS, its wrapper implements Display
    impl<'a, T: Print> fmt::Display for PrintWrapper<'a, T> {
        fn fmt(&self, out: &mut fmt::Formatter) -> fmt::Result {
            self.0.fmt_dimacs(out)
        }
    }
}

#[cfg(test)]
mod test {
    use super::*;

    /// test that ClauseData doesn't waste space
    #[test]
    fn test_size_clause_data() {
        use std::mem;
        assert_eq!(mem::size_of::<super::ClauseData>(), 4);
    }

    #[test]
    fn test_eq() {
        use super::lbool;
        for i in 0..4 {
            let a = lbool::from_u8(i);
            for j in 0..4 {
                let b = lbool::from_u8(j);
                let are_eq = (i == 0 && j == 0) || (i == 1 && j == 1) || (i >= 2 && j >= 2);
                assert_eq!(
                    are_eq,
                    a == b,
                    "{:?}[{}] == {:?}[{}] should be {}",
                    a,
                    i,
                    b,
                    j,
                    are_eq
                );
            }
        }
    }

    #[test]
    fn test_not() {
        assert_eq!(-lbool::TRUE, lbool::FALSE);
        assert_eq!(-lbool::FALSE, lbool::TRUE);
        assert_eq!(-lbool::UNDEF, lbool::UNDEF);
    }

    #[test]
    fn test_bitxor() {
        assert_eq!(lbool::TRUE ^ true, lbool::FALSE);
        assert_eq!(lbool::TRUE ^ false, lbool::TRUE);
        assert_eq!(lbool::FALSE ^ true, lbool::TRUE);
        assert_eq!(lbool::FALSE ^ false, lbool::FALSE);
        assert_eq!(lbool::UNDEF ^ true, lbool::UNDEF);
        assert_eq!(lbool::UNDEF ^ false, lbool::UNDEF);
    }

    #[test]
    fn test_bitand() {
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

    #[test]
    fn test_cref_undef_special() {
        assert_eq!(CRef::UNDEF, CRef::SPECIAL + 1);
    }
}
