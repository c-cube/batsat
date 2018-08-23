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
use std::ops;
use std::slice;
use std::u32;

use intmap::{AsIndex, IntMap, IntSet};
use alloc::{self, RegionAllocator};

#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub struct Var(u32);

impl fmt::Debug for Var {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        if self.0 == !0 {
            write!(f, "UNDEF")
        } else {
            write!(f, "Var({})", self.0)
        }
    }
}

impl Var {
    pub const UNDEF: Var = Var(!0);
    pub(crate) fn from_idx(idx: u32) -> Self {
        debug_assert!(idx < u32::MAX / 2, "Var::from_idx: index too large");
        Var(idx)
    }
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

#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub struct Lit(u32);

impl Lit {
    pub const UNDEF: Lit = Lit(!1);
    pub const ERROR: Lit = Lit(!0);
    pub fn new(var: Var, sign: bool) -> Self {
        Lit(var.0 * 2 + sign as u32)
    }
    pub(crate) fn from_idx(idx: u32) -> Self {
        Lit(idx)
    }
    pub fn idx(&self) -> u32 {
        self.0
    }
    pub fn sign(&self) -> bool {
        (self.0 & 1) != 0
    }
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
            write!(f, "Lit({}, {})", self.0 / 2, (self.0 & 1) != 0)
        }
    }
}

impl ops::Not for Lit {
    type Output = Self;
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
    fn as_index(self) -> usize {
        self.0 as usize
    }
    fn from_index(index: usize) -> Self {
        Lit(index as u32)
    }
}

pub type LMap<V> = IntMap<Lit, V>;
pub type LSet = IntSet<Lit>;

#[allow(non_camel_case_types)]
#[derive(Clone, Copy)]
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
    pub fn new(v: bool) -> Self {
        lbool((!v) as u8)
    }
    pub fn to_u8(&self) -> u8 {
        self.0
    }
}

impl PartialEq for lbool {
    fn eq(&self, rhs: &Self) -> bool {
        self.0 == rhs.0 || (self.0 & rhs.0 & 2) != 0
    }
}

impl Eq for lbool {}

impl ops::Neg for lbool {
    type Output = lbool;
    fn neg(self) -> Self {
        if self.0 == 0 { lbool::FALSE }
        else if self.0 == 1 { lbool::TRUE }
        else { lbool::UNDEF }
    }
}

impl ops::BitXor<bool> for lbool {
    type Output = lbool;
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
pub struct ClauseRef<'a> {
    header: ClauseHeader,
    data: &'a [ClauseData],
    extra: Option<ClauseData>,
}
#[derive(Debug)]
pub struct ClauseMut<'a> {
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
    pub fn mark(&self) -> u32 {
        self.header.mark()
    }
    pub fn learnt(&self) -> bool {
        self.header.learnt()
    }
    pub fn has_extra(&self) -> bool {
        self.header.has_extra()
    }
    pub fn reloced(&self) -> bool {
        self.header.reloced()
    }
    pub fn size(&self) -> u32 {
        self.data.len() as u32
    }
    pub fn activity(&self) -> f32 {
        debug_assert!(self.has_extra());
        unsafe { self.extra.expect("no extra field").f32 }
    }
    pub fn abstraction(&self) -> u32 {
        debug_assert!(self.has_extra());
        unsafe { self.extra.expect("no extra field").u32 }
    }
    pub fn relocation(&self) -> CRef {
        debug_assert!(self.reloced());
        unsafe { self.data[0].cref }
    }
    pub fn iter(&self) -> ClauseIter {
        ClauseIter(self.data.iter())
    }
}
impl<'a> ClauseMut<'a> {
    pub fn mark(&self) -> u32 {
        self.header.mark()
    }
    pub fn learnt(&self) -> bool {
        self.header.learnt()
    }
    pub fn has_extra(&self) -> bool {
        self.header.has_extra()
    }
    pub fn reloced(&self) -> bool {
        self.header.reloced()
    }
    pub fn size(&self) -> u32 {
        self.data.len() as u32
    }
    pub fn set_mark(&mut self, mark: u32) {
        debug_assert!(mark < 4);
        self.header.set_mark(mark);
    }
    pub fn set_learnt(&mut self, learnt: bool) {
        self.header.set_learnt(learnt);
    }
    pub fn set_has_extra(&mut self, has_extra: bool) {
        self.header.set_has_extra(has_extra);
    }
    pub fn set_reloced(&mut self, reloced: bool) {
        self.header.set_reloced(reloced);
    }
    pub fn activity(&self) -> f32 {
        debug_assert!(self.has_extra());
        unsafe { self.extra.as_ref().expect("no extra field").f32 }
    }
    pub fn set_activity(&mut self, activity: f32) {
        debug_assert!(self.has_extra());
        self.extra.as_mut().expect("no extra field").f32 = activity;
    }
    pub fn abstraction(&self) -> u32 {
        debug_assert!(self.has_extra());
        unsafe { self.extra.as_ref().expect("no extra field").u32 }
    }
    pub fn set_abstraction(&mut self, abstraction: u32) {
        debug_assert!(self.has_extra());
        self.extra.as_mut().expect("no extra field").u32 = abstraction;
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
    pub fn iter(&self) -> ClauseIter {
        ClauseIter(self.data.iter())
    }
    pub fn iter_mut(&mut self) -> ClauseIterMut {
        ClauseIterMut(self.data.iter_mut())
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
    fn index(&self, index: u32) -> &Self::Output {
        unsafe { &self.data[index as usize].lit }
    }
}
impl<'a> ops::Index<u32> for ClauseMut<'a> {
    type Output = Lit;
    fn index(&self, index: u32) -> &Self::Output {
        unsafe { &self.data[index as usize].lit }
    }
}
impl<'a> ops::IndexMut<u32> for ClauseMut<'a> {
    fn index_mut(&mut self, index: u32) -> &mut Self::Output {
        unsafe { &mut self.data[index as usize].lit }
    }
}

#[derive(Debug, Clone)]
pub struct ClauseIter<'a>(slice::Iter<'a, ClauseData>);

impl<'a> Iterator for ClauseIter<'a> {
    type Item = &'a Lit;
    fn next(&mut self) -> Option<Self::Item> {
        self.0.next().map(|lit| unsafe { &lit.lit })
    }
    fn size_hint(&self) -> (usize, Option<usize>) {
        self.0.size_hint()
    }
}
impl<'a> DoubleEndedIterator for ClauseIter<'a> {
    fn next_back(&mut self) -> Option<Self::Item> {
        self.0.next_back().map(|lit| unsafe { &lit.lit })
    }
}

#[derive(Debug)]
pub struct ClauseIterMut<'a>(slice::IterMut<'a, ClauseData>);

impl<'a> Iterator for ClauseIterMut<'a> {
    type Item = &'a mut Lit;
    fn next(&mut self) -> Option<Self::Item> {
        self.0.next().map(|lit| unsafe { &mut lit.lit })
    }
    fn size_hint(&self) -> (usize, Option<usize>) {
        self.0.size_hint()
    }
}
impl<'a> DoubleEndedIterator for ClauseIterMut<'a> {
    fn next_back(&mut self) -> Option<Self::Item> {
        self.0.next_back().map(|lit| unsafe { &mut lit.lit })
    }
}

#[derive(Debug)]
pub struct ClauseAllocator {
    ra: RegionAllocator<ClauseData>,
    extra_clause_field: bool,
}
#[derive(Clone, Copy)]
pub union ClauseData {
    u32: u32,
    f32: f32,
    cref: CRef,
    header: ClauseHeader,
    lit: Lit,
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

// unsigned mark      : 2;
// unsigned learnt    : 1;
// unsigned has_extra : 1;
// unsigned reloced   : 1;
// unsigned size      : 27;
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
    pub fn mark(&self) -> u32 {
        self.0 >> 30
    }
    pub fn learnt(&self) -> bool {
        (self.0 & (1 << 29)) != 0
    }
    pub fn has_extra(&self) -> bool {
        (self.0 & (1 << 28)) != 0
    }
    pub fn reloced(&self) -> bool {
        (self.0 & (1 << 27)) != 0
    }
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
    pub fn len(&self) -> u32 {
        self.ra.len()
    }
    pub fn wasted(&self) -> u32 {
        self.ra.wasted()
    }
    pub fn alloc_with_learnt(&mut self, clause: &[Lit], learnt: bool) -> CRef {
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
                let mut abstraction: u32 = 0;
                for &lit in clause {
                    abstraction |= 1 << (lit.var().idx() & 31);
                }
                self.ra[clause_ptr + clause.len() as u32].u32 = abstraction;
            }
        }

        cid
    }
    pub fn alloc(&mut self, clause: &[Lit]) -> CRef {
        self.alloc_with_learnt(clause, false)
    }
    pub fn alloc_copy(&mut self, from: ClauseRef) -> CRef {
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

    pub fn free(&mut self, cr: CRef) {
        let size = {
            let c = self.get_ref(cr);
            1 + c.size() + c.has_extra() as u32
        };
        self.ra.free(size);
    }

    pub fn free_amount(&mut self, size: u32) {
        self.ra.free(size);
    }

    pub fn reloc(&mut self, cr: &mut CRef, to: &mut ClauseAllocator) {
        let mut c = self.get_mut(*cr);

        if c.reloced() {
            *cr = c.relocation();
            return;
        }

        *cr = to.alloc_copy(c.as_clause_ref());
        c.relocate(*cr);
    }

    pub fn get_ref(&self, cr: CRef) -> ClauseRef {
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
    pub fn get_mut(&mut self, cr: CRef) -> ClauseMut {
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

pub type CRef = alloc::Ref<ClauseData>;

pub trait DeletePred<V> {
    fn deleted(&self, &V) -> bool;
}

#[derive(Debug, Clone)]
pub struct OccListsData<K: AsIndex, V> {
    occs: IntMap<K, Vec<V>>,
    dirty: IntMap<K, bool>,
    dirties: Vec<K>,
}

impl<K: AsIndex, V> OccListsData<K, V> {
    pub fn new() -> Self {
        Self {
            occs: IntMap::new(),
            dirty: IntMap::new(),
            dirties: Vec::new(),
        }
    }
    pub fn init(&mut self, idx: K) {
        self.occs.reserve_default(idx);
        self.occs[idx].clear();
        self.dirty.reserve(idx, false);
    }

    pub fn promote<P: DeletePred<V>>(&mut self, pred: P) -> OccLists<K, V, P> {
        OccLists {
            data: self,
            pred: pred,
        }
    }

    pub fn lookup_mut_pred<P: DeletePred<V>>(&mut self, idx: K, pred: &P) -> &mut Vec<V> {
        if self.dirty[idx] {
            self.clean_pred(idx, pred);
        }
        &mut self.occs[idx]
    }

    pub fn clean_all_pred<P: DeletePred<V>>(&mut self, pred: &P) {
        for &x in &self.dirties {
            // Dirties may contain duplicates so check here if a variable is already cleaned:
            if self.dirty[x] {
                // self.clean(x, pred)
                self.occs[x].retain(|x| !pred.deleted(x));
                self.dirty[x] = false;
            }
        }
        self.dirties.clear();
    }

    pub fn clean_pred<P: DeletePred<V>>(&mut self, idx: K, pred: &P) {
        self.occs[idx].retain(|x| !pred.deleted(x));
        self.dirty[idx] = false;
    }

    pub fn smudge(&mut self, idx: K) {
        if !self.dirty[idx] {
            self.dirty[idx] = true;
            self.dirties.push(idx);
        }
    }

    pub fn clear(&mut self) {
        self.occs.clear();
        self.dirty.clear();
        self.dirties.clear();
    }

    pub fn free(&mut self) {
        self.occs.free();
        self.dirty.free();
        self.dirties.clear();
        self.dirties.shrink_to_fit();
    }
}

impl<K: AsIndex, V> ops::Index<K> for OccListsData<K, V> {
    type Output = Vec<V>;
    fn index(&self, index: K) -> &Self::Output {
        &self.occs[index]
    }
}
impl<K: AsIndex, V> ops::IndexMut<K> for OccListsData<K, V> {
    fn index_mut(&mut self, index: K) -> &mut Self::Output {
        &mut self.occs[index]
    }
}

pub struct OccLists<'a, K: AsIndex + 'a, V: 'a, P: DeletePred<V>> {
    data: &'a mut OccListsData<K, V>,
    pred: P,
}

impl<'a, K: AsIndex + 'a, V: 'a, P: DeletePred<V>> OccLists<'a, K, V, P> {
    pub fn lookup_mut(&mut self, idx: K) -> &mut Vec<V> {
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
