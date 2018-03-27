use std::fmt;
use std::ops;
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
}

pub type VMap<V> = IntMap<Var, V>;

#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub struct Lit(u32);

impl Lit {
    pub const UNDEF: Lit = Lit(!1);
    pub const ERROR: Lit = Lit(!0);
    pub(crate) fn new(var: Var, sign: bool) -> Self {
        Lit(var.0 * 2 + sign as u32)
    }
    pub(crate) fn new_positive(var: Var) -> Self {
        Self::new(var, false)
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

pub struct ClauseRef<'a> {
    header: ClauseHeader,
    data: &'a [ClauseData],
    extra: Option<ClauseData>,
}
pub struct ClauseMut<'a> {
    header: &'a mut ClauseHeader,
    data: &'a mut [ClauseData],
    extra: Option<&'a mut ClauseData>,
}

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
    pub fn with_start_cap(start_cap: u32) -> Self {
        Self {
            ra: RegionAllocator::new(start_cap),
            extra_clause_field: false,
        }
    }
    pub fn new() -> Self {
        Self::with_start_cap(1024 * 1024)
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
