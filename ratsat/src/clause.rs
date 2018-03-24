use std::fmt;
use std::ops;
use std::u32;

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub struct Var(u32);

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
        write!(f, "Lit({}, {})", self.0 / 2, (self.0 & 1) != 0)
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

#[allow(non_camel_case_types)]
#[derive(Debug, Clone, Copy, Default)]
pub struct lbool(u8);

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
