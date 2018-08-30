/*****************************************************************************************[alloc.rs]
Copyright (c) 2008-2010, Niklas Sorensson (MiniSat)
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

use std::cmp;
use std::fmt;
use std::marker::PhantomData;
use std::ops;

#[derive(Debug)]
pub struct RegionAllocator<T: Copy> {
    vec: Vec<T>,
    wasted: usize,
}

impl<T: Copy + Default> RegionAllocator<T> {
    pub fn new(start_cap: u32) -> Self {
        Self {
            vec: Vec::with_capacity(start_cap as usize),
            wasted: 0,
        }
    }
    pub fn len(&self) -> u32 {
        self.vec.len() as u32
    }
    pub fn wasted(&self) -> u32 {
        self.wasted as u32
    }
    pub fn alloc(&mut self, size: u32) -> Ref<T> {
        debug_assert!(size > 0);
        let r = Ref(self.vec.len() as u32, PhantomData);
        self.vec.extend((0..size).map(|_| T::default()));
        r
    }
    pub fn free(&mut self, size: u32) {
        self.wasted += size as usize;
    }
    pub fn subslice(&self, r: Ref<T>, len: u32) -> &[T] {
        &self.vec[r.0 as usize..r.0 as usize + len as usize]
    }
    pub fn subslice_mut(&mut self, r: Ref<T>, len: u32) -> &mut [T] {
        &mut self.vec[r.0 as usize..r.0 as usize + len as usize]
    }
}

impl<T: Copy> ops::Index<Ref<T>> for RegionAllocator<T> {
    type Output = T;
    fn index(&self, index: Ref<T>) -> &Self::Output {
        &self.vec[index.0 as usize]
    }
}
impl<T: Copy> ops::IndexMut<Ref<T>> for RegionAllocator<T> {
    fn index_mut(&mut self, index: Ref<T>) -> &mut Self::Output {
        &mut self.vec[index.0 as usize]
    }
}

#[derive(Clone, Copy)]
/// A reference to a `T` value living in the allocator.
///
/// The reference is invariant in `T`.
pub struct Ref<T: Copy>(u32, PhantomData<fn(T) -> T>);

impl<T: Copy> fmt::Debug for Ref<T> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        f.debug_tuple("Ref").field(&self.0).finish()
    }
}
impl<T: Copy> PartialEq for Ref<T> {
    #[inline(always)]
    fn eq(&self, rhs: &Self) -> bool {
        self.0 == rhs.0
    }
}
impl<T: Copy> Eq for Ref<T> {}
impl<T: Copy> PartialOrd for Ref<T> {
    fn partial_cmp(&self, rhs: &Self) -> Option<cmp::Ordering> {
        PartialOrd::partial_cmp(&self.0, &rhs.0)
    }
}
impl<T: Copy> Ord for Ref<T> {
    #[inline(always)]
    fn cmp(&self, rhs: &Self) -> cmp::Ordering {
        Ord::cmp(&self.0, &rhs.0)
    }
}
impl<T: Copy> Default for Ref<T> {
    fn default() -> Self {
        Ref(0, PhantomData)
    }
}

impl<T: Copy> Ref<T> {
    pub const UNDEF: Self = Ref(!0, PhantomData);
}

impl<T: Copy> ops::Add<u32> for Ref<T> {
    type Output = Ref<T>;
    fn add(self, rhs: u32) -> Self::Output {
        Ref(self.0 + rhs, PhantomData)
    }
}
