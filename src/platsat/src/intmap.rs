/*****************************************************************************************[intmap.rs]
Copyright (c) 2003-2006, Niklas Een, Niklas Sorensson (MiniSat)
Copyright (c) 2007-2011, Niklas Sorensson (MiniSat)
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
use no_std_compat::prelude::v1::*;
use std::ops;

pub(crate) trait AsIndex: Copy + From<usize> + Into<usize> {}

impl<T: Copy + From<usize> + Into<usize>> AsIndex for T {}

pub(crate) type IntMap<K, V> = default_vec2::DefaultVec<V, K>;

pub(crate) type IntMapBool<K> = default_vec2::BitSet<K>;

#[derive(Debug, Clone)]
pub struct IntSet<K: Copy + From<usize> + Into<usize>> {
    in_set: IntMapBool<K>,
    xs: Vec<K>,
}
impl<K: AsIndex> Default for IntSet<K> {
    fn default() -> Self {
        Self {
            in_set: IntMapBool::default(),
            xs: vec![],
        }
    }
}

impl<K: Copy + From<usize> + Into<usize>> IntSet<K> {
    pub fn new() -> Self {
        Self::default()
    }
    pub fn len(&self) -> usize {
        self.xs.len()
    }
    pub fn clear(&mut self) {
        self.in_set.clear();
        self.xs.clear()
    }
    pub fn as_slice(&self) -> &[K] {
        &self.xs
    }
    pub fn insert(&mut self, k: K) {
        if self.in_set.insert(k) {
            self.xs.push(k)
        }
    }
    pub fn has(&self, k: K) -> bool {
        self.in_set.contains(k)
    }
}
impl<K: AsIndex> ops::Index<usize> for IntSet<K> {
    type Output = K;
    fn index(&self, index: usize) -> &Self::Output {
        &self.xs[index]
    }
}

impl<K: AsIndex> ops::Deref for IntSet<K> {
    type Target = [K];
    fn deref(&self) -> &Self::Target {
        &self.xs
    }
}
