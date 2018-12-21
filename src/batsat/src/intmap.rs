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

use std::cmp;
use std::iter;
use std::ops;
use std::marker::PhantomData;
use bit_vec::BitVec;

pub trait AsIndex: Copy {
    fn as_index(self) -> usize;
    fn from_index(index: usize) -> Self;
}

#[derive(Debug, Clone)]
pub struct IntMap<K: AsIndex, V> {
    map: Vec<V>,
    _marker: PhantomData<fn(K)>, // contravariance
}

impl<K: AsIndex, V> Default for IntMap<K, V> {
    fn default() -> Self {
        Self { map: Vec::new(), _marker: PhantomData, }
    }
}

impl<K: AsIndex, V> IntMap<K, V> {
    pub fn new() -> Self { Self::default() }
    #[inline]
    pub fn has(&self, k: K) -> bool {
        k.as_index() < self.map.len()
    }
    pub fn reserve(&mut self, key: K, pad: V) where V: Clone {
        let index = key.as_index();
        if index >= self.map.len() {
            self.map.resize(index + 1, pad);
        }
    }
    pub fn reserve_default(&mut self, key: K) where V: Default {
        let index = key.as_index();
        if index >= self.map.len() {
            // self.map.resize_default(index + 1);
            let len = index + 1 - self.map.len();
            self.map.extend((0..len).map(|_| V::default()));
        }
    }
    #[inline]
    pub fn insert(&mut self, key: K, val: V, pad: V) where V: Clone {
        self.reserve(key, pad);
        self[key] = val;
    }
    pub fn insert_default(&mut self, key: K, val: V) where V: Default {
        self.reserve_default(key);
        self[key] = val;
    }

    /// Clear content, keep internal buffers. Does not allocate.
    pub fn clear(&mut self) {
        self.map.clear();
    }

    /// Clear content, free memory
    pub fn free(&mut self) {
        self.map.clear();
        self.map.shrink_to_fit();
    }
    pub fn iter(& self) -> impl iter::Iterator<Item=(K,&V)> {
        self.map.iter().enumerate().map(|(k, v)| (K::from_index(k), v))
    }
    pub fn iter_mut(&mut self) -> impl iter::Iterator<Item=(K,&mut V)> {
        self.map.iter_mut().enumerate().map(|(k, v)| (K::from_index(k), v))
    }
}

impl<K: AsIndex, V> ops::Index<K> for IntMap<K, V> {
    type Output = V;
    #[inline]
    fn index(&self, index: K) -> &Self::Output {
        &self.map[index.as_index()]
    }
}
impl<K: AsIndex, V> ops::IndexMut<K> for IntMap<K, V> {
    #[inline]
    fn index_mut(&mut self, index: K) -> &mut Self::Output {
        &mut self.map[index.as_index()]
    }
}

#[derive(Debug,Clone)]
pub struct IntMapBool<K : AsIndex> {
    map: BitVec,
    _marker: PhantomData<fn(K)>, // contravariance
}

impl<K: AsIndex> Default for IntMapBool<K> {
    fn default() -> Self { IntMapBool::new() }
}

impl<K: AsIndex> ops::Index<K> for IntMapBool<K> {
    type Output = bool;
    #[inline]
    fn index(&self, index: K) -> &Self::Output {
        &self.map[index.as_index()]
    }
}

impl<K: AsIndex> IntMapBool<K> {
    pub fn new() -> Self {
        Self { map: BitVec::new(), _marker: PhantomData::default(), }
    }
    #[inline]
    pub fn has(&self, k: K) -> bool {
        k.as_index() < self.map.len()
    }
    #[inline]
    pub fn set(&mut self, k: K, b: bool) {
        self.map.set(k.as_index(), b);
    }
    pub fn reserve(&mut self, key: K) {
        let index = key.as_index();
        let len = self.map.len();
        if index >= len {
            self.map.grow(index - len + 1, false);
        }
        debug_assert!(self.map.capacity() > index);
    }
    pub fn clear(&mut self) { self.map.clear(); }
    pub fn free(&mut self) {
        self.map.clear();
        self.map.shrink_to_fit();
    }
    #[inline]
    pub fn insert(&mut self, key: K) {
        self.reserve(key);
        self.map.set(key.as_index(), true);
    }
}

#[derive(Debug,Clone)]
pub struct IntSet<K: AsIndex> {
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

impl<K: AsIndex> IntSet<K> {
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
        self.in_set.reserve(k);
        if !self.in_set[k] {
            self.in_set.set(k, true);
            self.xs.push(k);
        }
    }
    pub fn has(&self, k: K) -> bool {
        self.in_set.has(k) && self.in_set[k]
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
    fn deref(&self) -> &Self::Target { &self.xs }
}

#[derive(Debug, Clone)]
pub struct HeapData<K: AsIndex> {
    heap: Vec<K>,
    indices: IntMap<K, i32>,
}

impl<K: AsIndex> Default for HeapData<K> {
    fn default() -> Self {
        Self { heap: Vec::new(), indices: IntMap::new(), }
    }
}

impl<K: AsIndex> HeapData<K> {
    pub fn new() -> Self {
        Self::default()
    }
    pub fn len(&self) -> usize {
        self.heap.len()
    }
    pub fn is_empty(&self) -> bool {
        self.heap.is_empty()
    }
    pub fn in_heap(&self, k: K) -> bool {
        self.indices.has(k) && self.indices[k] >= 0
    }

    pub fn promote<Comp: Comparator<K>>(&mut self, comp: Comp) -> Heap<K, Comp> {
        Heap { data: self, comp: comp, }
    }
}

impl<K: AsIndex> ops::Index<usize> for HeapData<K> {
    type Output = K;
    fn index(&self, index: usize) -> &Self::Output {
        &self.heap[index]
    }
}

pub trait Comparator<T: ?Sized> {
    fn cmp(&self, lhs: &T, rhs: &T) -> cmp::Ordering;
    fn max(&self, lhs: T, rhs: T) -> T where T: Sized {
        if self.ge(&rhs, &lhs) { rhs } else { lhs }
    }
    fn min(&self, lhs: T, rhs: T) -> T where T: Sized {
        if self.le(&lhs, &rhs) { lhs } else { rhs }
    }
    fn le(&self, lhs: &T, rhs: &T) -> bool {
        match self.cmp(lhs, rhs) {
            cmp::Ordering::Less | cmp::Ordering::Equal => true,
            _ => false,
        }
    }
    fn lt(&self, lhs: &T, rhs: &T) -> bool {
        match self.cmp(lhs, rhs) {
            cmp::Ordering::Less => true,
            _ => false,
        }
    }
    #[inline]
    fn gt(&self, lhs: &T, rhs: &T) -> bool { self.lt(rhs, lhs) }
    #[inline]
    fn ge(&self, lhs: &T, rhs: &T) -> bool { self.le(rhs, lhs) }
}

#[derive(Debug)]
pub struct Heap<'a, K: AsIndex + 'a, Comp: Comparator<K>> {
    data: &'a mut HeapData<K>,
    comp: Comp,
}

impl<'a, K: AsIndex + 'a, Comp: Comparator<K>> ops::Deref for Heap<'a, K, Comp> {
    type Target = HeapData<K>;
    fn deref(&self) -> &Self::Target {
        &self.data
    }
}
impl<'a, K: AsIndex + 'a, Comp: Comparator<K>> ops::DerefMut for Heap<'a, K, Comp> {
    fn deref_mut(&mut self) -> &mut Self::Target {
        &mut self.data
    }
}

impl<'a, K: AsIndex + 'a, Comp: Comparator<K>> Heap<'a, K, Comp> {
    fn percolate_up(&mut self, mut i: u32) {
        let x = self.heap[i as usize];
        let mut p = parent_index(i);

        while i != 0 && self.comp.lt(&x, &self.heap[p as usize]) {
            self.heap[i as usize] = self.heap[p as usize];
            let tmp = self.heap[p as usize];
            self.indices[tmp] = i as i32;
            i = p;
            p = parent_index(p);
        }
        self.heap[i as usize] = x;
        self.indices[x] = i as i32;
    }

    fn percolate_down(&mut self, mut i: u32) {
        let x = self.heap[i as usize];
        while (left_index(i) as usize) < self.heap.len() {
            let child = if (right_index(i) as usize) < self.heap.len()
                && self.comp.lt(
                    &self.heap[right_index(i) as usize],
                    &self.heap[left_index(i) as usize],
                ) {
                right_index(i)
            } else {
                left_index(i)
            };
            if !self.comp.lt(&self.heap[child as usize], &x) {
                break;
            }
            self.heap[i as usize] = self.heap[child as usize];
            let tmp = self.heap[i as usize];
            self.indices[tmp] = i as i32;
            i = child;
        }
        self.heap[i as usize] = x;
        self.indices[x] = i as i32;
    }
    pub fn decrease(&mut self, k: K) {
        debug_assert!(self.in_heap(k));
        let k_index = self.indices[k];
        self.percolate_up(k_index as u32);
    }
    pub fn increase(&mut self, k: K) {
        debug_assert!(self.in_heap(k));
        let k_index = self.indices[k];
        self.percolate_down(k_index as u32);
    }

    /// Safe variant of insert/decrease/increase:
    pub fn update(&mut self, k: K) {
        if !self.in_heap(k) {
            self.insert(k);
        } else {
            let k_index = self.indices[k];
            self.percolate_up(k_index as u32);
            let k_index = self.indices[k];
            self.percolate_down(k_index as u32);
        }
    }

    pub fn insert(&mut self, k: K) {
        self.indices.reserve(k, -1);
        debug_assert!(!self.in_heap(k));

        self.indices[k] = self.heap.len() as i32;
        self.heap.push(k);
        let k_index = self.indices[k];
        self.percolate_up(k_index as u32);
    }

    pub fn remove(&mut self, k: K) {
        debug_assert!(self.in_heap(k));
        let k_pos = self.indices[k] as u32;
        self.indices[k] = -1;
        if (k_pos as usize) < self.heap.len() - 1 {
            self.heap[k_pos as usize] = *self.heap.last().unwrap();
            let tmp = self.heap[k_pos as usize];
            self.indices[tmp] = k_pos as i32;
            self.heap.pop().expect("cannot pop from empty heap");
            self.percolate_down(k_pos);
        } else {
            self.heap.pop().expect("cannot pop from empty heap");
        }
    }

    pub fn remove_min(&mut self) -> K {
        let x = *self.heap.first().expect("heap is empty");
        let lastval = *self.heap.last().expect("heap is empty");
        self.heap[0] = lastval;
        self.indices[lastval] = 0;
        self.indices[x] = -1;
        self.heap.pop().expect("cannot pop from empty heap");
        if self.heap.len() > 1 {
            self.percolate_down(0);
        }
        x
    }

    /// Rebuild the heap from scratch, using the elements in 'ns':
    pub fn build(&mut self, ns: &[K]) {
        {
            let data = &mut self.data;
            for &x in &data.heap {
                data.indices[x] = -1;
            }
        }
        self.heap.clear();

        for (i, &x) in ns.iter().enumerate() {
            // TODO: this should probably call reserve instead of relying on it being reserved already.
            debug_assert!(self.indices.has(x));
            self.indices[x] = i as i32;
            self.heap.push(x);
        }

        let mut i = self.heap.len() as i32 / 2 - 1;
        while i >= 0 {
            self.percolate_down(i as u32);
            i -= 1;
        }
    }

    pub fn clear_dispose(&mut self, dispose: bool) {
        // TODO: shouldn't the 'indices' map also be dispose-cleared?
        {
            let data = &mut self.data;
            for &x in &data.heap {
                data.indices[x] = -1;
            }
        }
        self.heap.clear();
        if dispose {
            self.heap.shrink_to_fit();
        }
    }

    pub fn clear(&mut self) {
        self.clear_dispose(false)
    }
}

#[inline(always)]
fn left_index(i: u32) -> u32 {
    i * 2 + 1
}
#[inline(always)]
fn right_index(i: u32) -> u32 {
    (i + 1) * 2
}
#[inline(always)]
fn parent_index(i: u32) -> u32 {
    (i.wrapping_sub(1)) >> 1
}
