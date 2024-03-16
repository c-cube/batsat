use crate::intmap::{AsIndex, IntMap};
use std::{cmp, ops};

#[derive(Debug, Clone)]
pub struct HeapData<K: AsIndex, V> {
    heap: Vec<(K, V)>,
    indices: IntMap<K, i32>,
}

impl<K: AsIndex, V> Default for HeapData<K, V> {
    fn default() -> Self {
        Self {
            heap: Vec::new(),
            indices: IntMap::new(),
        }
    }
}

impl<K: AsIndex, V> HeapData<K, V> {
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

    pub fn promote<Comp: Comparator<(K, V)>>(&mut self, comp: Comp) -> Heap<K, V, Comp> {
        Heap { data: self, comp }
    }
}

impl<K: AsIndex, V> ops::Index<usize> for HeapData<K, V> {
    type Output = K;
    fn index(&self, index: usize) -> &Self::Output {
        &self.heap[index].0
    }
}

pub trait Comparator<T: ?Sized> {
    fn cmp(&self, lhs: &T, rhs: &T) -> cmp::Ordering;
    fn max(&self, lhs: T, rhs: T) -> T
    where
        T: Sized,
    {
        if self.ge(&rhs, &lhs) {
            rhs
        } else {
            lhs
        }
    }
    fn min(&self, lhs: T, rhs: T) -> T
    where
        T: Sized,
    {
        if self.le(&lhs, &rhs) {
            lhs
        } else {
            rhs
        }
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
    fn gt(&self, lhs: &T, rhs: &T) -> bool {
        self.lt(rhs, lhs)
    }
    #[inline]
    fn ge(&self, lhs: &T, rhs: &T) -> bool {
        self.le(rhs, lhs)
    }
}

pub trait MemoComparator<K, V>: Comparator<(K, V)> {
    fn value(&self, k: K) -> V;
}

#[derive(Debug)]
pub struct Heap<'a, K: AsIndex + 'a, V: 'a, Comp> {
    data: &'a mut HeapData<K, V>,
    comp: Comp,
}

impl<'a, K: AsIndex + 'a, V: 'a, Comp> ops::Deref for Heap<'a, K, V, Comp> {
    type Target = HeapData<K, V>;
    fn deref(&self) -> &Self::Target {
        &self.data
    }
}
impl<'a, K: AsIndex + 'a, V: 'a, Comp> ops::DerefMut for Heap<'a, K, V, Comp> {
    fn deref_mut(&mut self) -> &mut Self::Target {
        &mut self.data
    }
}

impl<'a, K: AsIndex + 'a, V: Copy + 'a, Comp: MemoComparator<K, V>> Heap<'a, K, V, Comp> {
    fn percolate_up(&mut self, mut i: u32) {
        let x = self.heap[i as usize];
        let mut p = parent_index(i);

        while i != 0 && self.comp.lt(&x, &self.heap[p as usize]) {
            self.heap[i as usize] = self.heap[p as usize];
            let tmp = self.heap[p as usize];
            self.indices[tmp.0] = i as i32;
            i = p;
            p = parent_index(p);
        }
        self.heap[i as usize] = x;
        self.indices[x.0] = i as i32;
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
            self.indices[tmp.0] = i as i32;
            i = child;
        }
        self.heap[i as usize] = x;
        self.indices[x.0] = i as i32;
    }

    pub fn decrease(&mut self, k: K) {
        debug_assert!(self.in_heap(k));
        let k_index = self.indices[k];
        self.heap[k_index as usize].1 = self.comp.value(k);
        self.percolate_up(k_index as u32);
    }

    pub fn insert(&mut self, k: K) {
        self.indices.reserve(k, -1);
        debug_assert!(!self.in_heap(k));

        self.indices[k] = self.heap.len() as i32;
        self.data.heap.push((k, self.comp.value(k)));
        let k_index = self.indices[k];
        self.percolate_up(k_index as u32);
    }

    pub fn remove_min(&mut self) -> K {
        let x = *self.heap.first().expect("heap is empty");
        let lastval = *self.heap.last().expect("heap is empty");
        self.heap[0] = lastval;
        self.indices[lastval.0] = 0;
        self.indices[x.0] = -1;
        self.heap.pop().expect("cannot pop from empty heap");
        if self.heap.len() > 1 {
            self.percolate_down(0);
        }
        x.0
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
