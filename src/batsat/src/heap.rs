use crate::intmap::{AsIndex, IntMap};
use std::fmt::Debug;
use std::{cmp, mem, ops};

/// Quaternary Heap
#[derive(Debug, Clone)]
pub struct HeapData<K: AsIndex, V> {
    heap: Box<[(K, V)]>,
    next_slot: usize,
    indices: IntMap<K, i32>,
}

impl<K: AsIndex, V> Default for HeapData<K, V> {
    fn default() -> Self {
        Self {
            heap: Box::new([]),
            next_slot: 0,
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
        self.next_slot <= ROOT as usize
    }
    pub fn in_heap(&self, k: K) -> bool {
        self.indices.has(k) && self.indices[k] >= 0
    }

    pub fn promote<Comp: Comparator<(K, V)>>(&mut self, comp: Comp) -> Heap<K, V, Comp> {
        Heap { data: self, comp }
    }

    /// Raw mutable access to all the elements of the heap
    pub(crate) fn heap_mut(&mut self) -> &mut [(K, V)] {
        if self.next_slot == 0 {
            &mut []
        } else {
            &mut self.heap[ROOT as usize..self.next_slot]
        }
    }
}

impl<K: AsIndex, V> ops::Index<usize> for HeapData<K, V> {
    type Output = K;
    fn index(&self, index: usize) -> &Self::Output {
        &self.heap[index].0
    }
}

pub trait Comparator<T: ?Sized> {
    type Comp: Ord;

    fn max_value(&self) -> T;
    fn to_cmp_form(&self, v: &T) -> Self::Comp;
    fn from_cmp_form(&self, c: Self::Comp) -> T;

    fn cmp(&self, lhs: &T, rhs: &T) -> cmp::Ordering {
        self.to_cmp_form(&lhs).cmp(&self.to_cmp_form(&rhs))
    }
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
    // ensure size is always a multiple of 4
    #[cold]
    #[inline(never)]
    fn heap_reserve(&mut self) {
        debug_assert_eq!(self.next_slot, self.data.len());
        if self.next_slot == 0 {
            self.next_slot = ROOT as usize;
            // Enough space for the root and 4 children
            self.heap = vec![self.comp.max_value(); 8].into_boxed_slice();
        } else {
            let new_size = self.next_slot << 2;
            let mut heap = mem::replace(&mut self.heap, Box::new([])).into_vec();
            heap.resize(new_size, self.comp.max_value());
            self.heap = heap.into_boxed_slice();
        }
    }

    #[inline]
    fn heap_push(&mut self, k: K, v: V) -> u32 {
        if self.next_slot >= self.heap.len() {
            self.heap_reserve();
            assert!(self.next_slot < self.heap.len());
        }
        let slot = self.next_slot;
        self.heap[slot] = (k, v);
        self.next_slot += 1;
        slot as u32
    }

    fn percolate_up(&mut self, mut i: u32) {
        let x = self.heap[i as usize];
        let xc = self.comp.to_cmp_form(&x);
        let mut p = parent_index(i);

        while i != ROOT && xc < self.comp.to_cmp_form(&self.heap[p as usize]) {
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
        let x = self.comp.to_cmp_form(&self.heap[i as usize]);
        let len = (self.next_slot + 3) & (usize::MAX - 3); // round up to nearest multiple of 4
                                                           // since the heap is padded with maximum values we can pretend that these are part of the
                                                           // heap but never swap with them
        let heap = &mut self.data.heap[..len];
        loop {
            let min = |x: (u32, Comp::Comp), y: (u32, Comp::Comp)| if x.1 < y.1 { x } else { y };
            let left_index = left_index(i);
            let Some(arr) = heap.get(left_index as usize..left_index as usize + 4) else {
                break;
            };
            let bundle = |x| (left_index + x, self.comp.to_cmp_form(&arr[x as usize]));
            let b0 = bundle(0);
            let b1 = bundle(1);
            let b2 = bundle(2);
            let b3 = bundle(3);
            let b01 = min(b0, b1);
            let b23 = min(b2, b3);
            let (child, min) = min(b01, b23);
            if min > x {
                break;
            }
            let min = self.comp.from_cmp_form(min);
            heap[i as usize] = min;
            self.data.indices[min.0] = i as i32;
            i = child;
        }
        let x = self.comp.from_cmp_form(x);
        heap[i as usize] = x;
        self.data.indices[x.0] = i as i32;
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
        let k_index = self.heap_push(k, self.comp.value(k));
        self.indices[k] = k_index as i32;
        self.percolate_up(k_index);
    }

    pub fn remove_min(&mut self) -> K {
        assert!(!self.is_empty(), "cannot pop from empty heap");
        let x = self.heap[ROOT as usize];
        let last = self.next_slot - 1;
        self.next_slot = last;
        self.indices[x.0] = -1;
        if self.is_empty() {
            self.heap[last] = self.comp.max_value();
            return x.0;
        }
        let lastval = self.heap[last];
        self.heap[last] = self.comp.max_value();
        self.heap[ROOT as usize] = lastval;
        self.indices[lastval.0] = ROOT as i32;
        self.percolate_down(ROOT);
        x.0
    }
}

/// Root of the quaternary heap
/// By using 3 as the root we ensure each chunk of 4 children has a multiple of 4 starting index
/// This gives the chunks a better chance of being cache aligned, i.e. they are cache aligned if
/// the allocation is cache aligned
const ROOT: u32 = 3;

#[inline(always)]
fn left_index(i: u32) -> u32 {
    (i - 2) << 2
}
#[inline(always)]
fn parent_index(i: u32) -> u32 {
    (i >> 2) + 2
}
