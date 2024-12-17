use crate::intmap::{AsIndex, IntMap};
use core::fmt::Formatter;
use default_vec2::ConstDefault;
use no_std_compat::prelude::v1::*;
use std::fmt::Debug;
use std::{mem, ops};

/// Quaternary Heap
#[derive(Debug, Clone)]
pub struct HeapData<K: AsIndex, V> {
    heap: Box<[V]>,
    next_slot: usize,
    indices: IntMap<K, HeapIndex>,
}

#[derive(Copy, Clone)]
struct HeapIndex(i32);

impl Debug for HeapIndex {
    fn fmt(&self, f: &mut Formatter<'_>) -> core::fmt::Result {
        self.0.fmt(f)
    }
}

impl Default for HeapIndex {
    fn default() -> Self {
        HeapIndex(-1)
    }
}

impl HeapIndex {
    fn idx(self) -> usize {
        self.0 as usize
    }
}

impl ConstDefault for HeapIndex {
    const DEFAULT: &'static Self = &HeapIndex(-1);
}

impl<K: AsIndex, V> Default for HeapData<K, V> {
    fn default() -> Self {
        Self {
            heap: Box::new([]),
            next_slot: 0,
            indices: IntMap::default(),
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
        self.indices[k].0 >= 0
    }

    pub fn promote<Comp: CachedKeyComparator<K, Key = V>>(&mut self, comp: Comp) -> Heap<K, Comp> {
        Heap { data: self, comp }
    }

    /// Raw mutable access to all the elements of the heap
    pub(crate) fn heap_mut(&mut self) -> &mut [V] {
        if self.next_slot == 0 {
            &mut []
        } else {
            &mut self.heap[ROOT as usize..self.next_slot]
        }
    }
}

impl<K: AsIndex, V> ops::Index<usize> for HeapData<K, V> {
    type Output = V;
    fn index(&self, index: usize) -> &Self::Output {
        &self.heap[index]
    }
}

pub trait CachedKeyComparator<T> {
    type Key: Ord + Copy;

    fn cache_key(&self, t: T) -> Self::Key;

    fn max_key(&self) -> Self::Key;

    fn un_cache_key(&self, k: Self::Key) -> T;
}

#[derive(Debug)]
pub struct Heap<'a, K: AsIndex + 'a, Comp: CachedKeyComparator<K>> {
    data: &'a mut HeapData<K, Comp::Key>,
    comp: Comp,
}

impl<'a, K: AsIndex + 'a, Comp: CachedKeyComparator<K>> ops::Deref for Heap<'a, K, Comp> {
    type Target = HeapData<K, Comp::Key>;
    fn deref(&self) -> &Self::Target {
        &self.data
    }
}
impl<'a, K: AsIndex + 'a, Comp: CachedKeyComparator<K>> ops::DerefMut for Heap<'a, K, Comp> {
    fn deref_mut(&mut self) -> &mut Self::Target {
        &mut self.data
    }
}

impl<'a, K: AsIndex + 'a, Comp: CachedKeyComparator<K>> Heap<'a, K, Comp> {
    // ensure size is always a multiple of 4
    #[cold]
    #[inline(never)]
    fn heap_reserve(&mut self) {
        debug_assert_eq!(self.next_slot, self.data.len());
        if self.next_slot == 0 {
            self.next_slot = ROOT as usize;
            // Enough space for the root and 4 children
            self.heap = vec![self.comp.max_key(); 8].into_boxed_slice();
        } else {
            let new_size = self.next_slot << 2;
            let mut heap = mem::replace(&mut self.heap, Box::new([])).into_vec();
            heap.resize(new_size, self.comp.max_key());
            self.heap = heap.into_boxed_slice();
        }
    }

    #[inline]
    fn heap_push(&mut self, k: Comp::Key) -> u32 {
        if self.next_slot >= self.heap.len() {
            self.heap_reserve();
            assert!(self.next_slot < self.heap.len());
        }
        let slot = self.next_slot;
        self.heap[slot] = k;
        self.next_slot += 1;
        slot as u32
    }

    fn percolate_up(&mut self, mut i: u32) {
        let x = self.heap[i as usize];
        let mut p = parent_index(i);

        while i != ROOT && x < self.heap[p as usize] {
            self.heap[i as usize] = self.heap[p as usize];
            let tmp = self.heap[p as usize];
            self.data.indices[self.comp.un_cache_key(tmp)] = HeapIndex(i as i32);
            i = p;
            p = parent_index(p);
        }
        self.heap[i as usize] = x;
        self.data.indices[self.comp.un_cache_key(x)] = HeapIndex(i as i32);
    }

    fn percolate_down(&mut self, mut i: u32) {
        let x = self.heap[i as usize];
        let len = (self.next_slot + 3) & (usize::MAX - 3); // round up to nearest multiple of 4
                                                           // since the heap is padded with maximum values we can pretend that these are part of the
                                                           // heap but never swap with them
        let heap = &mut self.data.heap[..len];
        loop {
            let min = |x: (u32, Comp::Key), y: (u32, Comp::Key)| if x.1 < y.1 { x } else { y };
            let left_index = left_index(i);
            let Some(arr) = heap.get(left_index as usize..left_index as usize + 4) else {
                break;
            };
            let bundle = |x| (left_index + x, arr[x as usize]);
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
            heap[i as usize] = min;
            self.data.indices[self.comp.un_cache_key(min)] = HeapIndex(i as i32);
            i = child;
        }
        heap[i as usize] = x;
        self.data.indices[self.comp.un_cache_key(x)] = HeapIndex(i as i32);
    }

    pub fn decrease(&mut self, k: K) {
        debug_assert!(self.in_heap(k));
        let k_index = self.indices[k];
        self.heap[k_index.idx()] = self.comp.cache_key(k);
        self.percolate_up(k_index.0 as u32);
    }

    pub fn insert(&mut self, k: K) {
        debug_assert!(!self.in_heap(k));
        let k_index = self.heap_push(self.comp.cache_key(k));
        self.indices[k] = HeapIndex(k_index as i32);
        self.percolate_up(k_index);
    }

    pub fn remove_min(&mut self) -> K {
        assert!(!self.is_empty(), "cannot pop from empty heap");
        let x = self.heap[ROOT as usize];
        let last = self.next_slot - 1;
        self.next_slot = last;
        let x_var = self.comp.un_cache_key(x);
        self.indices[x_var] = HeapIndex::default();
        if self.is_empty() {
            self.heap[last] = self.comp.max_key();
            return x_var;
        }
        let lastval = self.heap[last];
        self.heap[last] = self.comp.max_key();
        self.heap[ROOT as usize] = lastval;
        self.data.indices[self.comp.un_cache_key(lastval)] = HeapIndex(ROOT as i32);
        self.percolate_down(ROOT);
        self.comp.un_cache_key(x)
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
