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
    pub fn alloc(&mut self, size: u32) -> Ref<T> {
        debug_assert!(size > 0);
        let r = Ref(self.vec.len() as u32, PhantomData);
        self.vec.extend((0..size).map(|_| T::default()));
        r
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

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Default)]
pub struct Ref<T: Copy>(u32, PhantomData<fn(T) -> T>);

impl<T: Copy> Ref<T> {
    pub const UNDEF: Self = Ref(!0, PhantomData);
}

impl<T: Copy> ops::Add<u32> for Ref<T> {
    type Output = Ref<T>;
    fn add(self, rhs: u32) -> Self::Output {
        Ref(self.0 + rhs, PhantomData)
    }
}
