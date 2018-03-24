use std::ops;
use std::marker::PhantomData;

pub trait AsIndex: Copy {
    fn as_index(self) -> usize;
}

#[derive(Debug)]
pub struct IntMap<K: AsIndex, V> {
    map: Vec<V>,
    _marker: PhantomData<fn(K)>,
}

impl<K: AsIndex, V> Default for IntMap<K, V> {
    fn default() -> Self {
        Self {
            map: vec![],
            _marker: PhantomData,
        }
    }
}
impl<K: AsIndex, V> Clone for IntMap<K, V>
where
    V: Clone,
{
    fn clone(&self) -> Self {
        Self {
            map: self.map.clone(),
            _marker: PhantomData,
        }
    }
}

impl<K: AsIndex, V> IntMap<K, V> {
    pub fn new() -> Self {
        Self::default()
    }
    pub fn reserve(&mut self, key: K, pad: V)
    where
        V: Clone,
    {
        let index = key.as_index();
        if index >= self.map.len() {
            self.map.resize(index + 1, pad);
        }
    }
    pub fn insert(&mut self, key: K, val: V, pad: V)
    where
        V: Clone,
    {
        self.reserve(key, pad);
        self[key] = val;
    }
}

impl<K: AsIndex, V> ops::Index<K> for IntMap<K, V> {
    type Output = V;
    fn index(&self, index: K) -> &Self::Output {
        &self.map[index.as_index()]
    }
}
impl<K: AsIndex, V> ops::IndexMut<K> for IntMap<K, V> {
    fn index_mut(&mut self, index: K) -> &mut Self::Output {
        &mut self.map[index.as_index()]
    }
}
