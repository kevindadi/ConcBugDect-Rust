//! Strongly typed index vector for safe indexed access over sequential containers.
use std::fmt;
use std::marker::PhantomData;
use std::ops::{Index, IndexMut};

use serde::{Deserialize, Deserializer, Serialize, Serializer};

/// Trait implemented by identifier types that can index into [ IndexVec ].
pub trait Idx: Copy + Eq + PartialEq + Ord + fmt::Debug {
    fn index(self) -> usize;
    fn from_usize(idx: usize) -> Self;
}

/// A vector indexed by strongly typed identifiers.
#[derive(Clone, PartialEq, Eq, Hash)]
pub struct IndexVec<I, T> {
    data: Vec<T>,
    _marker: PhantomData<I>,
}

impl<I, T> IndexVec<I, T>
where
    I: Idx,
{
    pub fn new() -> Self {
        Self {
            data: Vec::new(),
            _marker: PhantomData,
        }
    }

    pub fn from_vec(data: Vec<T>) -> Self {
        Self {
            data,
            _marker: PhantomData,
        }
    }

    pub fn push(&mut self, value: T) -> I {
        let idx = self.data.len();
        self.data.push(value);
        I::from_usize(idx)
    }

    pub fn len(&self) -> usize {
        self.data.len()
    }

    pub fn is_empty(&self) -> bool {
        self.data.is_empty()
    }

    pub fn iter(&self) -> impl Iterator<Item = &T> {
        self.data.iter()
    }

    pub fn iter_enumerated(&self) -> impl Iterator<Item = (I, &T)> {
        self.data
            .iter()
            .enumerate()
            .map(|(idx, value)| (I::from_usize(idx), value))
    }

    pub fn iter_mut(&mut self) -> impl Iterator<Item = &mut T> {
        self.data.iter_mut()
    }

    pub fn get(&self, index: I) -> Option<&T> {
        self.data.get(index.index())
    }

    pub fn get_mut(&mut self, index: I) -> Option<&mut T> {
        self.data.get_mut(index.index())
    }

    pub fn into_vec(self) -> Vec<T> {
        self.data
    }
}

impl<I, T> Default for IndexVec<I, T>
where
    I: Idx,
{
    fn default() -> Self {
        Self::new()
    }
}

impl<I, T> fmt::Debug for IndexVec<I, T>
where
    I: Idx,
    T: fmt::Debug,
{
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_list().entries(self.data.iter()).finish()
    }
}

impl<I, T> Index<I> for IndexVec<I, T>
where
    I: Idx,
{
    type Output = T;

    fn index(&self, index: I) -> &Self::Output {
        &self.data[index.index()]
    }
}

impl<I, T> IndexMut<I> for IndexVec<I, T>
where
    I: Idx,
{
    fn index_mut(&mut self, index: I) -> &mut Self::Output {
        &mut self.data[index.index()]
    }
}

impl<I, T> IntoIterator for IndexVec<I, T>
where
    I: Idx,
{
    type Item = T;
    type IntoIter = std::vec::IntoIter<T>;

    fn into_iter(self) -> Self::IntoIter {
        self.data.into_iter()
    }
}

impl<I, T> From<Vec<T>> for IndexVec<I, T>
where
    I: Idx,
{
    fn from(value: Vec<T>) -> Self {
        Self::from_vec(value)
    }
}

impl<I, T> Serialize for IndexVec<I, T>
where
    I: Idx,
    T: Serialize,
{
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: Serializer,
    {
        self.data.serialize(serializer)
    }
}

impl<'de, I, T> Deserialize<'de> for IndexVec<I, T>
where
    I: Idx,
    T: Deserialize<'de>,
{
    fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
    where
        D: Deserializer<'de>,
    {
        let data = Vec::<T>::deserialize(deserializer)?;
        Ok(Self {
            data,
            _marker: PhantomData,
        })
    }
}
