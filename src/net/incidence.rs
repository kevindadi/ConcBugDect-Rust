//! Sparse incidence matrices for input/output (and extended) arc relations.
use std::fmt;
use std::ops::{Add, Sub};

use serde::{Deserialize, Serialize};
use smallvec::SmallVec;

use crate::net::ids::{PlaceId, TransitionId};
use crate::net::index_vec::{Idx, IndexVec};

type SmallRow<T> = SmallVec<[T; 4]>;

#[derive(Clone, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub struct Incidence<T> {
    rows: IndexVec<PlaceId, SmallRow<T>>,
    cols: usize,
}

impl<T> Incidence<T>
where
    T: Clone,
{
    pub fn new(places: usize, transitions: usize, default: T) -> Self {
        let mut rows = IndexVec::new();
        for _ in 0..places {
            rows.push(SmallRow::from_elem(default.clone(), transitions));
        }
        Self {
            rows,
            cols: transitions,
        }
    }

    pub fn from_rows(rows: IndexVec<PlaceId, SmallRow<T>>) -> Self {
        let cols = rows.iter().map(|row| row.len()).next().unwrap_or_default();
        debug_assert!(rows.iter().all(|row| row.len() == cols));
        Self { rows, cols }
    }

    pub fn push_place_with_default(&mut self, default: T) -> PlaceId {
        let mut row = SmallRow::new();
        row.resize(self.cols, default);
        self.rows.push(row)
    }

    pub fn places(&self) -> usize {
        self.rows.len()
    }

    pub fn transitions(&self) -> usize {
        self.cols
    }

    pub fn push_place(&mut self, row: SmallRow<T>) -> PlaceId {
        debug_assert!(
            row.len() == self.cols,
            "row length {} does not match incidence column count {}",
            row.len(),
            self.cols
        );
        self.rows.push(row)
    }

    pub fn push_transition_with_default(&mut self, default: T) -> TransitionId {
        let next = self.cols;
        for row in self.rows.iter_mut() {
            row.push(default.clone());
        }
        self.cols += 1;
        TransitionId::from_usize(next)
    }

    pub fn set(&mut self, place: PlaceId, transition: TransitionId, value: T) {
        self.rows[place][transition.index()] = value;
    }

    pub fn get(&self, place: PlaceId, transition: TransitionId) -> &T {
        &self.rows[place][transition.index()]
    }

    pub fn get_mut(&mut self, place: PlaceId, transition: TransitionId) -> &mut T {
        &mut self.rows[place][transition.index()]
    }

    pub fn rows(&self) -> &IndexVec<PlaceId, SmallRow<T>> {
        &self.rows
    }

    pub fn into_rows(self) -> IndexVec<PlaceId, SmallRow<T>> {
        self.rows
    }

    pub fn map<U, F>(&self, mut f: F) -> Incidence<U>
    where
        U: Clone,
        F: FnMut(&T) -> U,
    {
        let mut rows = IndexVec::new();
        for row in self.rows.iter() {
            rows.push(row.iter().map(|value| f(value)).collect::<SmallRow<_>>());
        }
        Incidence {
            rows,
            cols: self.cols,
        }
    }
}

impl<T> fmt::Debug for Incidence<T>
where
    T: fmt::Debug,
{
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("Incidence")
            .field("rows", &self.rows)
            .field("cols", &self.cols)
            .finish()
    }
}

impl Incidence<u64> {
    pub fn difference(&self, other: &Self) -> Incidence<i64> {
        assert_eq!(self.places(), other.places());
        assert_eq!(self.transitions(), other.transitions());
        let mut rows = IndexVec::new();
        for (left, right) in self.rows.iter().zip(other.rows.iter()) {
            rows.push(
                left.iter()
                    .zip(right.iter())
                    .map(|(l, r)| *l as i64 - *r as i64)
                    .collect::<SmallRow<_>>(),
            );
        }
        Incidence {
            rows,
            cols: self.cols,
        }
    }
}

impl<T> Incidence<T>
where
    T: Copy + Add<Output = T> + Sub<Output = T>,
{
    pub fn add_assign(&mut self, place: PlaceId, transition: TransitionId, delta: T)
    where
        T: Default,
    {
        let entry = self.get_mut(place, transition);
        *entry = *entry + delta;
    }

    pub fn sub_assign(&mut self, place: PlaceId, transition: TransitionId, delta: T)
    where
        T: Default,
    {
        let entry = self.get_mut(place, transition);
        *entry = *entry - delta;
    }
}

#[derive(Clone, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub struct IncidenceBool {
    rows: IndexVec<PlaceId, SmallRow<bool>>,
    cols: usize,
}

impl IncidenceBool {
    pub fn new(places: usize, transitions: usize) -> Self {
        let mut rows = IndexVec::new();
        for _ in 0..places {
            rows.push(SmallRow::from_elem(false, transitions));
        }
        Self {
            rows,
            cols: transitions,
        }
    }

    pub fn from_rows(rows: IndexVec<PlaceId, SmallRow<bool>>) -> Self {
        let cols = rows.iter().map(|row| row.len()).next().unwrap_or_default();
        debug_assert!(rows.iter().all(|row| row.len() == cols));
        Self { rows, cols }
    }

    pub fn push_place(&mut self) -> PlaceId {
        let row = SmallRow::from_elem(false, self.cols);
        self.rows.push(row)
    }

    pub fn push_transition(&mut self) -> TransitionId {
        let next = self.cols;
        for row in self.rows.iter_mut() {
            row.push(false);
        }
        self.cols += 1;
        TransitionId::from_usize(next)
    }

    pub fn get(&self, place: PlaceId, transition: TransitionId) -> bool {
        self.rows[place][transition.index()]
    }

    pub fn set(&mut self, place: PlaceId, transition: TransitionId, value: bool) {
        self.rows[place][transition.index()] = value;
    }

    pub fn rows(&self) -> &IndexVec<PlaceId, SmallRow<bool>> {
        &self.rows
    }
}

impl fmt::Debug for IncidenceBool {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("IncidenceBool")
            .field("rows", &self.rows)
            .field("cols", &self.cols)
            .finish()
    }
}
