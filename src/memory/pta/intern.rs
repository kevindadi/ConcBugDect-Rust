use rustc_data_structures::fx::FxHashMap;
use std::hash::Hash;

/// Generic value interner: maps `T` to a dense `u32` id and back.
pub struct Interner<T: Clone + Eq + Hash> {
    map: FxHashMap<T, u32>,
    items: Vec<T>,
}

impl<T: Clone + Eq + Hash> Default for Interner<T> {
    fn default() -> Self {
        Self {
            map: FxHashMap::default(),
            items: Vec::new(),
        }
    }
}

impl<T: Clone + Eq + Hash> Interner<T> {
    pub fn intern(&mut self, value: T) -> u32 {
        if let Some(&id) = self.map.get(&value) {
            return id;
        }
        let id = self.items.len() as u32;
        self.items.push(value.clone());
        self.map.insert(value, id);
        id
    }

    pub fn get(&self, id: u32) -> &T {
        &self.items[id as usize]
    }

    /// Look up an existing id without interning a new value.
    pub fn get_id(&self, value: &T) -> Option<u32> {
        self.map.get(value).copied()
    }

    pub fn len(&self) -> usize {
        self.items.len()
    }

    pub fn is_empty(&self) -> bool {
        self.items.is_empty()
    }

    /// Iterate `(id, &value)` for every interned item in id order.
    pub fn iter(&self) -> impl Iterator<Item = (u32, &T)> {
        self.items.iter().enumerate().map(|(i, v)| (i as u32, v))
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn interns_dedup_and_roundtrip() {
        let mut i: Interner<String> = Interner::default();
        let a = i.intern("x".to_string());
        let b = i.intern("x".to_string());
        let c = i.intern("y".to_string());
        assert_eq!(a, b);
        assert_ne!(a, c);
        assert_eq!(i.get(a), "x");
        assert_eq!(i.get(c), "y");
        assert_eq!(i.len(), 2);
    }
}
