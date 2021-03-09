use rand::rngs::ThreadRng;
use rand::{thread_rng, Rng};
use std::collections::HashMap;
use std::hash::Hash;

// random replacement cache
struct RRCache<K: Clone + Eq + Hash, V> {
    capacity: usize,
    map: HashMap<K, V>,
    vec: Vec<K>,
    rng: ThreadRng,
}

impl<K: Clone + Eq + Hash, V> RRCache<K, V> {
    fn new(capacity: usize) -> Self {
        Self {
            capacity,
            map: HashMap::with_capacity(capacity),
            vec: Vec::with_capacity(capacity),
            rng: thread_rng(),
        }
    }

    fn try_get<'a>(&'a mut self, key: &K) -> Option<&'a V> {
        self.map.get(key).map(|value| value)
    }

    /// Expects that key isn't already present!
    fn insert(&mut self, key: K, value: V) {
        if self.vec.len() < self.capacity {
            self.vec.push(key.clone());
        } else {
            let rm = self.rng.gen_range(0, self.capacity);
            self.map.remove(&self.vec[rm]);
            self.vec[rm] = key.clone();
        }
        self.map.insert(key, value);
    }
}

// Test:

#[cfg(test)]
mod test {
    use super::RRCache;
    use crate::cache::Cache;

    #[test]
    fn simple() {
        let mut rr = RRCache::new(3);
        for i in 0..10 {
            assert_eq!(rr.try_get(&i), None);
            rr.insert(i, ('A' as u8 + i) as char);
            assert_eq!(rr.try_get(&i), Some(&(('A' as u8 + i) as char)));
        }
        assert_eq!(rr.map.len(), 3);
        assert_eq!(rr.vec.len(), 3);
        let mut count = 0;
        let mut present = [false; 10];
        for i in 0..10 {
            if rr.try_get(&i).is_some() {
                count += 1;
                present[i as usize] = true;
            }
        }
        assert_eq!(count, 3);
        for i in 0..10 as u8 {
            let c = ('A' as u8 + i) as char;
            let expect = match present[i as usize] {
                false => None,
                true => Some(&c),
            };
            assert_eq!(rr.try_get(&i), expect);
        }
    }
}
