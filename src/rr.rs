// SPDX-FileCopyrightText: 2024 2023 Martin Koreček
//
// SPDX-License-Identifier: GPL-3.0-or-later

// An implementation of the random replacement cache data structure. We keep record of cached keys
// inside a vector (`vec`). This is used when we evict records (once the cache's capacity is
// reached and another record is being inserted). At that event, we generate an index in the `vec`
// uniformly at random. That key is evicted and replaced with a new one.
// 
// The records themselves are stored in the `map` hash map for constant-time retrievals.
// 
// (`get`s don't change the cache's state)

use rand::rngs::ThreadRng;
use rand::{thread_rng, Rng};
use std::collections::HashMap;
use std::hash::Hash;

/// # Random Replacement Cache
/// A cache data structure using the Random Replacement eviction logic. It
/// serves as a key-value storage for a limited amount of records.
/// 
/// We create an RRCache struct by providing the `new` function with a capacity
/// ```
/// let mut cache = RRCache::new(10);
/// ```
/// `cache` can now be used to store key-value pairs, we insert records with
/// the `insert` method:
/// ```
/// // Only keys that aren't present in the cache yet can be inserted
/// cache.insert(key1, value1);
/// cache.insert(key2, value2);
/// ```
/// The data structure never exceeds the given capacity of records, once the
/// capacity is reached and another records are being inserted, it evicts
/// records.
/// 
/// Values for keys can be retrieved with the `get` function. The returned
/// value is an `Option`, it may be `None` if the record hasn't been inserted
/// at all, or was evicted by the replacement logic
/// ```
/// assert!(cache.get(&key1), Some(&value1));
/// ```
pub struct RRCache<K: Clone + Eq + Hash, V> {
    // The set capacity of the cache.
    capacity: usize,
    // A hash map holding the actual records.
    map: HashMap<K, V>,
    // A vector of all the currently cached keys
    vec: Vec<K>,
    // (random number generator)
    rng: ThreadRng,
}

impl<K: Clone + Eq + Hash, V> RRCache<K, V> {
    /// Create a new cache of given capacity, with the Random replacement
    /// policy.
    pub fn new(capacity: usize) -> Self {
        Self {
            capacity,
            map: HashMap::with_capacity(capacity),
            vec: Vec::with_capacity(capacity),
            rng: thread_rng(),
        }
    }

    /// Returns a reference to the value cached with this key, if cached.
    pub fn get<'a>(&'a mut self, key: &K) -> Option<&'a V> {
        self.map.get(key).map(|value| value)
    }

    /// Submit this key-value pair for caching.
    /// The key must not yet be present in the cache!
    pub fn insert(&mut self, key: K, value: V) {
        if self.vec.len() < self.capacity {
            // If capacity hasn't been reached, we can just push the new key
            self.vec.push(key.clone());
        } else {
            // Eviction necessary. We generate a random index in `vec` and
            // evict the respective key.
            let rm = self.rng.gen_range(0, self.capacity);
            self.map.remove(&self.vec[rm]);
            self.vec[rm] = key.clone();
        }
        // Insert the actual key-value pair
        self.map.insert(key, value);
    }
}

// Test:

#[cfg(test)]
mod test {
    use super::RRCache;
    use rand::{thread_rng, Rng};

    #[test]
    fn smoke_test() {
        // This test uses randomized operation to make sure the cache always
        // stays at the limit number of elements.
        let mut rng = thread_rng();
        let mut cache = RRCache::new(25);
        // First, fill the cache
        for i in 0..25 {
            cache.insert(i, i);
        }

        // Now access (and insert) records at random and make sure the number
        // cached ones stays at 25
        for i in 0..10000 {
            let key = rng.gen_range(0, 200);
            let record = cache.get(&key);
            // If the record isn't yet present, insert it
            if record.is_none() {
                cache.insert(key, key);
            }

            if i % 100 == 0 {
                // Check that there are exactly 25 records
                let mut count = 0;
                for k in 0..200 {
                    let record = cache.get(&k);
                    if let Some(val) = record {
                        assert_eq!(val, &k);
                        count += 1;
                    }
                }
                assert_eq!(count, 25);
            }
        }
    }
}
