// SPDX-FileCopyrightText: 2024 2023 Martin Koreček
//
// SPDX-License-Identifier: GPL-3.0-or-later

// This is an implementation of a cache data structure using the Least Recently Used (LRU)
// replacement policy. As the name suggests, when the cache is full and a new record is being
// inserted into it, the strategy evicts the record that has been accessed the least recently.
//
// We implement this with a queue (a doubly linked list). New records are pushed to the list's
// front. On reaccess, an element moves back to the front. Records are evicted from the back.
//
// As with any cache data structure, we also keep a hash map (called `map`) that stores pointers to
// the list's nodes for the records' keys, to implement operations in a convenient and
// constant-time way.

use crate::list::{DLList, DLNode};
use std::collections::HashMap;
use std::hash::Hash;
use std::ptr::NonNull;

/// # LRU Cache
/// A cache data structure using the LRU eviction logic. It serves as a key-value storage for a limited amount of records.
/// 
/// We create an LRUCache struct by providing the `new` function with a
/// capacity.
/// ```
/// let mut cache = LRUCache::new(10);
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
/// Both `insert` and `get` update the cache's internal state according to the
/// LRU logic.
pub struct LRUCache<K: Clone + Eq + Hash, V> {
    // The set capacity of the cache
    capacity: usize,
    // Hash map storing pointers to nodes in the queue, for convenience.
    map: HashMap<K, NonNull<DLNode<(K, V)>>>,
    // The queue (doubly linked list) itself
    list: DLList<(K, V)>,
}

impl<K: Clone + Eq + Hash, V> LRUCache<K, V> {
    /// Create a new cache of given capacity, with the LRU replacement policy.
    pub fn new(capacity: usize) -> Self {
        Self {
            capacity,
            map: HashMap::with_capacity(capacity),
            list: DLList::new(),
        }
    }

    /// Returns a reference to the value cached with this key, if cached.
    pub fn get<'a>(&'a mut self, key: &K) -> Option<&'a V> {
        match self.map.get_mut(key) {
            Some(node) => unsafe {
                // Reaccessed element gets moved to the list's front
                node.as_mut().move_to_front(&mut self.list);
                Some(&node.as_ref().elem.1)
            },
            None => None,
        }
    }

    /// Submit this key-value pair for caching.
    /// The key must not yet be present in the cache!
    pub fn insert(&mut self, key: K, value: V) {
        if self.list.size == self.capacity {
            // If a record needs to be evicted, we evict the one at the list's
            // tail
            if let Some((k, _)) = self.list.pop_back() {
                self.map.remove(&k);
            }
        }
        // Create the new node for this record.
        let mut node =
            NonNull::new(Box::into_raw(Box::new(DLNode::new((key.clone(), value))))).unwrap();
        // First, insert the pointer to the node into our hash map
        self.map.insert(key, node);
        // Finally, insert the node to the list's front
        unsafe {
            self.list.insert_head(node.as_mut() as *mut DLNode<_>);
        }
        self.list.size += 1;
    }

    /// Evicts a record with given key from the cache.
    pub fn evict(&mut self, key: &K) {
        self.extract(key);
    }

    /// Like get, but removing the record from the cache.
    /// This is useful when this LRU is a thread-local cache and the thread
    /// currently has write privilege to a global transactional cache, ie if
    /// a record is present in our local cache, we can remove it from here and
    /// include it in the global cache instead.
    pub fn extract(&mut self, key: &K) -> Option<V> {
        if let Some(node) = self.map.remove(key) {
            let mut node = unsafe { *Box::from_raw(node.as_ptr()) };
            node.remove(&mut self.list);
            Some(node.elem.1)
        } else {
            None
        }
    }
}

// Test:

#[cfg(test)]
mod test {
    use super::LRUCache;
    use rand::{thread_rng, Rng};

    #[test]
    fn simple() {
        // Basic test of the semantics of the LRU cache
        let mut lru = LRUCache::new(3);
        assert_eq!(lru.get(&1), None);
        lru.insert(1, 'A');
        assert_eq!(lru.get(&2), None);
        lru.insert(2, 'B');
        assert_eq!(lru.get(&2), Some(&'B'));
        assert_eq!(lru.get(&2), Some(&'B'));
        assert_eq!(lru.get(&1), Some(&'A'));
        assert_eq!(lru.get(&3), None);
        // Capacity now gets filled
        lru.insert(3, 'C');
        assert_eq!(lru.get(&4), None);
        // First record over capacity, key 2 should get evicted.
        lru.insert(4, 'D');

        assert_eq!(lru.get(&2), None);
        assert_eq!(lru.list.size, 3);
        // Check the exact ordering in our queue
        for i in [(1, 'A'), (3, 'C'), (4, 'D')].iter() {
            assert_eq!(lru.list.pop_back(), Some(*i));
        }
        // No more elements in the queue
        assert_eq!(lru.list.size, 0);
        assert_eq!(lru.list.pop_back(), None);
    }

    #[test]
    fn extract_simple() {
        // Basic test that checks the behavior of the `extract` function (and
        // transitively `evict` too)
        let mut lru = LRUCache::new(5);
        assert_eq!(lru.extract(&7), None);
        // Insert several elements, half over capacity
        for i in 1..11 {
            lru.insert(i, 2 * i);
        }
        // Check this key was evicted by the replacement policy
        assert_eq!(lru.extract(&5), None);

        // Extract two cached elements
        assert_eq!(lru.list.size, 5);
        assert_eq!(lru.extract(&7), Some(14));
        assert_eq!(lru.list.size, 4);
        assert_eq!(lru.extract(&9), Some(18));
        assert_eq!(lru.list.size, 3);

        // Check the exact ordering in our queue
        for elem in [(6, 12), (8, 16), (10, 20)].iter() {
            assert_eq!(lru.list.pop_back(), Some(*elem));
        }
        assert_eq!(lru.list.size, 0);
        assert_eq!(lru.list.pop_back(), None);
    }

    #[test]
    fn smoke_test() {
        // Doesn't test the cache semantics. Uses randomized operation to
        // make sure the cache always stays at the limit number of elements.
        let mut rng = thread_rng();
        let mut cache = LRUCache::new(25);
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
