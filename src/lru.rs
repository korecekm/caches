// This is an implementation of a cache data structure using the Least Recently Used (LRU)
// replacement policy. As the name suggests, when the cache is full and a new record is being
// inserted into it, the strategy evicts the record that has been accessed the least recently.
//
// We implement this with a queue - a doubly linked list. New records are pushed to the list's
// front, on reaccess, an element moves back to the front. Records are evicted from the back.
//
// As with any cache data structure, we also keep a hash map (called `map`) that stores pointers to
// the list's nodes for the records' keys, to implement operations in a convenient and
// constant-time way

use crate::list::{DLList, DLNode};
use std::collections::HashMap;
use std::hash::Hash;
use std::ptr::NonNull;

pub struct LRUCache<K: Clone + Eq + Hash, V> {
    capacity: usize,
    map: HashMap<K, NonNull<DLNode<(K, V)>>>,
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
        lru.insert(3, 'C');
        assert_eq!(lru.get(&4), None);
        lru.insert(4, 'D');

        assert_eq!(lru.get(&2), None);
        assert_eq!(lru.list.size, 3);
        for i in [(1, 'A'), (3, 'C'), (4, 'D')].iter() {
            assert_eq!(lru.list.pop_back(), Some(*i));
        }
        assert_eq!(lru.list.size, 0);
        assert_eq!(lru.list.pop_back(), None);
    }

    #[test]
    fn extract_simple() {
        // Basic test that checks the behavior of the `extract` function (and
        // transitively `evict` too)
        let mut lru = LRUCache::new(5);
        assert_eq!(lru.extract(&7), None);
        for i in 1..11 {
            lru.insert(i, 2 * i);
        }
        assert_eq!(lru.extract(&5), None);

        assert_eq!(lru.list.size, 5);
        assert_eq!(lru.extract(&7), Some(14));
        assert_eq!(lru.list.size, 4);
        assert_eq!(lru.extract(&9), Some(18));
        assert_eq!(lru.list.size, 3);

        for elem in [(6, 12), (8, 16), (10, 20)].iter() {
            assert_eq!(lru.list.pop_back(), Some(*elem));
        }
        assert_eq!(lru.list.size, 0);
        assert_eq!(lru.list.pop_back(), None);
    }

    #[test]
    fn smoke_test() {
        // Doesn't test the cache semantics, only makes sure the cache always
        // stays at the limit number of elements
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
