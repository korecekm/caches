// SPDX-FileCopyrightText: 2024 2023 Martin Koreček
//
// SPDX-License-Identifier: GPL-3.0-or-later

// A transactional LRU cache that gives read transactions no way of modifying the cache's content
// (that is, even by cache hits). Write transactions store all the LRU logic in a special
// (sequential) logic struct, which only stores information about keys and not values.
// 
// Values are stored separately in a transactional hash map (we use our TrieMap implementation).
// The cache logic is separate from this map.
// 
// This makes write transaction rollbacks expensive, because such rollbacks don't only roll back
// the cached content in our transactional hash map, but also the information in the logic struct.
// 
// Once a write txn. rolls back (i.e. its handle is dropped without the txn being committed) and
// the cache is asked for another write txn, we resolve the situation by giving the new txn avery
// simple approximation of the logic struct - in fact, we just iterate through all keys in the hash
// map and insert them to a new logic struct one by one (this essentially means putting all the
// keys into the struct in random order, because the iteration order is decided by the keys'
// hashes).
// 
// An argument for why rollbacks can be expensive is that they aren't expected to be useful in the
// context of caches and should not occur (or be really rare) for most use cases.

use crate::list::{DLList, DLNode};
use crate::trie_hashmap::{TMReadTxn, TMWriteTxn, TrieMap};
use std::collections::hash_map::HashMap as StdMap;
use std::hash::Hash;
use std::mem;
use std::ptr::NonNull;
use std::sync::{Mutex, MutexGuard};

/// # LRU Transactional
/// 
/// A concurrently readable, transactional key-value cache
/// (using the LRU eviction logic).
///
/// `LRUCache` itself works only as an immutable handle. Modifications to the
/// cache need to be done via `LRUWriteTxn` (obtained with the `write` method)
/// write transactions, and are only recorded once the transactions are
/// committed (only one write transaction is allowed at a time).
///
/// `LRUReadTxn` read transactions (obtained via the `read` method ) only give
/// a snapshot to the current cached set, ie. to the values that are cached at
/// the moment of the transaction's creation and don't modify the cache in any
/// way, not even internally.
///
/// As said, write transactions need to get committed to take effect globally.
/// Their work may also be rolled back simply by having the txn handle dropped,
/// although that's discouraged, as the next write transaction's creation may
/// be expensive.
///
/// ## Example usage:
/// We will show an example usage of the write transaction:
/// ```
/// // We will simply call the global cache handle 'cache'
/// let cache = LRUCache::new(32000);
///
/// // ... let's imagine the cache is supplied with records here by another
/// // write transaction, which is now committed ...
///
/// let mut write = cache.write();
/// // a write transaction may also be created with try_write(), which returns
/// // None if another write txn is already active. write() alone waits for the
/// // active txn to finish
///
/// // a cached value was successfully retrieved
/// // unlike read transactions, write txn's get functions modify the cache
/// // internally, giving the accessed element higher priority.
/// assert!(write.get(&X).is_some());
///
/// // another value isn't recorded and we wish to submit it for caching:
/// assert!(write.get(&Y).is_none());
/// write.insert(Y, Y_value);
///
/// write.commit();
/// // now, the modifications will be visible for new transaction handles
/// ```
pub struct LRUTransactional<K: Clone + Eq + Hash, V: Clone> {
    capacity: usize,
    map: TrieMap<K, V>,
    // The logic fields are only accessed if a write txn was successfully
    // acquired for the map
    logic_valid: Mutex<bool>,
    logic: Mutex<LRULogic<K>>,
}

pub struct LRUReadTxn<K: Clone + Eq + Hash, V: Clone> {
    map: TMReadTxn<K, V>,
}

pub struct LRUWriteTxn<'a, K: Clone + Eq + Hash, V: Clone> {
    // The only reason the map is in an Option is so that it can be later taken
    // for commit. It will stay Some(txn) for the whole time though.
    map: Option<TMWriteTxn<'a, K, V>>,
    logic_valid: MutexGuard<'a, bool>,
    logic: MutexGuard<'a, LRULogic<K>>,
}

struct LRULogic<K: Clone + Eq + Hash> {
    capacity: usize,
    map: StdMap<K, NonNull<DLNode<K>>>,
    list: DLList<K>,
}

unsafe impl<K: Clone + Eq + Hash, V: Clone> Send for LRUTransactional<K, V> {}
unsafe impl<K: Clone + Eq + Hash, V: Clone> Sync for LRUTransactional<K, V> {}

impl<K: Clone + Eq + Hash, V: Clone> LRUTransactional<K, V> {
    /// Create a new transactional LRU cache with the given capacity.
    /// 
    /// *You may want to consider, that the transactional cache may require
    /// quite a significant space overhead. As for the data structure itself,
    /// that only adds an amount of pointers linear to the number of records,
    /// but remember that all the read transactions make the values cached at
    /// the time of the txn's creation stay in memory, so if you plan on having
    /// many read transactions holding different versions of the cache, quite a
    /// few more values could be kept than just the given capacity,
    /// potentially.*
    pub fn new(capacity: usize) -> Self {
        Self {
            capacity,
            map: TrieMap::new(),
            logic_valid: Mutex::new(true),
            logic: Mutex::new(LRULogic::new(capacity)),
        }
    }

    /// If a write transaction rolls back, it invalidates the cache's logic
    /// data structure. After that, if another write transaction is to be
    /// acquired, we need to recover the logic structure in some way.
    fn recover_logic(&self) {
        let mut logic = LRULogic::new(self.capacity);
        // Insert the keys in the main map into the logic struct one by one
        for key in self.map.read().iter_keys() {
            logic.submit(key.clone());
        }
        *self.logic.lock().unwrap() = logic;
    }

    /// Acquire a read transaction to this cache
    pub fn read(&self) -> LRUReadTxn<K, V> {
        LRUReadTxn {
            map: self.map.read(),
        }
    }

    /// Acquire a write transaction to this cache
    pub fn write<'a>(&'a self) -> LRUWriteTxn<K, V> {
        Self::prepare_write_txn(&self, self.map.write())
    }

    /// If there's no other write transaction accessing this cache, the
    /// function returns Some(WRITE_TXN), otherwise, it returns None.
    pub fn try_write<'a>(&'a self) -> Option<LRUWriteTxn<'a, K, V>> {
        let write_attempt = self.map.try_write();
        write_attempt.map(|txn| Self::prepare_write_txn(&self, txn))
    }

    /// Once a write transaction to the (trie) map has been acquired, this
    /// function prepares the write transaction for our cache.
    fn prepare_write_txn<'a>(&'a self, map_write: TMWriteTxn<'a, K, V>) -> LRUWriteTxn<'a, K, V> {
        let mut logic_valid_guard = self.logic_valid.lock().unwrap();
        if !*logic_valid_guard {
            // A previous write transaction was rolled back, invalidating the
            // logic structure.
            self.recover_logic();
        }
        *logic_valid_guard = false;
        LRUWriteTxn {
            map: Some(map_write),
            logic_valid: logic_valid_guard,
            logic: self.logic.lock().unwrap(),
        }
    }
}

impl<K: Clone + Eq + Hash, V: Clone> LRUReadTxn<K, V> {
    /// Attempt to retrieve a value reference for given key among cached data
    /// by the time this read transaction was generated.
    /// Note that this doesn't change the inner structure of the cache, ie. in
    /// case of a cache hit, the hit won't be registered. You might want to
    /// record hit keys and access them once you have a write transaction, so
    /// that the keys don't get evicted too soon.
    pub fn get(&self, key: &K) -> Option<&V> {
        self.map.search(key)
    }
}

impl<K: Clone + Eq + Hash, V: Clone> LRUWriteTxn<'_, K, V> {
    /// Commit the transaction. This consumes the struct.
    pub fn commit(mut self) {
        *self.logic_valid = true;
        // A problem may occur if this thread crashes before being able to
        // commit the map itself properly. Such accident will corrupt the
        // structure's state permanently, making write transactions impossilbe
        // to generate, but (besides that basically being what we would expect
        // should happen) the cache remains valid for reading from as is.
        mem::take(&mut self.map).unwrap().commit();
    }

    /// Attempt to retrieve a value reference for given key among currently
    /// cached data.
    pub fn get(&mut self, key: &K) -> Option<&V> {
        let value = self.map.as_ref().unwrap().search(key);
        if value.is_some() {
            (*self.logic).hit(key);
        }
        value
    }

    /// Submit this key-value pair for caching.
    /// Only call this if the record isn't already present in the cache.
    pub fn insert(&mut self, key: K, value: V) {
        // The logic DS may indicate that we need to evict a value
        if let Some(remove_key) = (*self.logic).submit(key.clone()) {
            self.map.as_mut().unwrap().remove(&remove_key);
        }
        self.map.as_mut().unwrap().update(key, value);
    }

    /// This function enables modifications to the present values.
    /// Only call this if the record *is* already present in the cache.
    pub fn reinsert(&mut self, key: K, value: V) {
        (*self.logic).hit(&key);
        self.map.as_mut().unwrap().update(key, value);
    }
}

impl<K: Clone + Eq + Hash> LRULogic<K> {
    /// Initiate an empty LRU logic data structure
    fn new(capacity: usize) -> Self {
        Self {
            capacity,
            map: StdMap::with_capacity(capacity),
            list: DLList::new(),
        }
    }

    /// Submit a *new* (the key really must not yet be present) key for
    /// caching. If a value for another key needs to be removed (the cache is
    /// full), the key is returned.
    fn submit(&mut self, key: K) -> Option<K> {
        // If we need to evict a key, we store it to a variable to return later
        let evict_key = if self.list.size == self.capacity {
            if let Some(k) = self.list.pop_back() {
                self.map.remove(&k);
                Some(k)
            } else {
                panic!("Unreachable");
            }
        } else {
            None
        };
        // Create a node for the new key
        let mut node = NonNull::new(Box::into_raw(Box::new(DLNode::new(key.clone())))).unwrap();
        // First, insert the pointer to the node into our hash map
        self.map.insert(key, node);
        // Finally, insert the node to the list's front
        self.list
            .insert_head(unsafe { node.as_mut() as *mut DLNode<_> });
        self.list.size += 1;

        evict_key
    }

    /// Update LRU state on a record's reaccess
    fn hit(&mut self, key: &K) {
        if let Some(node) = self.map.get_mut(key) {
            unsafe {
                // Move the key's node to the list's front
                node.as_mut().move_to_front(&mut self.list);
            }
        } else {
            // Key was hit in the value map, but not the one in Logic
            panic!("Unreachable.");
        }
    }
}

#[cfg(test)]
mod test {
    use super::LRUTransactional;
    use rand::{thread_rng, Rng};
    use std::mem;

    #[test]
    fn simple() {
        // Checks the cache semantics with a basic example use case
        let lru = LRUTransactional::new(3);
        // We perform several insertions and reaccessing, then we check logic
        // is in the state we expect
        let mut lru_write = lru.write();
        assert_eq!(lru_write.get(&1), None);
        assert_eq!(lru.read().get(&1), None);
        lru_write.insert(1, 'A');
        lru_write.insert(2, 'B');
        assert_eq!(lru_write.get(&2), Some(&'B'));
        assert_eq!(lru_write.get(&2), Some(&'B'));
        assert_eq!(lru_write.get(&1), Some(&'A'));
        lru_write.commit();

        lru_write = lru.write();
        assert_eq!(lru_write.get(&3), None);
        lru_write.insert(3, 'C');
        assert_eq!(lru_write.get(&4), None);
        lru_write.insert(4, 'D');
        lru_write.commit();

        lru_write = lru.write();
        assert_eq!(lru_write.get(&2), None);
        // See if the list in the `logic` structure looks as we expect
        let produced_list = &mut (*lru_write.logic).list;
        assert_eq!(produced_list.size, 3);
        for i in [1, 3, 4].iter() {
            assert_eq!(produced_list.pop_back(), Some(*i));
        }
    }

    #[test]
    #[allow(unused_assignments)]
    fn roolback() {
        // This test attempts to check if rollbacks work correctly, via simple
        // example usage.
        let lru = LRUTransactional::new(3);

        // First, insert three values in a valid way:
        let mut lru_write = Some(lru.write());
        for i in 0..3 {
            lru_write.as_mut().unwrap().insert(i, i);
        }
        mem::take(&mut lru_write).unwrap().commit();

        // Insert another three in a write txn that gets rolled back:
        lru_write = Some(lru.write());
        for i in 0..3 {
            lru_write.as_mut().unwrap().insert(3 + i, 3 + i);
        }
        lru_write = None; // rollback

        // Checks the cache is in the state we expect
        rollback_check(&lru, 3, 0);
        for i in 0..3 {
            let mut write = lru.write();
            write.insert(6 + i, 6 + i);
            write.commit();
            rollback_check(&lru, 2 - i, 1 + i);
        }
    }

    /// Checks for the right amount of values in the [0, 2] and [6, 8] ranges
    /// being currently recorded.
    fn rollback_check(lru: &LRUTransactional<usize, usize>, first: usize, last: usize) {
        // we need this not to modify the persisting cache structure
        // (so we use a read txn)
        let read = lru.read();
        let mut count = 0;
        for i in 0..3 {
            if read.get(&i).is_some() {
                count += 1;
            }
        }
        assert_eq!(count, first);

        for i in 0..3 {
            assert_eq!(read.get(&(3 + i)), None);
        }

        count = 0;
        for i in 0..3 {
            if read.get(&(6 + i)).is_some() {
                count += 1;
            }
        }
        assert_eq!(count, last);
    }

    #[test]
    fn smoke_test() {
        // Without checking the cache semantics, this only makes sure the cache
        // always returns the correct number of elements.
        let mut rng = thread_rng();
        let cache = LRUTransactional::new(25);
        let mut write = cache.write();
        // First, fill the cache
        for i in 0..25 {
            write.insert(i, i);
        }
        write.commit();

        for iter in 0..3000 {
            // Check that the current read transaction can read 25 elements
            let mut count = 0;
            let read = cache.read();
            for k in 0..200 {
                let record = read.get(&k);
                if let Some(val) = record {
                    assert_eq!(val, &k);
                    count += 1;
                }
            }
            assert_eq!(count, 25);

            // Now modify the cache with a write txn
            let mut write = cache.write();
            let key = rng.gen_range(0, 200);
            let record = write.get(&key);
            if record.is_none() {
                write.insert(key, key);
            }

            // Check that the write txn can access all its 25 element
            count = 0;
            for k in 0..200 {
                let record = write.get(&k);
                if let Some(val) = record {
                    assert_eq!(val, &k);
                    count += 1;
                }
            }
            assert_eq!(count, 25);

            // Commit the modifications for the next iteration.
            // Every 300th iteration gets rolled back to also test logic
            // recovery.
            if iter % 300 != 0 {
                write.commit();
            }
        }
    }
}
