use crate::list::{DLList, DLNode};
use crate::trie_hashmap::{TMReadTxn, TMWriteTxn, TrieMap};
use std::cell::Cell;
use std::collections::hash_map::HashMap as StdMap;
use std::hash::Hash;
use std::mem;
use std::ptr::NonNull;

// A transactional LRU that gives read transactions no way to modify the cache's
// content. Write transactions store all LRU logic in a special sequential
// LRULogic struct.
// This makes rollbacks expensive, since then the current cached set might have
// little to do with what's recorded in Logic (this is resolved by iterating
// through all cached keys and putting them into the LRULogic one by one (this
// essentially means putting all the keys in the logic in random order, since
// the iteration order is decided by the keys' hashes)).
// An argument to why rollbacks may be expensive is that they aren't expected
// to be useful in the context of caches.

/// A concurrently readable, transactional key-value cache.
///
/// `LRUCache` itself works only as an immutable handle. Modifications to the
/// cache need to be done via `LRUWriteTxn` write transactions and are only
/// recorded once the transactions are committed (only one write transaction is
/// allowed at a time).
///
/// `LRUReadTxn` read transactions only give a snapshot to the current cached
/// set, ie. to the values that are cached at the moment of the transaction's
/// creation and don't modify the cache in any way, not even internally.
///
/// As said, write transactions need to get committed to take effect globally.
/// Their work may also be rolled back simply by having the txn handle dropped,
/// although that's discouraged, as the next write transaction's creation may
/// be expensive.
///
/// ## Example:
/// We will present, how a write transaction may function:
/// ```
/// // assume this name for the globally (potentially by several threads) used
/// // cache
/// let cache = LRUCache::new(32000);
///
/// // ... arbitrary operation ...
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
///
/// Since read transactions aren't enabeld to affect the global cache, their
/// threads may either count on some lookups being more expensive, or hold
/// their own, smaller thread-local sequential caches, potentially committing
/// the locally cached items once they succeed at claiming a write transaction
/// handle.
pub struct LRUCache<K: Clone + Eq + Hash, V: Clone> {
    capacity: usize,
    map: TrieMap<K, V>,
    // the other fields are only accessed if a write txn for the map was
    // successfully received, ie. the map itself protects the struct against
    // concurrent rewrites
    logic_valid: Cell<bool>,
    logic: Cell<*mut LRULogic<K>>,
}

struct LRULogic<K: Clone + Eq + Hash> {
    capacity: usize,
    map: StdMap<K, NonNull<DLNode<K>>>,
    list: DLList<K>,
}

pub struct LRUReadTxn<K: Clone + Eq + Hash, V: Clone> {
    map: TMReadTxn<K, V>,
}

pub struct LRUWriteTxn<'a, K: Clone + Eq + Hash, V: Clone> {
    // The only reason the map is in an Option is so that it can be later taken
    // for commit. It will stay Some(txn) for the whole time though.
    map: Option<TMWriteTxn<'a, K, V>>,
    logic_valid: &'a Cell<bool>,
    logic: *mut LRULogic<K>,
}

unsafe impl<K: Clone + Eq + Hash, V: Clone> Send for LRUCache<K, V> {}
unsafe impl<K: Clone + Eq + Hash, V: Clone> Sync for LRUCache<K, V> {}

impl<K: Clone + Eq + Hash, V: Clone> LRUCache<K, V> {
    pub fn new(capacity: usize) -> Self {
        Self {
            capacity,
            map: TrieMap::new(),
            logic_valid: Cell::new(true),
            logic: Cell::new(Box::into_raw(Box::new(LRULogic {
                capacity,
                map: StdMap::with_capacity(capacity),
                list: DLList::new(),
            }))),
        }
    }

    fn recover_logic(&self) {
        let mut logic = LRULogic {
            capacity: self.capacity,
            map: StdMap::with_capacity(self.capacity),
            list: DLList::new(),
        };
        for key in self.map.read().iter_keys() {
            // We are counting on the map not having over $capacity number of
            // elements and removes therefore not being necessary.
            logic.submit(key.clone());
        }
        self.logic.set(Box::into_raw(Box::new(logic)));
    }

    pub fn read(&self) -> LRUReadTxn<K, V> {
        LRUReadTxn {
            map: self.map.read(),
        }
    }

    pub fn write<'a>(&'a self) -> LRUWriteTxn<K, V> {
        Self::prepare_write_txn(&self, self.map.write())
    }

    pub fn try_write<'a>(&'a self) -> Option<LRUWriteTxn<'a, K, V>> {
        let write_attempt = self.map.try_write();
        write_attempt.map(|txn| Self::prepare_write_txn(&self, txn))
    }

    fn prepare_write_txn<'a>(&'a self, map_write: TMWriteTxn<'a, K, V>) -> LRUWriteTxn<'a, K, V> {
        if !self.logic_valid.get() {
            self.recover_logic();
        }
        self.logic_valid.set(false);
        LRUWriteTxn {
            map: Some(map_write),
            logic_valid: &self.logic_valid,
            logic: self.logic.get(),
        }
    }
}

impl<K: Clone + Eq + Hash, V: Clone> Drop for LRUCache<K, V> {
    fn drop(&mut self) {
        if self.logic_valid.get() {
            unsafe {
                Box::from_raw(self.logic.get());
            }
        }
    }
}

impl<K: Clone + Eq + Hash, V: Clone> LRUReadTxn<K, V> {
    /// Attempt to retrieve a value reference for given key among data cached
    /// by the time this read transaction was generated.
    pub fn get(&self, key: &K) -> Option<&V> {
        self.map.search(key)
    }
}

impl<K: Clone + Eq + Hash, V: Clone> LRUWriteTxn<'_, K, V> {
    pub fn commit(mut self) {
        self.logic_valid.set(true);
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
        let record = self.map.as_ref().unwrap().search(key);
        if record.is_some() {
            unsafe {
                (*self.logic).hit(key);
            }
        }

        record
    }

    /// Submit this key-value pair for caching.
    /// Only call this if the record isn't already present in the cache.
    pub fn insert(&mut self, key: K, value: V) {
        self.map.as_mut().unwrap().update(key.clone(), value);
        if let Some(remove_key) = unsafe { (*self.logic).submit(key) } {
            self.map.as_mut().unwrap().remove(&remove_key);
        }
    }
}

impl<K: Clone + Eq + Hash, V: Clone> Drop for LRUWriteTxn<'_, K, V> {
    fn drop(&mut self) {
        // drop the whole queue and helper map
        // (which now likely hold data irrelevant to the cached keys that are
        // actually cached in the map)
        if !self.logic_valid.get() {
            unsafe {
                Box::from_raw(self.logic);
            }
        }
    }
}

impl<K: Clone + Eq + Hash> LRULogic<K> {
    /// Submit a *new* (not already present) key for caching.
    /// If another key needs to be removed, it is returned
    fn submit(&mut self, key: K) -> Option<K> {
        let remove_key = if self.list.size == self.capacity {
            if let Some(k) = self.list.pop_back() {
                self.map.remove(&k);
                Some(k)
            } else {
                panic!("Unreachable.")
            }
        } else {
            None
        };
        let mut node = NonNull::new(Box::into_raw(Box::new(DLNode::new(key.clone())))).unwrap();
        self.map.insert(key, node);
        self.list
            .insert_head(unsafe { node.as_mut() as *mut DLNode<_> });
        self.list.size += 1;

        remove_key
    }

    /// Update LRU state after a cache it at given key.
    fn hit(&mut self, key: &K) {
        if let Some(node) = self.map.get_mut(key) {
            unsafe {
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
    use super::LRUCache;
    use std::mem;

    #[test]
    fn simple() {
        let lru = LRUCache::new(3);
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
        let produced_list = unsafe { &mut (*lru_write.logic).list };
        assert_eq!(produced_list.size, 3);
        for i in [1, 3, 4].iter() {
            assert_eq!(produced_list.pop_back(), Some(*i));
        }
    }

    #[test]
    #[allow(unused_assignments)]
    fn roolback() {
        let lru = LRUCache::new(3);

        // first insert three values in a valid way:
        let mut lru_write = Some(lru.write());
        for i in 0..3 {
            lru_write.as_mut().unwrap().insert(i, i);
        }
        mem::take(&mut lru_write).unwrap().commit();

        // insert another three in a write txn that gets rolled back:
        lru_write = Some(lru.write());
        for i in 0..3 {
            lru_write.as_mut().unwrap().insert(3 + i, 3 + i);
        }
        lru_write = None; // rollback

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
    fn rollback_check(lru: &LRUCache<usize, usize>, first: usize, last: usize) {
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
}
