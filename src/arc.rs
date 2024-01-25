// SPDX-FileCopyrightText: 2024 2023 Martin Koreček
//
// SPDX-License-Identifier: GPL-3.0-or-later

// An implementation of the ARC cache replacement policy based on
// Megiddo, Modha: ARC: A Self-Tuning, Low Overhead Replacement Cache
// (https://www.usenix.org/conference/fast-03/arc-self-tuning-low-overhead-replacement-cache)
//
// Once full, this data structure actually holds twice as many elements as its' given capacity, but
// only `capacity` of them also hold a value for the key (inside a Box). The other half of elements
// are just ghost records to keep records of what keys we have seen "recently".
//
// All elements are divided into two (imaginary) linked lists, L1 and L2. L1 is a list for
// "recently" seen, but just once, L2 holds records which we have seen at lest twice "recently"
// (since the time when they were last uncached). In reality, these imaginary lists are further
// split into T1, B1 and T2, B2 (T as Top, B as Bottom). All four lists only really hold keys, but
// the DS only holds (boxed) values for the records of keys inside T1 and T2. All records are held
// inside `map`, a hash map of `Record`s, you may notice that T1 and T2 Records also have an
// asociated boxed value.
//
// Both (each) L1 and L2 have a capacity of the one given to the whole data structure, while we (as
// a way to think of it) always try to keep the number of records inside T1 as `p`, which is a
// parameter inside our cache which adaptively changes based on current access patterns (it gets
// increased on accesses to B1 and decreased on accesses to B2).
// 
// As with any cache data structure, we also keep a hash map (called `map`) that stores pointers to
// the list's nodes for the records' keys, to implement operations in a convenient and
// constant-time way.

use crate::list::{DLList, DLNode};
use std::cmp::{max, min};
use std::collections::HashMap;
use std::hash::Hash;
use std::ptr::NonNull;

// This is what is stored in the `map`, each type of record holds a pointer to
// its node in one of the queues. Only records in the 'resident' parts of the
// cache (T1 and T2) also hold boxed values.
enum Record<K, V> {
    T1(NonNull<DLNode<K>>, Box<V>),
    B1(NonNull<DLNode<K>>),
    T2(NonNull<DLNode<K>>, Box<V>),
    B2(NonNull<DLNode<K>>),
}

/// # ARC Cache
/// A cache data structure using the ARC eviction logic. It serves as a
/// key-value storage for a limited amount of records.
/// 
/// We create an ARCache struct by providing the `new` function with a capacity
/// ```
/// let mut cache = ARCache::new(10);
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
/// ARC logic.
pub struct ARCache<K: Clone + Eq + Hash, V> {
    // The total cache capacity
    capacity: usize,
    // `map` for convenient accesses to nodes
    map: HashMap<K, Record<K, V>>,
    // The four queues of the structure.
    t1: DLList<K>,
    b1: DLList<K>,
    t2: DLList<K>,
    b2: DLList<K>,
    // The "p" parameter from the original paper. divides the total capacity
    // between T1 and T2.
    p: usize,
}

impl<K: Clone + Eq + Hash, V> ARCache<K, V> {
    /// Create a new cache of given capacity, with the ARC replacement policy.
    ///
    /// Note that when full, this data structure keeps, besides the `capacity`
    /// of key-value records also another `capacity` of records with just the
    /// key. You might want to consider this in case your stored values have
    /// a similar size to the size of keys.
    pub fn new(capacity: usize) -> Self {
        Self {
            capacity,
            map: HashMap::with_capacity(2 * capacity),
            t1: DLList::new(),
            b1: DLList::new(),
            t2: DLList::new(),
            b2: DLList::new(),
            p: 0,
        }
    }

    /// Submit this key-value pair for caching.
    /// The given `key` must not be present in the cache yet.
    pub fn insert(&mut self, key: K, value: V) {
        match self.map.remove(&key) {
            Some(Record::B1(node_ptr)) => {
                // Remove the record from the B1 ghost list
                unsafe {
                    (*node_ptr.as_ptr()).remove(&mut self.b1);
                }
                // Take care of the rest
                self.insert_from_b1(key, value, node_ptr);
            }
            Some(Record::B2(node_ptr)) => {
                // Remove the record from the B2 ghost list
                unsafe {
                    (*node_ptr.as_ptr()).remove(&mut self.b2);
                }
                // Take care of the rest
                self.insert_from_b2(key, value, node_ptr);
            }
            Some(_) => panic!("Unreachable"),
            None => self.insert_on_miss(key, value),
        }
    }

    /// Insert a key-value pair, where the key was already stored in B1 (and is
    /// now removed from there).
    ///
    /// `node_ptr` is a NonNull pointer to a node with given key, with no neighbours
    fn insert_from_b1(&mut self, key: K, value: V, node_ptr: NonNull<DLNode<K>>) {
        self.increase_p();
        self.remove_in_cached(self.p + 1);
        self.t2.insert_head(node_ptr.as_ptr());
        self.t2.size += 1;
        self.map.insert(key, Record::T2(node_ptr, Box::new(value)));
    }

    /// Insert a key-value pair, where the key was already stored in B2 (and is
    /// now removed from there).
    ///
    /// `node_ptr` is a NonNull pointer to a node with given key, with no neighbours
    fn insert_from_b2(&mut self, key: K, value: V, node_ptr: NonNull<DLNode<K>>) {
        self.decrease_p();
        self.remove_in_cached(max(1, self.p));
        self.t2.insert_head(node_ptr.as_ptr());
        self.t2.size += 1;
        self.map.insert(key, Record::T2(node_ptr, Box::new(value)));
    }

    /// Inserts given key-value pair into our DS, in the case where no record
    /// for given key exists yet (ie. not even as a ghost in B1 or B2).
    fn insert_on_miss(&mut self, key: K, value: V) {
        if self.t1.size + self.b1.size == self.capacity {
            // L1 is full, evict one of its elements:
            if self.t1.size < self.capacity {
                // First, we evict the LRU of B1.
                if let Some(k) = self.b1.pop_back() {
                    self.map.remove(&k);
                }
                // Now we also remove an element that keeps a cached value
                self.remove_in_cached(self.p + 1);
            } else {
                // B1 is empty, remove LRU of T1:
                if let Some(k) = self.t1.pop_back() {
                    self.map.remove(&k);
                }
            }
        } else {
            // L1 has less than `capacity` elements
            if (self.t1.size + self.b1.size + self.t2.size + self.b2.size) == (2 * self.capacity) {
                // full capacity reached, remove b2's LRU
                if let Some(k) = self.b2.pop_back() {
                    self.map.remove(&k);
                }
            }
            self.remove_in_cached(self.p + 1);
        }

        // Now insert the new record as T1's MRU:
        let node = NonNull::new(Box::into_raw(Box::new(DLNode::new(key.clone())))).unwrap();
        let boxed_val = Box::new(value);
        self.map.insert(key, Record::T1(node, boxed_val));
        self.t1.insert_head(node.as_ptr());
        self.t1.size += 1;
    }

    /// Returns a reference to the value for the given key, if it is cached.
    pub fn get<'a>(&'a mut self, key: &K) -> Option<&'a V> {
        if let Some(record) = self.map.get(key) {
            // `get` is only relevant if the record is inside T1 or T2 (the ).
            // B1/B2 reaccesses are processed only on `insert`
            match record {
                Record::T1(_, _) => Some(self.get_in_t1(key)),
                Record::T2(_, _) => {
                    // Move the record to the MRU position:
                    // (workaround to be able to borrow self as mut in the other case branch)
                    if let Some(Record::T2(node, boxed_val)) = self.map.get_mut(key) {
                        unsafe {
                            node.as_mut().move_to_front(&mut self.t2);
                        }
                        Some(&*boxed_val)
                    } else {
                        panic!("Unreachable.");
                    }
                }
                _ => None,
            }
        } else {
            None
        }
    }

    /// Takes care of an access to T1 and returns the value's reference.
    fn get_in_t1<'a>(&'a mut self, key: &K) -> &'a V {
        if let Some(Record::T1(node_ptr, boxed_val)) = self.map.remove(key) {
            let node = unsafe { &mut (*node_ptr.as_ptr()) };
            // Move the record from T1 to T2
            node.remove(&mut self.t1);
            self.t2.insert_head(node as *mut DLNode<_>);
            self.t2.size += 1;
            self.map
                .insert(key.clone(), Record::T2(node_ptr, boxed_val));
        } else {
            panic!("Unreachable.");
        }
        // Workaround to be able to change record type to T2 and
        // return the value reference:
        if let Some(Record::T2(_, boxed_val)) = self.map.get(key) {
            &*boxed_val
        } else {
            panic!("Unreachable.");
        }
    }

    /// Removes one record from T1 or T2, ie. a record that also holds a boxed
    /// value.
    /// `t1_limit` says, what minimum size of the T1 triggers an eviction from
    /// it.
    fn remove_in_cached(&mut self, t1_limit: usize) {
        if self.t1.size + self.t2.size < self.capacity {
            // We only remove the element if the capacity is reached
            return;
        }
        if self.t1.size >= t1_limit {
            // Turn T1's LRU into B1's MRU
            if let Some(t1_lru_key) = self.t1.pop_back() {
                // Create a new node to insert into B1:
                let node_ptr =
                    NonNull::new(Box::into_raw(Box::new(DLNode::new(t1_lru_key.clone())))).unwrap();
                self.b1.insert_head(node_ptr.as_ptr());
                self.b1.size += 1;
                // This changes the record type inside our map and also frees
                // the space taken up by the value
                self.map.insert(t1_lru_key, Record::B1(node_ptr));
            }
        } else {
            // Turn T2's LRU into B2's MRU
            if let Some(t2_lru_key) = self.t2.pop_back() {
                // Create a new node to insert into B2:
                let node_ptr =
                    NonNull::new(Box::into_raw(Box::new(DLNode::new(t2_lru_key.clone())))).unwrap();
                self.b2.insert_head(node_ptr.as_ptr());
                self.b2.size += 1;
                // This changes the record type inside our map and also frees
                // the space taken up by the value
                self.map.insert(t2_lru_key, Record::B2(node_ptr));
            }
        }
    }

    /// Increases the p parameter accordingly to the ARC logic
    /// (used when a B1 record is accessed (via insert), the b1 record is
    /// already removed, and so we need to increment to b1.size)
    fn increase_p(&mut self) {
        let b1_size = self.b1.size + 1;
        let b2_size = self.b2.size;
        let delta = if b1_size >= b2_size {
            1
        } else {
            b2_size / b1_size
        };
        self.p = min(self.p + delta, self.capacity);
    }

    /// Decreases the p parameter accordingly to the ARC logic
    /// (used when a B2 record is accessed (via insert), the b2 record is
    /// already removed, and so we need to increment to b2.size)
    fn decrease_p(&mut self) {
        let b1_size = self.b1.size;
        let b2_size = self.b2.size + 1;
        let delta = if b2_size >= b1_size {
            1
        } else {
            b1_size / b2_size
        };
        self.p -= min(self.p, delta);
    }
}

#[cfg(test)]
mod test {
    use super::ARCache;
    use crate::list::DLList;
    use rand::{thread_rng, Rng};
    use std::fmt::Debug;
    use std::hash::Hash;

    #[test]
    fn simple() {
        // A simple test of the cache semantics
        let mut arc = ARCache::new(3);
        for i in 0..3 {
            arc.insert(i, 2 * i);
        }
        // key 1 gets moved into T2
        assert_eq!(arc.get(&1), Some(&2));
        arc.insert(3, 6);
        check_queue_elements(&arc, vec![3, 2], vec![0], vec![1], vec![]);

        // B1 element 0 goes to T2
        assert_eq!(arc.get(&0), None);
        arc.insert(0, 0);
        assert_eq!(arc.p, 1);
        check_queue_elements(&arc, vec![3], vec![2], vec![0, 1], vec![]);

        // 1 moves to the LRU position inside T2
        assert_eq!(arc.get(&1), Some(&2));
        // Insert another new value and force a T2 element to move to B2
        arc.insert(4, 8);
        check_queue_elements(&arc, vec![4, 3], vec![2], vec![1], vec![0]);

        // Access the only B2 element (moving it back into T2)
        assert_eq!(arc.get(&0), None);
        arc.insert(0, 0);
        assert_eq!(arc.p, 0);
        check_queue_elements(&arc, vec![4], vec![3, 2], vec![0, 1], vec![]);

        // We have tried all types of accesses.
        // Now we just add a few more records to check evictions from B1 and B2:

        // 3 moves from B1 to T2
        arc.insert(3, 6);
        // new value, 5 and 6
        arc.insert(5, 10);
        arc.insert(6, 12);
        check_queue_elements(&arc, vec![6, 5], vec![4], vec![3], vec![0, 1]);
    }

    /// Checks that the records in the given ARCache are stored in the queues
    /// ordered exactly as we expect.
    fn check_queue_elements<K>(
        cache: &ARCache<K, K>,
        expect_t1: Vec<K>,
        expect_b1: Vec<K>,
        expect_t2: Vec<K>,
        expect_b2: Vec<K>,
    ) where
        K: Eq + Clone + Hash + Debug,
    {
        check_list_content(&cache.t1, &expect_t1);
        check_list_content(&cache.b1, &expect_b1);
        check_list_content(&cache.t2, &expect_t2);
        check_list_content(&cache.b2, &expect_b2);
    }

    /// Given a DLList and a Vec, this checks that both contain exactly the
    /// same records, in the same order.
    fn check_list_content<K>(list: &DLList<K>, expect: &Vec<K>)
    where
        K: Eq + Clone + Hash + Debug,
    {
        let mut list_iter = list.iter();
        for key in expect.iter() {
            assert_eq!(list_iter.next(), Some(key));
        }
        assert_eq!(list_iter.next(), None);
    }

    #[test]
    fn smoke_test() {
        // Doesn't test the cache semantics, only makes sure the cache always
        // returns the correct number of elements.
        let mut rng = thread_rng();
        let mut arc = ARCache::new(25);
        // First, just insert 25 distinct elements
        for i in 0..25 {
            arc.insert(i, i);
        }

        for _ in 0..1000 {
            let key = rng.gen_range(0, 200);
            let record = arc.get(&key);
            if record.is_none() {
                arc.insert(key, key);
            }

            // Check that there are exactly 25 cached records
            let mut count = 0;
            for k in 0..200 {
                let record = arc.get(&k);
                if let Some(val) = record {
                    assert_eq!(val, &k);
                    count += 1;
                }
            }
            assert_eq!(count, 25);
        }
    }
}
