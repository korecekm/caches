// SPDX-FileCopyrightText: 2024 2023 Martin Koreček
//
// SPDX-License-Identifier: GPL-3.0-or-later

// An implementation of a cache data structure using the 2Q replacement policy.
// 
// The DS is implemented with 3 separate queues, Q1, Q2 and the main queue, which we call the LRU,
// as it acts just as the LRU queue.
// 
// Records are inserted into Q1, if Q1 is full, its records overflow into Q2. Records overflowing
// the Q2 are evicted. Reaccesses to records in the Q1 do nothing. Records reaccessed in the Q2
// move to the LRU queue. Reaccesses inside the LRU are just as the standard LRU queue. Records
// overflowing the LRU are evicted.
// 
// We store key-value pairs in `Record` structs that also hold information about their location, so
// that we can tell which queue they are in.
//
// As with any cache data structure, we also keep a hash map (called `map`) that stores pointers to
// the nodes of our queues for the records' keys, to implement operations in a convenient and
// constant-time way.

use crate::list::{DLList, DLNode};
use std::collections::HashMap;
use std::hash::Hash;
use std::ptr::NonNull;

/// Each record in the cache needs to hold information about its location, i.e.
/// the Q1 or Q2 queues, or the main one, which we call the LRU.
enum RecordType {
    Q1Elem,
    Q2Elem,
    LRUElem,
}

/// A record in one of our 3 queues
struct Record<K, V> {
    rec_type: RecordType,
    key: K,
    value: V,
}

/// # 2Q Cache
/// A cache data structure using the 2Q eviction logic. It serves as a
/// key-value storage for a limited amount of records.
/// 
/// This replacement policy is parameterized, meaning that its full capacity is
/// divided between three: capacities of the Q1, Q2 and M (main, "LRU") queues.
/// Example of how it can be created:
/// ```
/// let q1_capacity = 3;
/// let q2_capacity = 3;
/// let m_capacity = 10;
/// let mut cache = QCache::new(q1_capacity, q2_capacity, m_capacity);
/// ```
/// `cache` can now be used to store key-value pairs, we insert records with
/// the `insert` method:
/// ```
/// // Only keys that aren't present in the cache yet can be inserted
/// cache.insert(key1, value1);
/// cache.insert(key2, value2);
/// ```
/// The data structure never exceeds the given capacity of records (which is
/// the sum of the Q1, Q2 and M capacities) by evicting records using the 2Q
/// replacement policy.
/// 
/// Values for keys can be retrieved with the `get` function. The returned
/// value is an `Option`, it may be `None` if the record hasn't been inserted
/// at all, or was evicted by the replacement logic
/// ```
/// assert!(cache.get(&key1), Some(&value1));
/// ```
/// Both `insert` and `get` update the cache's internal state according to the
/// 2Q logic.
pub struct QCache<K: Clone + Eq + Hash, V> {
    // The given capacities of the queues
    q1_capacity: usize,
    q2_capacity: usize,
    lru_capacity: usize,
    // `map` for convenient accesses to nodes
    map: HashMap<K, NonNull<DLNode<Record<K, V>>>>,
    // The three queues
    queue1: DLList<Record<K, V>>,
    queue2: DLList<Record<K, V>>,
    lru: DLList<Record<K, V>>,
}

impl<K: Clone + Eq + Hash, V> QCache<K, V> {
    /// Create a new 2Q cache with the given capacities of internal queues. If
    /// you are unsure of what parameters to choose, our measurements suggest
    /// using this approach:
    /// * Choose the total capacity for the cache (it must be high enough for
    ///   the next points)
    /// * Set Q1 size as 10
    /// * Set Q2 size as the sixth of the total
    /// * (the main queue, "LRU" gets the rest)
    pub fn new(q1_capacity: usize, q2_capacity: usize, lru_capacity: usize) -> Self {
        Self {
            q1_capacity,
            q2_capacity,
            lru_capacity,
            map: HashMap::with_capacity(q1_capacity + q2_capacity + lru_capacity),
            queue1: DLList::new(),
            queue2: DLList::new(),
            lru: DLList::new(),
        }
    }

    /// Returns a reference to the value cached with this key, if cached.
    pub fn get<'a>(&'a mut self, key: &K) -> Option<&'a V> {
        match self.map.get(key) {
            Some(node_ptr) => {
                let node_ptr = node_ptr.clone();
                Some(self.access(node_ptr))
            }
            None => None,
        }
    }

    /// Performs a cache hit for the given node, returns a reference to the
    /// node's stored value.
    fn access<'a>(&'a mut self, node_ref: NonNull<DLNode<Record<K, V>>>) -> &'a V {
        let node = unsafe { &mut (*node_ref.as_ptr()) };
        match node.elem.rec_type {
            RecordType::Q2Elem => {
                // move a record inside the second queue to the main queue on new access
                node.elem.rec_type = RecordType::LRUElem;
                node.remove(&mut self.queue2);
                // in case the LRU would overflow, remove the last element
                if self.lru.size == self.lru_capacity {
                    if let Some(record) = self.lru.pop_back() {
                        self.map.remove(&record.key);
                    }
                }
                self.lru.insert_head(node as *mut DLNode<_>);
                self.lru.size += 1;
            }
            RecordType::LRUElem => {
                // classical LRU behavior
                node.move_to_front(&mut self.lru);
            }
            // no change for the first queue
            _ => {}
        }
        &node.elem.value
    }

    /// Submit this key-value pair for caching.
    /// The key must not yet be present in the cache!
    pub fn insert(&mut self, key: K, value: V) {
        if self.queue1.size == self.q1_capacity {
            // If Q1's capacity is reached overflow the back element to Q2
            if let Some(mut record) = self.queue1.pop_back() {
                let last_key = record.key.clone();
                record.rec_type = RecordType::Q2Elem;
                let record_ptr =
                    NonNull::new(Box::into_raw(Box::new(DLNode::new(record)))).unwrap();
                self.insert_into_q2(record_ptr);
                // The map's record must be updated with the new RecordType
                self.map.insert(last_key, record_ptr);
            }
        }
        // Generate the new record's node
        let mut new_record = NonNull::new(Box::into_raw(Box::new(DLNode::new(Record {
            rec_type: RecordType::Q1Elem,
            key: key.clone(),
            value,
        }))))
        .unwrap();
        // Insert it to the map and to Q1
        self.map.insert(key, new_record);
        unsafe {
            self.queue1
                .insert_head(new_record.as_mut() as *mut DLNode<_>);
        }
        self.queue1.size += 1;
    }

    /// Inserts given node to Q2. It must already have the right RecordType
    fn insert_into_q2(&mut self, mut node: NonNull<DLNode<Record<K, V>>>) {
        if self.queue2.size == self.q2_capacity {
            // If capacity reached, the back element is evicted
            if let Some(record) = self.queue2.pop_back() {
                self.map.remove(&record.key);
            }
        }
        // Perform the insertion itself
        unsafe {
            self.queue2.insert_head(node.as_mut() as *mut DLNode<_>);
        }
        self.queue2.size += 1;
    }
}

#[cfg(test)]
mod test {
    use super::QCache;

    #[test]
    fn simple() {
        // A basic test of the 2Q semantics
        let mut qq = QCache::new(2, 2, 3);
        assert_eq!(qq.get(&1), None);
        for i in 1..5 {
            qq.insert(i, 2 * i);
        }
        assert_eq!(qq.get(&3), Some(&6));
        assert_eq!(qq.get(&4), Some(&8));
        qq.insert(5, 10);
        qq.insert(6, 12);
        assert_eq!(qq.get(&1), None);
        assert_eq!(qq.get(&2), None);
        // 3 gets moved to the LRU
        assert_eq!(qq.get(&3), Some(&6));
        assert_eq!(qq.get(&6), Some(&12));
        qq.insert(7, 14);
        qq.insert(8, 16);
        assert_eq!(qq.get(&4), None);
        // 5 enters the LRU
        assert_eq!(qq.get(&5), Some(&10));
        assert_eq!(qq.get(&7), Some(&14));
        qq.insert(9, 18);
        qq.insert(10, 20);
        // all these modify the LRU:
        assert_eq!(qq.get(&7), Some(&14));
        assert_eq!(qq.get(&3), Some(&6));
        assert_eq!(qq.get(&8), Some(&16));

        assert_eq!(qq.get(&5), None);
        let expect = [8, 3, 7];
        let mut idx = 0;
        // Check the exact ordering in the LRU
        for elem in qq.lru.iter() {
            assert_eq!((elem.key, elem.value), (expect[idx], (expect[idx] * 2)));
            idx += 1;
        }
    }
}
