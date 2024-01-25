// SPDX-FileCopyrightText: 2024 2023 Martin Koreček
//
// SPDX-License-Identifier: GPL-3.0-or-later

// An implementation of the LIRS cache replacement policy based on
// Jiang, Zhang: LIRS: An Efficient Low Inter-reference Recency Set Replacement Policy to Improve
// Buffer Cache Performance
// (http://web.cse.ohio-state.edu/hpcs/WWW/HTML/publications/abs02-6.html)
//
// The most important logical block of this data structure is the access_queue, where accesses
// (both inserts and gets) to specific keys are recorded in a FIFO order.
// There are two types of cache records, LIRs (low inter-reference) and HIRs (high i-r), these are
// further divided into three types based on their appearance in the access queue and their value's
// residency in the cache.
//
// While lir_capacity (the maximum chosen amount of LIR records at one point) isn't filled yet,
// this cache acts just like the LRU. Once this capacity is reached, elements that would be evicted
// from an LRU are instead turned into (resident, but missing an access record) HIR elements and
// pushed into our resident_hirs queue.
//
// Once both lir_capacity and hir_capacity (ie. the total allowed amount of resident - cached
// values) are reached and new records are inserted, we evict the back (queue front) element of
// resident_hirs, but leave its potential access record. If the inserted element is found in the
// access_queue (ie. it is a non-resident HIR), it turns into a LIR and pushes the back LIR in the
// access queue out, turning it into a HIR element (with no recorded access). If the inserted
// element has no access record, on the other hand, It is inserted as a 'full' HIR, both at the
// front of access_queue and resident_hirs queues. For this to work properly, the access_queue tail
// is always a LIR record, potential HIRs occuring at the tail are simply popped out.
//
// All this is enabled via 'map', a hash map that lets us access these records in constant time
// and also is the only component of our data structure that lets us determine record types.

use crate::list::{DLList, DLNode};
use std::collections::HashMap;
use std::hash::Hash;
use std::ptr::NonNull;

// Records inside the record map mark their type.
// * LIR (with an access record and a boxed value)
// * non-resident HIR (only an access record for when the key might get reaccessed)
// * HIR without an access record (only the key-value pair among resident HIRs)
// * 'full' HIR record that has both an access record and an element in the resident HIRs queue
enum Record<K, V> {
    // An LIR element with the pointer to its' corresponding access queue record
    // and a Box including the cached value
    Lir(NonNull<DLNode<K>>, Box<V>),
    // An HIR-non-resident element; only has a pointer to the access queue
    HirNr(NonNull<DLNode<K>>),
    // An HIR-no-access element, which has a reference to the HIR queue record,
    // but isn't included in the access queue at all
    HirNa(NonNull<DLNode<(K, Box<V>)>>),
    // A full HIR element with both the 'recent' access record and HIR queue
    // record
    Hir(NonNull<DLNode<K>>, NonNull<DLNode<(K, Box<V>)>>),
}

impl<K, V> Record<K, V> {
    /// Is this record a LIR?
    fn is_lir(&self) -> bool {
        if let Self::Lir(_, _) = self {
            true
        } else {
            false
        }
    }
}

/// # LIRS Cache
/// A cache data structure using the LIRS eviction logic. It serves as a key
/// value storage for a limited amount of records.
/// 
/// This replacement policy is parameterized, its full capacity is divided
/// between a LIR-capacity and a HIR-capacity, which we need to select when
/// creating the cache struct.
/// ```
/// let mut cache = LIRSCache::new(50, 4);
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
/// LIRS logic.
pub struct LIRSCache<K: Clone + Eq + Hash, V> {
    // The maximum number of low inter-reference elements cached together
    lir_capacity: usize,
    // The maximum number of cached (resident) high inter-reference elements
    hir_capacity: usize,
    map: HashMap<K, Record<K, V>>,
    lir_count: usize,
    access_queue: DLList<K>,
    resident_hirs: DLList<(K, Box<V>)>,
}

impl<K: Clone + Eq + Hash, V> LIRSCache<K, V> {
    /// Create a new LIRS cache data structure instance.
    /// * The total maximum number of cached items will be lir_capacity + hir_capacity
    /// * Those parameters determine the maximum number of LIR and HIR records, respectively
    ///
    /// If you are unsure of what parameters to choose, determine the absolute maximum number of
    /// records that may be cached at one time and make the hir_capacity a tiny fraction of it (the
    /// original LIRS paper recommends fractions as little as 1% of the total capacity; also note
    /// that when there is a high amount of rarely, or only once, accessed keys, these keys stay
    /// recorded inside this cache's metadata; if your cached values are of similar size as keys,
    /// this may pose a big problem in determining how much space the cache might occupy in total)
    pub fn new(lir_capacity: usize, hir_capacity: usize) -> Self {
        Self {
            lir_capacity,
            hir_capacity,
            // We can't determine the hash map capacity in advance.
            // In fact, the cache logic allows adding an unlimited amount of
            // access records (non-resident HIRs)!
            map: HashMap::new(),
            lir_count: 0,
            access_queue: DLList::new(),
            resident_hirs: DLList::new(),
        }
    }

    /// Submit this key-value pair for caching.
    /// The key must not yet be present in the cache!
    pub fn insert(&mut self, key: K, value: V) {
        if self.lir_count < self.lir_capacity {
            // The maximum number of LIR records hasn't been reached yet.
            // Simply insert this key-value pair as a new LIR record
            self.insert_lir(key, value);
            return;
        }
        if self.resident_hirs.size < self.hir_capacity {
            // The access queue is full, but the maximum number of HIR elements
            // hasn't been reached yet.
            // Pop the back element of the access queue and change it into a
            // (resident) HIR record:
            if let Some(popped_key) = self.access_queue.pop_back() {
                if let Some(Record::Lir(_, boxed_val)) = self.map.remove(&popped_key) {
                    let mut hir_node = NonNull::new(Box::into_raw(Box::new(DLNode::new((
                        popped_key.clone(),
                        boxed_val,
                    )))))
                    .unwrap();
                    self.map.insert(popped_key, Record::HirNa(hir_node));
                    unsafe {
                        self.resident_hirs.insert_head(hir_node.as_mut());
                    }
                    self.resident_hirs.size += 1;
                } else {
                    panic!("Unreachable. A LIR record inside the access queue wasn't present or wasn't marked as LIR in the record hash map.");
                }
                self.lir_count -= 1;
                self.prune_queue();
            }
            // Now insert the new records as LIR
            self.insert_lir(key, value);
            return;
        }

        // Cache capacity has been reached. We replace an HIR element.
        // Remove the record at the back of resident_hirs:
        if let Some((popped_key, _)) = self.resident_hirs.pop_back() {
            if let Some(Record::Hir(access_ptr, _)) = self.map.remove(&popped_key) {
                // If the key is also present in the access queue, leave it there and convert the
                // record to a non-resident HIR. (otherwise it's simply removed altogether)
                self.map.insert(popped_key, Record::HirNr(access_ptr));
            }
        }
        // Insert the new record:
        self.insert_hir(key, value);
    }

    /// Returns a reference to the value cached with this key, if cached.
    pub fn get<'a>(&'a mut self, key: &K) -> Option<&'a V> {
        if let Some(ref record) = self.map.get(key) {
            match record {
                Record::Lir(_, _) => unsafe { Some(self.access_lir(key)) },
                Record::Hir(access_ptr, hir_ptr) => unsafe {
                    let access_ptr = access_ptr.clone();
                    let hir_ptr = hir_ptr.clone();
                    Some(self.access_hir(access_ptr, hir_ptr))
                },
                Record::HirNa(hir_ptr) => unsafe {
                    let hir_ptr = hir_ptr.clone();
                    Some(self.access_hir_no_access(hir_ptr))
                },
                Record::HirNr(access_ptr) => unsafe {
                    // The record is non-resident, but we may move it to the queue's front in case
                    // of future access.
                    (*access_ptr.as_ptr()).move_to_front(&mut self.access_queue);
                    None
                },
            }
        } else {
            None
        }
    }

    /// Works as 'get' when we know the record is a LIR one.
    unsafe fn access_lir<'a>(&'a mut self, key: &K) -> &'a V {
        if let Some(Record::Lir(access_ptr, _)) = self.map.get(key) {
            // move the record to the front
            (*access_ptr.as_ptr()).move_to_front(&mut self.access_queue);
            // The LIR might have been the tail element; try pruning tail HIRs
            self.prune_queue();
            // Necessary workaround so that the queue pruning is possible:
            if let Some(Record::Lir(_, boxed_val)) = self.map.get(key) {
                &*boxed_val
            } else {
                panic!("Unreachable.");
            }
        } else {
            panic!("Unreachable.");
        }
    }

    /// Works as 'get', where the record is a Record::Hir(access_ptr, hir_ptr).
    unsafe fn access_hir<'a>(
        &'a mut self,
        access_ptr: NonNull<DLNode<K>>,
        hir_ptr: NonNull<DLNode<(K, Box<V>)>>,
    ) -> &'a V {
        // The HIR record will turn into a LIR one.
        // Move access record to the front
        (*access_ptr.as_ptr()).move_to_front(&mut self.access_queue);
        // Turn the HIR record into a LIR:
        (*hir_ptr.as_ptr()).remove(&mut self.resident_hirs);
        let (taken_key, boxed_val) = (*Box::from_raw(hir_ptr.as_ptr())).elem;
        self.map
            .insert(taken_key.clone(), Record::Lir(access_ptr, boxed_val));
        // Turn the (LIR) record at the queue back into a HIR
        if let Some(k) = self.access_queue.pop_back() {
            if let Some(Record::Lir(_, boxed_val)) = self.map.remove(&k) {
                let mut hir_node =
                    NonNull::new(Box::into_raw(Box::new(DLNode::new((k.clone(), boxed_val)))))
                        .unwrap();
                self.map.insert(k, Record::HirNa(hir_node));
                self.resident_hirs.insert_head(hir_node.as_mut());
                self.resident_hirs.size += 1;
            } else {
                panic!("Unreachable. A LIR record inside the access queue wasn't present or wasn't marked as LIR in the record hash map.");
            }
        }
        self.prune_queue();
        // (lir_count stays the same)
        // Necessary workaround to return value reference:
        if let Record::Lir(_, ref boxed_val) = self.map.get(&taken_key).unwrap() {
            &**boxed_val
        } else {
            panic!("Unreachable.");
        }
    }

    /// Works as 'get', where the record is a Record::HirNa(hir_ptr)
    unsafe fn access_hir_no_access<'a>(
        &'a mut self,
        hir_ptr: NonNull<DLNode<(K, Box<V>)>>,
    ) -> &'a V {
        let key = (*hir_ptr.as_ptr()).elem.0.clone();
        // create an access node for this key
        let mut access_node =
            NonNull::new(Box::into_raw(Box::new(DLNode::new(key.clone())))).unwrap();
        // update record type
        self.map
            .insert(key.clone(), Record::Hir(access_node, hir_ptr));
        self.access_queue.insert_head(access_node.as_mut());
        self.access_queue.size += 1;
        // move the HIR to the front to approximate LRU behavior even in this queue
        (*hir_ptr.as_ptr()).move_to_front(&mut self.resident_hirs);
        &(*hir_ptr.as_ptr()).elem.1
    }

    /// When the LIR capacity isn't been reached yet, this enables us to insert
    /// a new LIR element to the front of the access queue
    fn insert_lir(&mut self, key: K, value: V) {
        let mut lir_node = NonNull::new(Box::into_raw(Box::new(DLNode::new(key.clone())))).unwrap();
        self.map.insert(key, Record::Lir(lir_node, Box::new(value)));
        unsafe {
            self.access_queue.insert_head(lir_node.as_mut());
        }
        self.access_queue.size += 1;
        self.lir_count += 1;
    }

    /// When the HIR capacity isn't reached, this method checks if given key is stored as a
    /// non-resident HIR and
    /// * if yes, it ejects the LRU LIR element and turns this non-resident HIR into a LIR
    /// * otherwise, this record is simply inserted as a new HIR
    fn insert_hir(&mut self, key: K, value: V) {
        if let Some(Record::HirNr(access_ptr)) = self.map.remove(&key) {
            // Remove the existing non-resident HIR record and drop it.
            unsafe {
                (*access_ptr.as_ptr()).remove(&mut self.access_queue);
                Box::from_raw(access_ptr.as_ptr());
            }
            // Turn the (LIR) record at the queue back into a HIR
            if let Some(k) = self.access_queue.pop_back() {
                if let Some(Record::Lir(_, boxed_val)) = self.map.remove(&k) {
                    let mut hir_node =
                        NonNull::new(Box::into_raw(Box::new(DLNode::new((k.clone(), boxed_val)))))
                            .unwrap();
                    self.map.insert(k, Record::HirNa(hir_node));
                    unsafe {
                        self.resident_hirs.insert_head(hir_node.as_mut());
                    }
                    self.resident_hirs.size += 1;
                } else {
                    panic!("Unreachable. A LIR record inside the access queue wasn't present or wasn't marked as LIR in the record hash map.");
                }
            }
            // remove all HIR records at the back to ensure access queue tail being a LIR record
            self.prune_queue();
            // insert the new record as a LIR
            let mut lir_node =
                NonNull::new(Box::into_raw(Box::new(DLNode::new(key.clone())))).unwrap();
            self.map.insert(key, Record::Lir(lir_node, Box::new(value)));
            unsafe {
                self.access_queue.insert_head(lir_node.as_mut());
            }
            self.access_queue.size += 1;
            // (LIR count remains the same)
        } else {
            // insert the new HIR, ie. create both the access record and resident HIR record.
            let mut access_node =
                NonNull::new(Box::into_raw(Box::new(DLNode::new(key.clone())))).unwrap();
            let mut hir_node = NonNull::new(Box::into_raw(Box::new(DLNode::new((
                key.clone(),
                Box::new(value),
            )))))
            .unwrap();
            self.map.insert(key, Record::Hir(access_node, hir_node));
            unsafe {
                self.access_queue.insert_head(access_node.as_mut());
                self.access_queue.size += 1;
                self.resident_hirs.insert_head(hir_node.as_mut());
                self.resident_hirs.size += 1;
            }
        }
    }

    /// Pops all HIR records from the back of our access queue.
    /// (this is to guarantee that the back element is always an LIR one)
    fn prune_queue(&mut self) {
        while let Some(ref access_key) = self.access_queue.get_back() {
            if !self.map.get(access_key).unwrap().is_lir() {
                // It is a HIR record.
                let hir_key = self.access_queue.pop_back().unwrap();
                // if non-resident, also remove from the record map, otherwise change record type
                if let Some(Record::Hir(_, resident_hir)) = self.map.remove(&hir_key) {
                    self.map.insert(hir_key, Record::HirNa(resident_hir));
                }
            } else {
                return;
            }
        }
    }
}

#[cfg(test)]
mod test {
    use super::LIRSCache as LIRS;
    use rand::{thread_rng, Rng};
    use std::fmt::Debug;
    use std::hash::Hash;

    #[test]
    fn simple() {
        // A basic test of the cache's semantics
        let mut lirs = LIRS::new(3, 2);
        assert_eq!(lirs.get(&1), None);
        lirs.insert(1, 2);
        assert_eq!(lirs.get(&1), Some(&2));

        // Each time, we perform intentional insertions and gets, and check the
        // state of the cache is as we expect.
        lirs.insert(2, 4);
        lirs.insert(3, 6);
        assert_eq!(lirs.get(&2), Some(&4));
        lirs.insert(4, 8);
        lirs.insert(5, 10);
        check_queue_elements(&lirs, 3, vec![5, 4, 2], vec![3, 1]);

        assert_eq!(lirs.get(&3), Some(&6));
        assert_eq!(lirs.get(&1), Some(&2));
        lirs.insert(6, 12);
        assert_eq!(lirs.get(&3), None);
        assert_eq!(lirs.get(&1), Some(&2));
        lirs.insert(7, 12);
        check_queue_elements(&lirs, 3, vec![7, 1, 3, 6, 5, 4], vec![7, 2]);

        assert_eq!(lirs.get(&6), None);
        lirs.insert(6, 12);
        assert_eq!(lirs.get(&1), Some(&2));
        lirs.insert(8, 16);
        assert_eq!(lirs.get(&8), Some(&16));
        check_queue_elements(&lirs, 3, vec![8, 1, 6], vec![5, 4]);
    }

    /// Check the exact state of the cache and its utility queues.
    fn check_queue_elements<K>(
        cache: &LIRS<K, K>,
        lir_count: usize,
        expect_access_keys: Vec<K>,
        expect_hir_keys: Vec<K>,
    ) where
        K: Eq + Clone + Hash + Debug,
    {
        assert_eq!(cache.lir_count, lir_count);
        assert_eq!(cache.access_queue.size, expect_access_keys.len());
        assert_eq!(cache.resident_hirs.size, expect_hir_keys.len());

        let mut access_iter = cache.access_queue.iter();
        for key in expect_access_keys.iter() {
            assert_eq!(access_iter.next(), Some(key));
        }
        assert_eq!(access_iter.next(), None);

        let mut hir_iter = cache.resident_hirs.iter();
        for key in expect_hir_keys.iter() {
            assert_eq!(hir_iter.next().unwrap().0, *key);
        }
        assert_eq!(hir_iter.next(), None);
    }

    #[test]
    fn smoke_test() {
        // Makes sure the cache always returns the correct number of elements.
        let mut rng = thread_rng();
        let mut lirs = LIRS::new(30, 10);
        for i in 0..40 {
            lirs.insert(i, i);
            check_access_back_lir(&lirs);
        }

        for _ in 0..2000 {
            let key = rng.gen_range(0, 200);
            let miss = lirs.get(&key).is_none();
            check_access_back_lir(&lirs);
            if miss {
                lirs.insert(key, key);
            }
            check_access_back_lir(&lirs);

            // Check that there are exactly 40 cached records
            let mut count = 0;
            for k in 0..200 {
                let record = lirs.get(&k);
                if let Some(val) = record {
                    assert_eq!(val, &k);
                    count += 1;
                }
                check_access_back_lir(&lirs);
            }
            assert_eq!(count, 40);
        }
    }

    /// Check that the access queue's back element is a LIR record (which is a
    /// LIRS invariant).
    fn check_access_back_lir(cache: &LIRS<u32, u32>) {
        if let Some(ref access_key) = cache.access_queue.get_back() {
            assert!(cache.map.get(access_key).unwrap().is_lir());
        } else {
            panic!("Access queue returned None for its back element");
        }
    }
}
