// SPDX-FileCopyrightText: 2024 2023 Martin Koreček
//
// SPDX-License-Identifier: GPL-3.0-or-later

// Implementation of an associative set of LRU caches. We call the caches in the set 'slots'. We
// attempt to divide records into uniformly large sets, and have each slot only keep records from
// one of these sets.
// 
// The way we do it is by hashing the records' keys and splitting the hash set uniformly. The
// reason we split the cache thus is to try allow concurrent accesses to the cache. If the sets of
// records two transactions need to access are disjoint, chances are that also the slots each of
// the sets fall into are disjoint. Two threads can then perform the two transactions
// simultaneously, each acquiring unique access just to the 'slots' it needs.
// 
// The way we implement it here, to prevent deadlock, is by having one main Mutex for the whole
// associative cache and separate Mutexes for each slot. When a thread wants to get unique access
// to slots for some particular keys, it will (via the `generate_mut_guard` method):
// * Lock the main Mutex (i.e. wait to get unique access for "slot selection")
// * One by one, lock all slots needed (i.e. wait untill they aren't occupied by another thread(s))
// * Unlock the main Mutex (allow other threads to take slots that we didn't select)
// 
// (after the transaction is finished, it unlocks all the slots again, simply by dropping the
// handle)

use crate::lru::LRUCache;
use ahash::AHasher;
use std::hash::Hash;
use std::hash::Hasher;
use std::sync::{Mutex, MutexGuard};

// This macro receives a `key` (that implements Hash), and the number of slots
// that we divide our cache into. It "returns" the slot this key belongs to.
macro_rules! hash_choice {
    ($key:expr, $cache_count:expr) => {{
        // Choice of hasher keys is arbitrary.
        let mut hasher = AHasher::new_with_keys(3, 7);
        $key.hash(&mut hasher);
        let divisor = u64::MAX / $cache_count as u64;
        (hasher.finish() / divisor) as usize
    }};
}
/// # LRU Associative
///
/// This splits the cache's key set into "slots" and enables acquiring unique
/// access to slots. In fact, each slot is its own LRU cache. Once a
/// thread needs to access a known set of keys, it can get unique access to
/// their respective slots by calling the `generate_mut_guard` method, which
/// generates a `LRUAssociativeGuard` struct, providing unique access to
/// all slots containing the keys.
/// It can also get unique access to simply all the slots at once with the
/// `generate_unique_access_guard` function.
///
/// ## Example usage
/// ```
/// // Create a new associative cache with a total of 300 maximum records split
/// // between 20 "slots"
/// let cache = LRUAssociative::new(300, 20);
///
/// // ... let's imagine the cache gets occupied with key-value pairs here ...
///
/// // We acquire unique access to two specific keys
/// let mut cache_guard = cache.generate_mut_guard(&vec![X, Y]);
/// // (We imagine) one is retrieved successfully, one is not and gets inserted
/// // to the cache.
/// assert!(cache_guard.get(&X).is_some());
/// assert!(cache_guard.get(&Y).is_none());
/// cache_guard.insert(Y, Y_value);
/// // Only once the cache guard is dropped, other threads may access the
/// // occupied slots
/// drop(cache_guard);
///
/// // Now we get a cache guard for the whole cache (all slots; perhaps because
/// // we don't yet know what exact keys we will be accessing)
/// let mut cache_guard = cache.generate_unique_access_guard();
/// // No other thread may access any of the slots now
///
/// // We may access any keys we want with this guard
/// *cache.get_mut(&Z).unwrap() = Z_new_value;
/// assert_eq!(cache_guard.get(&Y), Some(&Y_value));
///
/// drop(cache_guard);
/// ```
pub struct LRUAssociative<K: Clone + Eq + Hash, V> {
    main_lock: Mutex<()>,
    slot_vec: Vec<Mutex<LRUCache<K, V>>>,
}

pub struct LRUAssociativeGuard<'a, K: Clone + Eq + Hash, V> {
    guard_vec: Vec<Option<MutexGuard<'a, LRUCache<K, V>>>>,
}

unsafe impl<K: Clone + Eq + Hash, V> Send for LRUAssociative<K, V> {}
unsafe impl<K: Clone + Eq + Hash, V> Sync for LRUAssociative<K, V> {}

impl<K: Clone + Eq + Hash, V> LRUAssociative<K, V> {
    /// Creat
    pub fn new(capacity_total: usize, slot_count: usize) -> Self {
        let slot_capacity = capacity_total / slot_count;
        // Prepare the struct
        let mut cache = Self {
            main_lock: Mutex::new(()),
            slot_vec: Vec::with_capacity(slot_count),
        };
        // Insert all the slots
        for _ in 0..slot_count {
            cache.slot_vec.push(Mutex::new(LRUCache::new(slot_capacity)));
        }
        cache
    }

    /// This method takes a reference to a vector of record keys that a thread
    /// may need to access. It returns a handle that enables unique access to
    /// exactly the cache slots the given keys belong to.
    pub fn generate_mut_guard(&self, keys: &Vec<K>) -> LRUAssociativeGuard<K, V> {
        let slot_count = self.slot_vec.len();
        // Prepare the struct
        let mut cache_guard = LRUAssociativeGuard {
            guard_vec: Vec::with_capacity(slot_count),
        };
        // First, leave all mutex guards uninitiated
        let mut slots_locked = 0;
        for _ in 0..slot_count {
            cache_guard.guard_vec.push(None);
        }
        // Lock the main mutex to be the only thread locking slots
        let _main_lock = self.main_lock.lock().unwrap();
        // Key by key, get the guard for the corresponding slot
        for k in keys.iter() {
            let slot_idx = hash_choice!(*k, slot_count);
            // If we don't have unique access to this slot yet, acquire it
            if cache_guard.guard_vec[slot_idx].is_none() {
                cache_guard.guard_vec[slot_idx] = Some(self.slot_vec[slot_idx].lock().unwrap());
                slots_locked += 1;
            }
            if slots_locked == slot_count {
                // We have unique access to all slots already
                break;
            }
        }
        // Just to be explicit about when the lock is released
        drop(_main_lock);
        cache_guard
    }

    /// A special function generating a guard that provides unique access to
    /// the whole extent of the cache (all slots).
    pub fn generate_unique_access_guard(&self) -> LRUAssociativeGuard<K, V> {
        let slot_count = self.slot_vec.len();
        let mut cache_guard = LRUAssociativeGuard {
            guard_vec: Vec::with_capacity(slot_count),
        };
        // Lock the main mutex to have unique access to slot locking
        let _main_lock = self.main_lock.lock().unwrap();
        // Lock all the keys
        for slot_idx in 0..slot_count {
            let slot_guard = self.slot_vec[slot_idx].lock().unwrap();
            cache_guard.guard_vec.push(Some(slot_guard));
        }
        // Just to be explicit about releasing the lock
        drop(_main_lock);
        cache_guard
    }
}

impl<'a, K: Clone + Eq + Hash, V> LRUAssociativeGuard<'a, K, V> {
    /// Returns a reference to the value for given key, if cached.
    pub fn get<'b>(&'b mut self, key: &K) -> Option<&'b V> {
        (**self.obtain_slot_guard(key)).get(key)
    }

    /// Submit this key-value pair for caching.
    /// The key must not be present in the cache yet!
    pub fn insert(&mut self, key: K, value: V) {
        (**self.obtain_slot_guard(&key)).insert(key, value);
    }

    /// A utility function that obtains the MutexGuard for the key that given
    /// key belongs to.
    fn obtain_slot_guard<'b>(&'b mut self, key: &K) -> &'b mut MutexGuard<'a, LRUCache<K, V>> {
        let slot_idx = hash_choice!(*key, self.guard_vec.len());
        match self.guard_vec[slot_idx] {
            Some(ref mut slot_guard) => slot_guard,
            // If we don't have the MutexGuard for this slot, we panic.
            None => panic!("Invalid request. Attempt to access a slot that wasn't acquired."),
        }
    }
}

#[cfg(test)]
mod test {
    use super::LRUAssociative;
    use rand::{thread_rng, Rng};

    #[test]
    fn simple() {
        // This test checks the function of basic associative cache semantics.

        // Create an associative cache with 4 slots each with a capacity of 8
        // records.
        let cache = LRUAssociative::new(32, 4);
        // Acquire access for two specific keys and use it.
        let mut cache_guard = cache.generate_mut_guard(&vec![2, 4]);
        cache_guard.insert(2, 2);
        cache_guard.insert(4, 4);
        drop(cache_guard);
        // Access one of the records again, and also a new one.
        let mut cache_guard = cache.generate_mut_guard(&vec![4, 6]);
        assert_eq!(cache_guard.get(&4), Some(&4));
        cache_guard.insert(6, 6);
        drop(cache_guard);

        // Check all three records are cached correctly.
        let mut cache_guard = cache.generate_mut_guard(&vec![2, 4, 6]);
        assert_eq!(cache_guard.get(&2), Some(&2));
        assert_eq!(cache_guard.get(&4), Some(&4));
        assert_eq!(cache_guard.get(&6), Some(&6));
    }

    #[test]
    fn smoke_test() {
        // Tests that the associative cache keeps the limit number of elements.
        let cache = LRUAssociative::new(25, 5);
        // First, we need to fill it
        let mut max_elem = 0;
        loop {
            // We can't guarantee any specific number of records fills all
            // slots, therefore we add keys sequentially until the cache's full
            let curr_max = max_elem;
            for k in 0..30 {
                let mut cache_guard = cache.generate_mut_guard(&vec![curr_max + k]);
                cache_guard.insert(curr_max + k, ());
                max_elem += 1;
            }
            let elem_count = count_elements(&cache, max_elem);
            // We have filled the whole cache:
            if elem_count >= 25 {
                assert_eq!(elem_count, 25);
                break;
            }
        }

        // Now we keep accessing (and inserting) random elements and always
        // make sure there is still the maximum number of elements present in
        // the cache.
        // We will pick the keys we access at random out of a range thrice the
        // size of the range we have used to fill the cache (arbitrary choice).
        max_elem *= 3;
        let mut rng = thread_rng();
        for _ in 0..1000 {
            // Pick random key to access
            let key = rng.gen_range(0, max_elem);
            // Get the guard for it
            let mut cache_guard = cache.generate_mut_guard(&vec![key]);
            let record = cache_guard.get(&key);
            // If it isn't present, insert it
            if record.is_none() {
                cache_guard.insert(key, ());
            }
            drop(cache_guard);

            // Always check that the cache still keeps the right (limit) number
            // of elements
            assert_eq!(count_elements(&cache, max_elem), 25);
        }
    }

    #[test]
    fn smoke_test_unique_access() {
        // Tests that random modifications to the cache by a guard for unique
        // access keeps the limit number of cached elements.
        // This is the same test concept as `smoke_test`, but we get unique
        // access to all slots.
        let cache = LRUAssociative::new(25, 5);
        // First, we will fill the cache
        let mut max_elem = 0;
        loop {
            let curr_max = max_elem;
            let mut cache_guard = cache.generate_unique_access_guard();
            for k in 0..100 {
                cache_guard.insert(curr_max + k, ());
                max_elem += 1;
            }
            drop(cache_guard);
            let elem_count = count_elements(&cache, max_elem);
            if elem_count >= 25 {
                assert_eq!(elem_count, 25);
                break;
            }
        }

        // Now we keep accessing (and inserting) elements at random and we
        // always make sure there is still the maximum number of elements
        // present in the cache.
        max_elem *= 4;
        let mut rng = thread_rng();
        for _ in 0..1000 {
            let mut cache_guard = cache.generate_unique_access_guard();
            for _ in 0..5 {
                let key = rng.gen_range(0, max_elem);
                if cache_guard.get(&key).is_none() {
                    cache_guard.insert(key, ());
                }
            }
            drop(cache_guard);

            assert_eq!(count_elements(&cache, max_elem), 25);
        }
    }

    /// Counts how many elements (or rather keys between 0 and {max_elem - 1})
    /// there are present in the cache.
    fn count_elements(cache: &LRUAssociative<u32, ()>, max_elem: u32) -> usize {
        let mut count = 0;
        for k in 0..max_elem {
            let mut cache_guard = cache.generate_mut_guard(&vec![k]);
            if cache_guard.get(&k).is_some() {
                count += 1;
            }
        }
        count
    }
}
