use crate::clock_pro::CLOCKProCache;
use ahash::AHasher;
use std::hash::Hash;
use std::hash::Hasher;
use std::sync::{Mutex, MutexGuard};

// Implementation of an associative set of CLOCK-Pro caches. This works by
// attempting to divide the cached key set uniformly into "slots" of uniform
// size by hashing the keys and having the hash set split uniformly.
// This means that we have several caches and each takes care of a different
// subset of keys. This is in an attempt to allow concurrent accesses to the
// whole cached set. If the working sets of keys of two transactions are
// disjoint, chances are that also the hashes of those keys divide into
// disjoint slots of our associative cache. Two threads can then take care of
// the two transactions simultaneously by each taking just the slots it needs.
// To ensure consistency, this structure has one main mutex that a thread needs
// to lock before locking the slots separately.
// All in all, the function that provides access handles to this associative
// cache (called `generate_mut_guard`) must:
// * Lock the main mutex (wait to get unique access for "slot selection")
// * One by one, lock all slots needed (wait 'till they aren't occupied)
// * Unlock the main mutex (allow other threads to take slots we didn't select)
// and after the transaction is done, it unlocks all the slots again.

// This macro receives a `key` (that implements Hash), and the number of slots
// that we divide our cache into. It "returns" the slot this key belongs to.
macro_rules! hash_choice {
    ($key:expr, $cache_count:expr) => {{
        // Choice of hasher keys is arbitrary.
        let mut hasher = AHasher::new_with_keys(3, 7);
        $key.hash(&mut hasher);
        let divisor = u64::MAX / $cache_count as u64;
        (hasher.finish(generate_mut_guard) / divisor) as usize
    }};
}

/// # CLOCK-Pro Associative
///
/// This splits the cache's key set into "slots" and enables acquiring unique
/// access by slots. In fact, each slot is its own CLOCK-Pro cache. Once a
/// thread needs to access a known set of keys, it can get unique access to
/// their respective slots by calling the `generate_mut_guard` method, which
/// generates a `CLOCKProAssociativeGuard` struct, providing unique access to
/// all slots containing the keys.
/// It can also get unique access to simply all the slots at once with the
/// `generate_unique_access_guard` function.
///
/// ## Example usage
/// ```
/// // Create a new associative cache with a total of 300 maximum records split
/// // between 20 "slots"
/// let cache = CLOCKProAssociative::new(300, 20);
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
pub struct CLOCKProAssociative<K: Clone + Eq + Hash, V> {
    main_lock: Mutex<()>,
    slot_vec: Vec<Mutex<CLOCKProCache<K, V>>>,
}

pub struct CLOCKProAssociativeGuard<'a, K: Clone + Eq + Hash, V> {
    guard_vec: Vec<Option<MutexGuard<'a, CLOCKProCache<K, V>>>>,
}

unsafe impl<K: Clone + Eq + Hash, V> Send for CLOCKProAssociative<K, V> {}
unsafe impl<K: Clone + Eq + Hash, V> Sync for CLOCKProAssociative<K, V> {}

impl<K: Clone + Eq + Hash, V> CLOCKProAssociative<K, V> {
    /// Creates a new associative CLOCK-Pro cache. If the `slot_count` doesn't
    /// divide `capacity_total`, all slots will have the capacity of the floor
    /// value of the division.
    pub fn new(capacity_total: usize, slot_count: usize) -> Self {
        let capacity_slot = capacity_total / slot_count;
        // Prepare the struct.
        let mut cache = Self {
            main_lock: Mutex::new(()),
            slot_vec: Vec::with_capacity(slot_count),
        };
        // Insert all the slots.
        for _ in 0..slot_count {
            cache
                .slot_vec
                .push(Mutex::new(CLOCKProCache::new(capacity_slot)));
        }
        cache
    }

    pub fn generate_mut_guard(&self, keys: &Vec<K>) -> CLOCKProAssociativeGuard<K, V> {
        let slot_count = self.slot_vec.len();
        // Prepare the struct
        let mut cache_guard = CLOCKProAssociativeGuard {
            guard_vec: Vec::with_capacity(slot_count),
        };
        // First, leave all mutex guards uninitiated
        let mut slots_locked = 0;
        for _ in 0..slot_count {
            cache_guard.guard_vec.push(None);
        }
        // Lock the main mutex to have unique access for slot locking
        let _main_lock = self.main_lock.lock().unwrap();
        // Key by key, get the guard for the corresponding slot
        for k in keys.iter() {
            let slot_idx = hash_choice!(*k, slot_count);
            if cache_guard.guard_vec[slot_idx].is_none() {
                cache_guard.guard_vec[slot_idx] = Some(self.slot_vec[slot_idx].lock().unwrap());
                slots_locked += 1;
            }
            if slots_locked == slot_count {
                // All locks are already locked
                break;
            }
        }
        // Just to be explicit about when the lock is released
        drop(_main_lock);
        cache_guard
    }

    /// A special function generating a guard that provides unique access to
    /// the whole extent of the cache (all slots).
    pub fn generate_unique_access_guard(&self) -> CLOCKProAssociativeGuard<K, V> {
        let slot_count = self.slot_vec.len();
        let mut cache_guard = CLOCKProAssociativeGuard {
            guard_vec: Vec::with_capacity(slot_count),
        };
        // Lock the main mutex to have unique access to slot locking
        let _main_lock = self.main_lock.lock().unwrap();
        // Lock all the keys
        for slot_idx in 0..slot_count {
            let slot_guard = self.slot_vec[slot_idx].lock().unwrap();
            cache_guard.guard_vec.push(Some(slot_guard));
        }
        // Just to be explicit about when the lock is released
        drop(_main_lock);
        cache_guard
    }
}

impl<'a, K: Clone + Eq + Hash, V> CLOCKProAssociativeGuard<'a, K, V> {
    /// Returns a reference to the value for given key, if it is cached.
    pub fn get<'b>(&'b mut self, key: &K) -> Option<&'b V> {
        (**self.obtain_slot_guard(key)).get(key)
    }

    /// Returns a mutable reference to the value for given key, if it is
    /// cached.
    pub fn get_mut<'b>(&'b mut self, key: &K) -> Option<&'b mut V> {
        (**self.obtain_slot_guard(key)).get_mut(key)
    }

    /// Submit this key-value pair for caching.
    /// The key must not be present in the cache yet!
    pub fn insert(&mut self, key: K, value: V) {
        (**self.obtain_slot_guard(&key)).insert(key, value)
    }

    /// A utility function that obtains the MutexGuard for the key that given
    /// key belongs to.
    fn obtain_slot_guard<'b>(&'b mut self, key: &K) -> &'b mut MutexGuard<'a, CLOCKProCache<K, V>> {
        let slot_idx = hash_choice!(*key, self.guard_vec.len());
        match self.guard_vec[slot_idx] {
            Some(ref mut slot_guard) => slot_guard,
            None => panic!("Invalid request. Attempt to access a slot that wasn't acquired."),
        }
    }
}

#[cfg(test)]
mod test {
    use super::CLOCKProAssociative;
    use rand::{thread_rng, Rng};

    #[test]
    fn simple() {
        // This test checks the function of basic associative cache semantics.

        // Create an associative cache with 4 slots each with a capacity of 8
        // records.
        let cache = CLOCKProAssociative::new(32, 4);
        // Acquire access for two specific keys and use it.
        let mut cache_guard = cache.generate_mut_guard(&vec![2, 4]);
        cache_guard.insert(2, 2);
        cache_guard.insert(4, 4);
        drop(cache_guard);
        // Access one of the records again, and also a new one.
        let mut cache_guard = cache.generate_mut_guard(&vec![4, 6]);
        let mut4 = cache_guard.get_mut(&4).unwrap();
        *mut4 = 100;
        cache_guard.insert(6, 6);
        drop(cache_guard);

        // Check all three records are cached correctly.
        let mut cache_guard = cache.generate_mut_guard(&vec![2, 4, 6]);
        assert_eq!(cache_guard.get(&2), Some(&2));
        assert_eq!(cache_guard.get(&4), Some(&100));
        assert_eq!(cache_guard.get(&6), Some(&6));
    }

    #[test]
    fn smoke_test() {
        // Tests that the associative cache keeps the limit number of elements.
        let cache = CLOCKProAssociative::new(25, 5);
        // First, we need to fill it
        let mut max_elem = 0;
        loop {
            let curr_max = max_elem;
            for k in 0..30 {
                let mut cache_guard = cache.generate_mut_guard(&vec![curr_max + k]);
                cache_guard.insert(curr_max + k, ());
                max_elem += 1;
            }
            let elem_count = count_elements(&cache, max_elem);
            if elem_count >= 25 {
                assert_eq!(elem_count, 25);
                break;
            }
        }

        // Now we keep accessing (and inserting) random elements and always
        // make sure there is still the maximum number of elements present in
        // the cache.
        max_elem *= 3;
        let mut rng = thread_rng();
        for _ in 0..1000 {
            let key = rng.gen_range(0, max_elem);
            let mut cache_guard = cache.generate_mut_guard(&vec![key]);
            let record = cache_guard.get(&key);
            if record.is_none() {
                cache_guard.insert(key, ());
            }
            drop(cache_guard);

            assert_eq!(count_elements(&cache, max_elem), 25);
        }
    }

    #[test]
    fn smoke_test_unique_access() {
        // Tests that random modifications to the cache by a guard for unique
        // access keeps the limit number of cached elements.
        let cache = CLOCKProAssociative::new(25, 5);
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

    // Counts how many elements (between 0 and {max_elem - 1}) there are present
    // in the cache.
    fn count_elements(cache: &CLOCKProAssociative<u32, ()>, max_elem: u32) -> usize {
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
