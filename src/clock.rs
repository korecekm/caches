// This is an implementation of the basic CLOCK replacement cache.
// The imaginary circular linked list is implemented with an array (called clock) in which we move
// our `insertion_idx` index. For constant-time searching for the list's elements, and also storing
// the cached values themselves, there is `map`.
//
// `get` doesn't modify our structure in any other way except setting an access bit for the key in
// question. That way we know a reaccess occured.
//
// If `insert` needs to evict an element, it moves `insertion_idx` until it finds a record with an
// unset access bit (which means it hasn't been reaccessed since its' insertion) and exchanges this
// record for the new one.

use std::collections::HashMap;
use std::hash::Hash;
use std::mem::MaybeUninit;

/// # CLOCK Cache
/// A cache data structure using the CLOCK eviction logic. It serves as a
/// key-value storage for a limited amount of records.
/// 
/// The capacity is set with const generics, so it is hardwired to the type. We
/// create a CLOCKCache struct with the `new` function.
/// ```
/// let mut cache = CLOCKCache::<key_type, value_type, CAPACITY>::new();
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
/// CLOCK logic.
pub struct CLOCKCache<K: Clone + Eq + Hash, V, const CAPACITY: usize> {
    // Our map stores indices inside `clock` and boxed values for stored keys.
    map: HashMap<K, (usize, Box<V>)>,
    // This "modular" array simulates the logical circular linked list.
    // Each tuple holds the key in question and its' corresponding access "bit"
    clock: MaybeUninit<[(K, bool); CAPACITY]>,
    // This is the imaginary linked list's head (tail)
    insertion_idx: usize,
}

impl<K: Clone + Eq + Hash, V, const CAPACITY: usize> CLOCKCache<K, V, CAPACITY> {
    pub fn new() -> Self {
        Self {
            map: HashMap::with_capacity(CAPACITY),
            clock: MaybeUninit::uninit(),
            insertion_idx: 0,
        }
    }

    /// Returns a value reference for the given key, if it is present in the cache.
    pub fn get<'a>(&'a mut self, key: &K) -> Option<&'a V> {
        match self.map.get(key) {
            Some((clock_idx, boxed_val)) => {
                // Set the approptiate access bit to 1
                unsafe {
                    (*(self.clock.as_ptr() as *mut [(K, bool); CAPACITY]))[*clock_idx].1 = true;
                }
                // return the value reference
                Some(&**boxed_val)
            }
            None => None,
        }
    }

    /// Submits this key-value pair for caching.
    /// The key must not already be present in the structure.
    pub fn insert(&mut self, key: K, value: V) {
        // If needed, evict a record:
        if self.map.len() == CAPACITY {
            // Skip records with a set access bit.
            loop {
                let access_bit = unsafe {
                    &mut (*(self.clock.as_ptr() as *mut [(K, bool); CAPACITY]))[self.insertion_idx]
                        .1
                };
                if !*access_bit {
                    // Access bit is unset.
                    break;
                }
                *access_bit = false;
                self.insertion_idx += 1;
                self.insertion_idx %= CAPACITY;
            }
            // Remove the record from the map
            let evict_key = unsafe { &(*self.clock.as_ptr())[self.insertion_idx].0 };
            self.map.remove(evict_key);
        }
        // Insert the new record:
        self.map
            .insert(key.clone(), (self.insertion_idx, Box::new(value)));
        unsafe {
            (*(self.clock.as_ptr() as *mut [(K, bool); CAPACITY]))[self.insertion_idx] =
                (key, false);
        }
        self.insertion_idx += 1;
        self.insertion_idx %= CAPACITY;
    }
}

#[cfg(test)]
mod test {
    use super::CLOCKCache as Clock;
    use rand::{thread_rng, Rng};
    use std::fmt::Debug;
    use std::hash::Hash;

    #[test]
    fn simple() {
        // A basic test of the cache's semantics
        let mut cache = Clock::<_, _, 4>::new();
        cache.insert(0, 0);
        cache.insert(1, 2);
        assert_eq!(cache.get(&0), Some(&0));
        cache.insert(2, 4);
        cache.insert(3, 6);
        assert_eq!(cache.get(&2), Some(&4));

        // Access bit is set for keys 0 and 2, try two evictions:
        cache.insert(4, 8);
        cache.insert(5, 10);
        check_clock_content(&cache, [(0, false), (4, false), (2, false), (5, false)]);

        // Access all of the elements
        assert_eq!(cache.get(&4), Some(&8));
        assert_eq!(cache.get(&0), Some(&0));
        assert_eq!(cache.get(&2), Some(&4));
        assert_eq!(cache.get(&5), Some(&10));
        check_clock_content(&cache, [(0, true), (4, true), (2, true), (5, true)]);
        // The eviction should now overflow back to index 0
        cache.insert(6, 12);
        assert_eq!(cache.get(&2), Some(&4));
        check_clock_content(&cache, [(6, false), (4, false), (2, true), (5, false)]);
    }

    /// Receives a CLOCK cache and an array and ensures, the contents of the
    /// array match those of the CLOCK's inner array
    fn check_clock_content<K, const CAPACITY: usize>(
        cache: &Clock<K, K, CAPACITY>,
        expect_array: [(K, bool); CAPACITY],
    ) where
        K: Clone + Eq + Hash + Debug,
    {
        for i in 0..CAPACITY {
            let clock_record = unsafe { &(*cache.clock.as_ptr())[i] };
            assert_eq!(&expect_array[i], clock_record);
        }
    }

    #[test]
    fn smoke_test() {
        // Doesn't test the cache semantics, only makes sure the cache always
        // returns the correct number of elements.
        let mut rng = thread_rng();
        let mut cache = Clock::<_, _, 25>::new();
        // First, insert 25 elements to fill the cache
        for i in 0..25 {
            cache.insert(i, i);
        }

        for _ in 0..1000 {
            let key = rng.gen_range(0, 200);
            let record = cache.get(&key);
            if record.is_none() {
                cache.insert(key, key);
            }

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
