// An implementation of the CLOCK-Pro cache replacement policy based on
// Jiang, Chen, Zhang: CLOCK-Pro: An Effective Improvement of the Clock Replacement
// (https://www.usenix.org/conference/2005-usenix-annual-technical-conference/clock-pro-effective-improvement-clock-replacement)
//
// The paper isn't fully explicit in all aspects of the structure's behavior, notably it doesn't
// say anything about how exactly it should function when there are no hot records yet, but in
// cases where the paper specified the functionality, this implementation tries to be obedient.
//
// Similarly to LIRS, we work with cold and hot records, where cold ones may also be non-resident,
// meaning that they don't store any value for their key and only function as logical elements for
// when the key gets reaccessed. The records also have a 'referenced' and 'test' (that one only for
// cold records) bits that partake in the logic.
//
// All records are kept in a circular (doubly) linked list, 'fast' searching in that list is
// provided by a hash map. In the 'final' case (once the structure is fully initiated), we also
// have three special pointers to the list's nodes, called hand_hot, hand_cold and hand_test.
// When a resident record is reaccessed, no movement takes place in the list, only the reference
// bit is set to the reaccessed record.
//
// `hand_cold` is the most important one, it provides the mechanism for record evictions, either by
// removing a value to a resident cold record, or removing the record altogether. It's always the
// resident colds that get evicted. Hot records don't get evicted directly. The hand also turns
// certain cold records (the referenced ones that are in their test periods) into hot ones.
// It is also the only 'hand' that is initiated from the very first record and it temporarily
// functions as the list's head.
//
// `hand_hot`'s main purpose is to turn hot records back into colds (those that haven't been
// referenced - it unsets the referenced bit to the rest), and it additionally functions exactly
// like hand_test towards cold records.
// Paradoxically, this way, hand_hot may be called to get rid of a hot record if they exceed their
// capacity, detect a cold record that passed its test period without getting reaccessed, which
// increases the capacity of hots and makes the actual hot record riddance unnecessary.
// Once this hand is non-null, it also acts as the list's head (records are inserted behind it).
//
// `hand_test` is there to eventually remove non-resident cold records if their capacity were to be
// exceeded. It also finishes test periods of cold records.
//
// The cache has a given capacity, out of which a fraction belongs to resident cold records and the
// rest to the hot records. The granted fractions change adaptively, both are never less than 2 and
// the capacity of hots start at 2 (the lower limit of 2 is chosen quite arbitrarily, isn't decided
// in the paper and may be changed to a higher number - not lower though, to keep the structure'
// functionality).
// Non-resident cold records are treated separately and are granted another full capacity (ie.
// there may be up to the same number of non-resident records as the limit of all resident ones).
//
// This is the lifecycle of records, summarized:
//
// Each record starts as a *(resident) cold one*. hand_cold may turn it into a hot one, a
// non-resident one or remove it altogether, based on their 'referenced' and 'test' status.
//
// A *hot record* may only change state to a cold one, when hand_hot reaches it unreferenced.
//
// A *non-resident cold record* may be removed fully by either hand_test or hand_hot. It its key
// gets reaccessed (reinserted), it turns straight into a hot record.

use std::collections::HashMap;
use std::hash::Hash;
use std::ptr;

// A Node of a circular DLL, which shall hold a record in our cache structure
struct Node<K, V> {
    prev: *const Node<K, V>,
    next: *const Node<K, V>,
    key: K,
    // The record may be non-resident, in which case it is null
    val: *const V,
    // Flags by lsb index:
    // 0: hot
    // 1: referenced (when a record gets reaccessed)
    // 2: test (the record is in its test period - only relevant for cold records)
    flags: u8,
}

pub struct CLOCKProCache<K: Clone + Eq + Hash, V> {
    capacity: usize,
    // The 'desired' state is having `cold_capacity` resident cold records and
    // `capacity - cold_capacity` hot ones, but only `capacity` is a hard limit
    // (for the number of resident records)
    cold_capacity: usize,
    // The hash map is to search for our records in the CDLL in constant time
    map: HashMap<K, *const Node<K, V>>,
    hot_count: usize,
    resident_cold_count: usize,
    nonresident_cold_count: usize,
    // hand_cold is only null when the cache is empty
    hand_cold: *const Node<K, V>,
    hand_hot: *const Node<K, V>,
    hand_test: *const Node<K, V>,
}

impl<K, V> Node<K, V> {
    /// New instance of a cold record node with the given key-value pair
    fn new(key: K, value: V) -> Self {
        Self {
            prev: ptr::null(),
            next: ptr::null(),
            key,
            val: Box::into_raw(Box::new(value)),
            // Flags for cold record in its test period
            flags: 0b100,
        }
    }

    /// The first reaccess of a cold record in its test period causes
    /// cold_capacity to increase. This method determines if that's the case
    /// for this node (record).
    fn check_cold_reaccess(&self) -> bool {
        self.flags == 0b100
    }

    /// Has this record been referenced since the last modification?
    fn was_referenced(&self) -> bool {
        self.flags & 2 != 0
    }

    /// Set the reference bit for this record
    fn set_referenced(&mut self, referenced: bool) {
        if referenced {
            self.flags |= 2;
        } else {
            self.flags &= 0b101;
        }
    }

    /// Change the record type to hot or cold
    fn set_hot(&mut self, hot: bool) {
        if hot {
            // When changing a cold record into hot, the reference bit also
            // disapears (and the test period bit is irrelevant).
            self.flags = 1;
        } else {
            self.flags &= 0b110;
        }
    }

    // Is this node a hot record?
    fn is_hot(&self) -> bool {
        self.flags & 1 != 0
    }

    /// Does this node also hold the value for its key?
    fn is_resident(&self) -> bool {
        !self.val.is_null()
    }

    /// Is the record in its test period?
    fn is_test(&self) -> bool {
        self.flags & 4 != 0
    }

    /// Starts or finishes the test period for this node (ie. sets the test bit).
    fn set_test(&mut self, test: bool) {
        if test {
            self.flags |= 4;
        } else {
            self.flags &= 0b011;
        }
    }

    /// Inserts this node behind the one at given pointer
    unsafe fn insert_behind(&mut self, node_ptr: *mut Self) {
        self.prev = (*node_ptr).prev;
        self.next = node_ptr;
        (*(node_ptr as *mut Node<K, V>)).prev = self;
        (*(self.prev as *mut Node<K, V>)).next = self;
    }

    /// Removes the node from a circular linked list (of size at least 2) by
    /// linking the previous and next node together
    fn remove(&self) {
        let mut_prev = self.prev as *mut Node<K, V>;
        let mut_next = self.next as *mut Node<K, V>;
        unsafe {
            (*mut_prev).next = self.next;
            (*mut_next).prev = self.prev;
        }
    }
}

impl<K: Clone + Eq + Hash, V> CLOCKProCache<K, V> {
    /// Create a new CLOCK-Pro cache data structure instance.
    /// Besides the `capacity` number of key-value pairs stored in this data
    /// structure, there may also be up to another `capacity` of record only
    /// containing the key. You may want to consider this when chosing the
    /// `capacity`, especially if the keys are of similar size as the values.
    ///
    /// *Note that the `capacity` needs to be at least 4 for the structure to
    /// function properly.*
    pub fn new(capacity: usize) -> Self {
        Self {
            capacity,
            cold_capacity: capacity - 2,
            // There may be up to two times the capacity of records.
            // (then, half the records are non-resident)
            map: HashMap::with_capacity(2 * capacity),
            hot_count: 0,
            resident_cold_count: 0,
            nonresident_cold_count: 0,
            hand_cold: ptr::null(),
            hand_hot: ptr::null(),
            hand_test: ptr::null(),
        }
    }

    /// Returns a reference to the value for given key, if it is cached.
    pub fn get<'a>(&'a mut self, key: &K) -> Option<&'a V> {
        self.get_value_ptr(key).map(|val_ptr| unsafe { &*val_ptr })
    }

    /// Returns a mutable reference to the value for given key, if it is cached.
    pub fn get_mut<'a>(&'a mut self, key: &K) -> Option<&'a mut V> {
        self.get_value_ptr(key)
            .map(|val_ptr| unsafe { &mut *(val_ptr as *mut V) })
    }

    /// A generic function that tries retrieving the ptr in which we store the
    /// value for received key (also performing a cache hit in case it's
    /// present).
    fn get_value_ptr(&mut self, key: &K) -> Option<*const V> {
        if let Some(node_ptr) = self.map.get(key) {
            let node_mut = unsafe { &mut *(*node_ptr as *mut Node<K, V>) };
            // The first reaccess makes cold_capacity increase
            if node_mut.check_cold_reaccess() {
                self.increment_cold_capacity();
            }
            // On reaccess, we only mark the record as referenced
            node_mut.set_referenced(true);
            if node_mut.val.is_null() {
                // Non-resident record
                None
            } else {
                // Resident record
                Some(node_mut.val)
            }
        } else {
            // No record for given key
            None
        }
    }

    /// Submit this key-value pair for caching.
    /// The key must not be present in the cache yet!
    pub fn insert(&mut self, key: K, value: V) {
        // If the key is present in a non-resident record, we reinsert it as a
        // hot record.
        let record = if let Some(nonresident_ptr) = self.map.get(&key) {
            let node = unsafe { &mut *(*nonresident_ptr as *mut Node<K, V>) };
            debug_assert!(!node.is_hot());
            debug_assert!(!node.is_resident());
            // If moving this record would also move hand_test, just move it
            // forward by one
            if self.hand_test == node {
                self.hand_test = node.next;
            }
            self.nonresident_cold_count -= 1;
            node.remove();
            Some(node)
        } else {
            None
        };

        if self.resident_cold_count + self.hot_count >= self.capacity {
            // Free a value
            self.trigger_hand_cold();
        }

        // Now either insert a new record, or reinsert the found one as hot
        if let Some(node) = record {
            node.val = Box::into_raw(Box::new(value));
            self.reinsert_as_hot(node);
            self.hot_count += 1;
        } else {
            self.insert_new(key, value);
            self.resident_cold_count += 1;
        }
    }

    /// Inserts a completely new record as a resident cold one.
    fn insert_new(&mut self, key: K, value: V) {
        let new_node = Box::into_raw(Box::new(Node::new(key.clone(), value)));
        if !self.hand_hot.is_null() {
            // Insert the record behind hand_hot
            unsafe {
                (*new_node).insert_behind(self.hand_hot as *mut _);
            }
        } else if !self.hand_cold.is_null() {
            // Insert the record behind hand_cold
            unsafe {
                (*new_node).insert_behind(self.hand_cold as *mut _);
            }
        } else {
            // Initiate the circular linked list with this one node
            unsafe {
                (*new_node).prev = new_node;
                (*new_node).next = new_node;
            }
            self.hand_cold = new_node;
        }
        self.map.insert(key, new_node);
    }

    /// Reinsert a node as a hot record.
    /// This only changes the node's status to hot and inserts it via hand_hot
    /// (which doesn't need to be initialized), but doesn't change any counters
    fn reinsert_as_hot(&mut self, record: &mut Node<K, V>) {
        // If the maximum number of hot records is already reached, decrease
        // the number by triggering hand_hot
        while self.hot_count >= self.capacity - self.cold_capacity {
            self.trigger_hand_hot();
        }

        record.set_hot(true);
        // If possible, insert the record behind hand_hot, otherwise make it
        // the new hand_hot
        if !self.hand_hot.is_null() {
            unsafe {
                record.insert_behind(self.hand_hot as *mut _);
            }
        } else {
            unsafe {
                record.insert_behind(self.hand_cold as *mut _);
            }
            self.hand_hot = record;
        }
    }

    /// The main purpose of this method is to evict a value from a resident
    /// cold record to be able to insert a new key-value pair.
    ///
    /// **We modify (only) cold records that we encounter with `hand_cold` in
    /// the following ways:**
    /// * A referenced record in its test period turns into a hot record
    /// * A non-referenced one in its test period loses its value
    /// * A referenced one outside test period loses the referenced bit, but
    ///   stays and keeps its value for another test period
    /// * One that is neither referenced nor in its test period gets evicted
    ///   altogether.
    ///
    /// The method ends when a value is evicted (either by evicting a record
    /// altogether or by removing its value).
    /// Finally, this method leaves hand_cold on a resident cold record node.
    fn trigger_hand_cold(&mut self) {
        // This bool will let us know if we have evicted a value, or need to
        // call the method again.
        let mut evicted = false;
        // Prepare a mutable reference to the record the hand points to, for
        // convenience
        let hand = unsafe { &mut *(self.hand_cold as *mut Node<K, V>) };
        debug_assert!(!hand.is_hot());
        debug_assert!(hand.is_resident());
        if hand.is_test() {
            if hand.was_referenced() {
                // Record turns into a hot one
                self.move_hand_cold_forward();
                self.resident_cold_count -= 1;
                hand.remove();
                self.reinsert_as_hot(hand);
                self.hot_count += 1;
            } else {
                // Remove the value, keep the record as a non-resident cold one.
                // If the total number of non-resident records were to thus
                // exceed the limit, remove one:
                if self.nonresident_cold_count >= self.capacity {
                    self.trigger_hand_test();
                }
                hand.val = ptr::null();
                self.resident_cold_count -= 1;
                self.nonresident_cold_count += 1;
                evicted = true;
                self.move_hand_cold_forward();
            }
        } else {
            if hand.was_referenced() {
                // Initiate new test period
                hand.set_referenced(false);
                hand.set_test(true);
                self.move_hand_cold_forward();
            } else {
                // Remove the record altogether:
                // If this would invalidate `hand_test`, move it forward.
                if self.hand_test == self.hand_cold {
                    self.hand_test = hand.next;
                }
                self.move_hand_cold_forward();
                self.map.remove(&hand.key);
                // Removal from the linked list
                hand.remove();
                // free
                unsafe {
                    Box::from_raw(hand);
                }
                self.resident_cold_count -= 1;
                evicted = true;
            }
        }
        if !evicted {
            // We haven't evicted a value yet, run again.
            self.trigger_hand_cold();
        }
    }

    /// Moves `hand_cold` forward to the nearest resident cold record
    fn move_hand_cold_forward(&mut self) {
        unsafe {
            loop {
                self.hand_cold = (*self.hand_cold).next;
                if !(*self.hand_cold).is_hot() && (*self.hand_cold).is_resident() {
                    break;
                }
            }
        }
    }

    /// This method is useful when there are too many hot records and one needs
    /// to be turned back into a cold one. When that happens, it needs to be
    /// called in a loop until the number decreases (one iteration doesn't
    /// guarantee the number of hots to decrease).
    /// We move `hand_hot` and modify the nodes we encounter, with hot records,
    /// we unset their reference bits and change those without the bit set into
    /// cold records.
    /// As the cited CLOCK-Pro paper suggest, we also act as hand_test on cold
    /// records along the way.
    /// Finally, the method always leaves hand_hot on a hot record.
    fn trigger_hand_hot(&mut self) {
        // Prepare a mutable reference to the record the hand points to, for
        // convenience
        let hand_hot = unsafe { &mut *(self.hand_hot as *mut Node<K, V>) };
        debug_assert!(hand_hot.is_hot());
        debug_assert!(hand_hot.is_resident());
        if hand_hot.was_referenced() {
            // Unset the reference bit
            hand_hot.set_referenced(false);
        } else {
            // Reference bit is unset; turn this record into a cold one
            hand_hot.set_hot(false);
            hand_hot.set_test(true);
            self.hot_count -= 1;
            self.resident_cold_count += 1;
        }
        debug_assert!(self.hot_count >= 1);
        // Move the hand forward until reaching another hot page.
        // Also act like `hand_test` on cold records.
        unsafe {
            self.hand_hot = (*self.hand_hot).next;
            while !(*self.hand_hot).is_hot() {
                // hand_test behavior:
                let hand = &mut *(self.hand_hot as *mut Node<K, V>);
                if hand.is_resident() {
                    // Resident cold record. End its test period and move on to the
                    // next node.
                    // Additionally, if a cold page passes its test period without
                    // a reaccess, `cold_capacity` decreases.
                    if hand.is_test() {
                        if !hand.was_referenced() {
                            self.decrement_cold_capacity();
                        }
                        hand.set_test(false);
                    }
                    self.hand_hot = hand.next;
                } else {
                    // If hand_test would get invalidated, move it forward
                    if self.hand_test == self.hand_hot {
                        self.hand_test = hand.next;
                    }
                    // Remove the non-resident cold record:
                    self.hand_hot = hand.next;
                    self.nonresident_cold_count -= 1;
                    // Remove from linked list
                    hand.remove();
                    // Remove from hash map
                    self.map.remove(&hand.key);
                    // free
                    Box::from_raw(hand);
                }
            }
        }
    }

    /// Moving `hand_test`, this removes the first non-resident cold record it
    /// finds, ending test periods of cold records along the way.
    /// It leaves `hand_test` on any type of record that's in line.
    fn trigger_hand_test(&mut self) {
        // If hand_test is uninitiated, initiate it:
        if self.hand_test.is_null() {
            self.hand_test = unsafe { (*self.hand_cold).next };
        }
        // Prepare a mutable reference to the record the hand points to, for
        // convenience
        let hand = unsafe { &mut *(self.hand_test as *mut Node<K, V>) };

        if hand.is_hot() {
            // We skip hot records
            self.hand_test = hand.next;
            self.trigger_hand_test();
        } else {
            if hand.is_resident() {
                // Resident cold record. End its test period and move on to the
                // next node.
                // Additionally, if a cold page passes its test period without
                // a reaccess, `cold_capacity` decreases.
                if hand.is_test() {
                    if !hand.was_referenced() {
                        self.decrement_cold_capacity();
                    }
                    hand.set_test(false);
                }
                self.hand_test = hand.next;
                self.trigger_hand_test();
            } else {
                // Non-resident cold node.
                // Remove it and move hand_test forward.
                self.hand_test = hand.next;
                self.nonresident_cold_count -= 1;
                // Remove from linked list
                hand.remove();
                // Remove from hash map
                self.map.remove(&hand.key);
                unsafe {
                    // free
                    Box::from_raw(hand);
                }
            }
        }
    }

    /// When a cold record in its test period is first reaccessed, the capacity
    /// of cold records increases
    fn increment_cold_capacity(&mut self) {
        if self.cold_capacity < self.capacity - 2 {
            self.cold_capacity += 1;
            // If this results in there being too many hot records, solve this
            // by turning enough of them (one, presumably) back into a cold one
            while self.hot_count > self.capacity - self.cold_capacity {
                self.trigger_hand_hot();
            }
        }
    }

    /// When a cold record passes its test period without being reaccessed, the
    /// capacity of cold records decreases (in favor of hot records)
    fn decrement_cold_capacity(&mut self) {
        if self.cold_capacity > 2 {
            self.cold_capacity -= 1;
        }
    }
}

impl<K, V> Drop for Node<K, V> {
    fn drop(&mut self) {
        unsafe {
            Box::from_raw(self.val as *mut V);
        }
    }
}

impl<K: Clone + Eq + Hash, V> Drop for CLOCKProCache<K, V> {
    fn drop(&mut self) {
        if !self.hand_cold.is_null() {
            let mut current_ptr =
                unsafe { (*Box::from_raw(self.hand_cold as *mut Node<K, V>)).next };
            while current_ptr != self.hand_cold {
                current_ptr = unsafe { (*Box::from_raw(current_ptr as *mut Node<K, V>)).next };
            }
        }
    }
}

#[cfg(test)]
mod test {
    use super::{CLOCKProCache, Node};
    use rand::{thread_rng, Rng};
    use std::fmt::{Debug, Display};
    use std::hash::Hash;

    #[test]
    fn simple() {
        // A simple test of the cache's semantics
        let mut cache = CLOCKProCache::new(6);
        for i in 0..6 {
            cache.insert(i, 2 * i);
        }
        assert_eq!(cache.get(&0), Some(&0));
        assert_eq!(cache.get(&4), Some(&8));
        assert_eq!(cache.get(&2), Some(&4));
        cache.insert(6, 12);
        check_clock_content(
            &cache,
            vec![
                (2, false, true),
                (3, false, true),
                (4, false, true),
                (5, false, true),
                (6, false, true),
                (0, true, true),
                (1, false, false),
            ],
        );
        cache.insert(7, 14);
        assert_eq!(cache.get(&0), Some(&0));
        check_clock_content(
            &cache,
            vec![
                (4, false, true),
                (5, false, true),
                (6, false, true),
                (2, true, true),
                (7, false, true),
                (0, true, true),
                (1, false, false),
                (3, false, false),
            ],
        );
        cache.insert(8, 16);
        assert_eq!(cache.get(&7), Some(&14));
        check_clock_content(
            &cache,
            vec![
                (6, false, true),
                (4, true, true),
                (8, false, true),
                (2, true, true),
                (7, false, true),
                (0, true, true),
            ],
        );

        // Insert enough records to have the full capacity of 6 non-resident records:
        // Even trigger hand_test and make one disappear
        cache.insert(9, 18);
        cache.insert(10, 20);
        cache.insert(11, 22);
        check_clock_content(
            &cache,
            vec![
                (10, false, true),
                (11, false, true),
                (2, true, true),
                (7, false, true),
                (0, true, true),
                (4, true, true),
                (8, false, false),
                (9, false, false),
            ],
        );
        cache.insert(12, 24);
        cache.insert(13, 26);
        cache.insert(14, 28);
        cache.insert(15, 30);
        cache.insert(16, 32);
        check_clock_content(
            &cache,
            vec![
                (15, false, true),
                (16, false, true),
                (2, true, true),
                (7, false, true),
                (0, true, true),
                (4, true, true),
                (9, false, false),
                (10, false, false),
                (11, false, false),
                (12, false, false),
                (13, false, false),
                (14, false, false),
            ],
        );

        // Now there is the full capacity of non-resident cold records
        // Reinsert such record (it turns straight into a hot one)
        // (just first reaccess some cold elements - also increasing
        // cold_capacity from 3 back to 4)
        assert_eq!(cache.get(&16), Some(&32));
        assert_eq!(cache.get(&15), Some(&30));
        assert_eq!(cache.get(&10), None);
        cache.insert(10, 20);

        check_clock_content(
            &cache,
            vec![
                (7, false, true),
                (0, false, true),
                (10, true, true),
                (16, true, true),
                (4, false, true),
                (15, false, true),
            ],
        );
    }

    #[test]
    fn get_mut_simple() {
        // A basic test to check if get_mut works how one would expect
        let mut cache = CLOCKProCache::new(6);
        for i in 0..6 {
            cache.insert(i, 2 * i);
        }
        let elem = cache.get_mut(&0).unwrap();
        assert_eq!(*elem, 0);
        *elem = 50;
        assert_eq!(cache.get(&4), Some(&8));
        *cache.get_mut(&2).unwrap() = 100;
        cache.insert(6, 12);
        check_clock_content(
            &cache,
            vec![
                (2, false, true),
                (3, false, true),
                (4, false, true),
                (5, false, true),
                (6, false, true),
                (0, true, true),
                (1, false, false),
            ],
        );
        cache.insert(7, 14);
        assert_eq!(cache.get(&0), Some(&50));
        check_clock_content(
            &cache,
            vec![
                (4, false, true),
                (5, false, true),
                (6, false, true),
                (2, true, true),
                (7, false, true),
                (0, true, true),
                (1, false, false),
                (3, false, false),
            ],
        );
        assert_eq!(cache.get(&2), Some(&100));
    }

    /// Checks that the constents of the cache's linked list are what we expect.
    /// The given `expect` vector gives tuples of the expected values for
    /// * The key in the record
    /// * The hot bit status
    /// * The record being resident
    /// in the order they appear starting from `hand_cold` and moving forward
    /// through the circular linked list until the record behind `hand_cold`
    /// again.
    fn check_clock_content<K>(cache: &CLOCKProCache<K, K>, expect: Vec<(K, bool, bool)>)
    where
        K: Clone + Eq + Hash + Debug + Display,
    {
        let mut current = unsafe { &*cache.hand_cold };
        let mut expect_hot_count = 0;
        let mut expect_resident_cold_count = 0;
        let mut expect_nonresident_cold_count = 0;
        let mut init = false;
        for (exp_key, exp_hot, exp_resident) in expect {
            if init {
                // Make sure we didn't cycle back to the first record
                assert!(current as *const Node<K, K> != cache.hand_cold);
            } else {
                init = true;
            }
            // We also count the numbers of expected records of certain counts
            // to ensure they are also correctly stored int the structure's
            // counters
            if exp_hot {
                expect_hot_count += 1;
            } else {
                if exp_resident {
                    expect_resident_cold_count += 1;
                } else {
                    expect_nonresident_cold_count += 1;
                }
            }
            // Now check compared records on equality.
            assert_eq!(current.key, exp_key);
            assert_eq!(current.is_hot(), exp_hot);
            assert_eq!(current.is_resident(), exp_resident);
            // Move forward in the list:
            current = unsafe { &*current.next };
        }
        // We must have circled back to `hand_cold`
        assert_eq!(current as *const Node<K, K>, cache.hand_cold);
        assert_eq!(cache.hot_count, expect_hot_count);
        assert_eq!(cache.resident_cold_count, expect_resident_cold_count);
        assert_eq!(cache.nonresident_cold_count, expect_nonresident_cold_count);
    }

    #[test]
    fn smoke_test() {
        // Doesn't test the cache semantics, only makes sure the cache always
        // returns the correct number of elements.
        let mut rng = thread_rng();
        let mut cache = CLOCKProCache::new(25);
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
