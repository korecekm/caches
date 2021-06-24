use crate::trie_hashmap::{TMReadTxn, TMWriteTxn, TrieMap};
use std::hash::Hash;
use std::collections::hash_map::HashMap as StdMap;
use std::cell::Cell;
use std::ptr;
use std::mem;

// A transactional CLOCK-Pro cache that gives read transactions no way of
// modifying the cache's content. Write transactions store all the CLOCK-Pro
// logic in a special (sequential) logic struct, that only stores information
// about keys, not values.
// Values are stored separately in a transactional hash map (TrieMap). The
// cache logic is separate from this hash map.
// This makes write transaction rollbacks expensive, because such roll back
// also rolls back the changes to the transactional hash map, but has no way
// of rolling back the logic struct.
// If one write txn. rolls back and the cache is asked for another write txn,
// we resolve this situation by giving the new txn a very simple approximation
// of the logic - in fact, we just iterate through all keys in the hash map and
// insert them to a new logic struct as resident cold records (this essentially
// means putting all the keys into the logic struct in random order, because
// the iteration order is decided by the keys' hashes).
// An argument for why rollbacks may be expensive is that they aren't expected
// to be useful in the context of caches and should be rare for most use cases.

// The CLOCK-Pro logic itself is not described here, for more information, see
// the standard CLOCK-Pro implementation (file `clock_pro.rs`).

/// # CLOCK-Pro Transactional
/// 
/// A concurrently readably, transactional key-value cache
/// (using CLOCK-Pro eviction logic).
/// 
/// `CLOCKProTransactional` itself works only as an immutable handle.
/// Modifications to the cache need to be done via `CLOCKProWriteTxn` write
/// transactions, obtained from the handle by the `write` method, and they are
/// only recorded globally once the transactions are committed (only a single
/// write transaction is allowed at one time).
/// 
/// The `read` method on the `CLOCKProTransactional` handle allows generation
/// of an arbitrary number of `LRUReadTxn` read transactions. Those merely give
/// a snapshot to the current cached set, ie. to the values that are cached at
/// the moment of the transaction's creation. Accesses to these transactions
/// don't modify the cache in any way.
/// 
/// As stated, write transactions need to get committed (using their `commit`
/// method) to take effect globally. Their progress may also be rolled back
/// (forgotten) simply by having the transaction handle dropped, although
/// this is discouraged, as the next write transaction's creation may be
/// expensive.
/// 
/// ## Example usage
/// We will show an example usage of a write transaction:
/// ```
/// // We will call the globall cache handle simply 'cache'
/// let cache = CLOCKProTransactional::new(32000);
/// 
/// // ... let's imagine the cache is supplied with records here by another
/// // write transaction, which is now committed ...
/// 
/// // Acquire a write transaction:
/// let mut cache_write = cache.write();
/// // a write transaction may also be created with try_write(), which returns
/// // None if another write txn is already active. write() alone waits for the
/// // active txn to finish.
/// 
/// // A cached value is successfully retrieved.
/// // Unlike read transactions, write txn's get function modifies the cache
/// // internally, giving the accessed element higher priority in being kept.
/// assert!(write.get(&X).is_some());
/// 
/// // Another value isn't recorded and we wish to submit it for caching:
/// assert!(write.get(&Y).is_none());
/// write.insert(Y, Y_value);
/// 
/// write.commit();
/// // Now, the modifications will be visible to new transactions.
/// // If the `write` handle was dropped, they would get rolled back.
/// ```
pub struct CLOCKProTransactional<K: Clone + Eq + Hash, V: Clone> {
    capacity: usize,
    map:TrieMap<K, V>,
    // the logic fields are only accessed if a write txn for the map was
    // successfully received, ie. the map itself protects the struct against
    // concurrent rewrites.
    logic_valid: Cell<bool>,
    logic: Cell<*mut CLOCKProLogic<K>>,
}

pub struct CLOCKProReadTxn<K: Clone + Eq + Hash, V: Clone> {
    map: TMReadTxn<K, V>,
}

pub struct CLOCKProWriteTxn<'a, K: Clone + Eq + Hash, V: Clone> {
    // The only reason the map is in an Option is so that it can be later taken
    // for commit. It will stay Some(txn) for the whole time though.
    map: Option<TMWriteTxn<'a, K, V>>,
    logic_valid: &'a Cell<bool>,
    logic: *mut CLOCKProLogic<K>,
}

// A Node of a circular DLL, which shall hold a record in our cache replacement
// logic structure.
struct Node<K> {
    prev: *const Node<K>,
    next: *const Node<K>,
    key: K,
    // Flags by lsb index:
    // 0: hot
    // 1: referenced (when a record gets reaccessed)
    // 2: test (the record is in its test period - only relevant for cold records)
    // 3: resident (whether the record is also present in our hash map)
    //    (the logic needs to know this separately, as it is separated from the hash map)
    flags: u8,
}

struct CLOCKProLogic<K: Clone + Eq + Hash> {
    capacity: usize,
    cold_capacity: usize,
    map: StdMap<K, *const Node<K>>,
    hot_count: usize,
    resident_cold_count: usize,
    nonresident_cold_count: usize,
    // hand_cold is only null when the cache is empty
    hand_cold: *const Node<K>,
    hand_hot: *const Node<K>,
    hand_test: *const Node<K>,
}

unsafe impl<K: Clone + Eq + Hash, V: Clone> Send for CLOCKProTransactional<K, V> {}
unsafe impl<K: Clone + Eq + Hash, V: Clone> Sync for CLOCKProTransactional<K, V> {}

impl<K: Clone + Eq + Hash, V: Clone> CLOCKProTransactional<K, V> {
    /// Create a new transactional CLOCK-Pro cache with the given capacity.
    /// * Note that the capacity needs to be at least 4 *
    /// You may want to consider, that the transactional cache may require
    /// quite a significant space overhead. As for the data structure itself,
    /// that only adds an amount of pointers linear to the number of records,
    /// but remember that all the read transactions make the values cached at
    /// the time of the txn's creation, so if you plan on having many read
    /// transactions holding different versions of the cache, all the values
    /// they hold will need to be kept in memory.
    pub fn new(capacity: usize) -> Self {
        Self{
            capacity,
            map: TrieMap::new(),
            logic_valid: Cell::new(true),
            logic: Cell::new(Box::into_raw(Box::new(CLOCKProLogic::new(capacity)))),
        }
    }

    /// If a write transaction rolls back, it invalidates the cache's logic
    /// data structure. After that, if another write transaction is to be
    /// acquired, we need to recover the logic structure in some way.
    fn recover_logic(&self) {
        let mut map = StdMap::with_capacity(2 * self.capacity);
        let mut hand_cold: *const Node<K> = ptr::null();
        let mut key_count = 0;
        // We will simply get all the values inside our hash map, and pretend
        // they are all (resident) cold records
        for key in self.map.read().iter_keys() {
            key_count += 1;
            let node = Box::into_raw(Box::new(Node::new(key.clone())));
            map.insert(key.clone(), node as *const Node<K>);
            if hand_cold.is_null() {
                unsafe {
                    (*node).prev = node;
                    (*node).next = node;
                }
                hand_cold = node;
            } else {
                unsafe {
                    (*node).insert_behind(hand_cold as *mut Node<K>);
                }
            }
        }
        self.logic.set(Box::into_raw(Box::new(
            CLOCKProLogic {
                capacity: self.capacity,
                cold_capacity: self.capacity - 2,
                map,
                hot_count: 0,
                resident_cold_count: key_count,
                nonresident_cold_count: 0,
                hand_cold,
                hand_hot: ptr::null(),
                hand_test: ptr::null(),
            }
        )));
    }

    /// Acquire a read transaction to this cache
    pub fn read(&self) -> CLOCKProReadTxn<K, V> {
        CLOCKProReadTxn {
            map: self.map.read(),
        }
    }

    /// Acquire a write transaction to this cache
    pub fn write<'a>(&'a self) -> CLOCKProWriteTxn<'a, K, V> {
        self.prepare_write_txn(self.map.write())
    }

    /// If there's no other write transaction accessing this cache, the
    /// function returns Some(write transaction), otherwise, it returns None.
    pub fn try_write<'a>(&'a self) -> Option<CLOCKProWriteTxn<'a, K, V>> {
        let write_attempt = self.map.try_write();
        write_attempt.map(|txn| self.prepare_write_txn(txn))
    }

    /// Once a write transaction to the (trie) map has been acquired, this
    /// function prepares the write transaction for our cache.
    fn prepare_write_txn<'a>(&'a self, map_write: TMWriteTxn<'a, K, V>) -> CLOCKProWriteTxn<'a, K, V> {
        if !self.logic_valid.get() {
            // A previous write transaction was rolled back, invalidating the
            // logic structure.
            self.recover_logic();
        }
        self.logic_valid.set(false);
        CLOCKProWriteTxn {
            map: Some(map_write),
            logic_valid: &self.logic_valid,
            logic: self.logic.get(),
        }
    }
}

impl<K: Clone + Eq + Hash, V: Clone> CLOCKProReadTxn<K, V> {
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

impl<K: Clone + Eq + Hash, V: Clone> CLOCKProWriteTxn<'_, K, V> {
    /// Commit the transaction. This consumes the struct.
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
        unsafe {
            (*self.logic).hit(key);
        }
        self.map.as_ref().unwrap().search(key)
    }

    /// Submit this key-value pair for caching.
    /// Only call this if the record isn't already present in the cache.
    pub fn insert(&mut self, key: K, value: V) {
        // The logic DS may indicate that we need to evict a value
        if let Some(remove_key) = unsafe { (*self.logic).submit(key.clone()) } {
            self.map.as_mut().unwrap().remove(&remove_key);
        }
        self.map.as_mut().unwrap().update(key, value);
    }

    /// This function enables modifications to the present values.
    /// Only call this if the record *is* already present in the cache.
    pub fn reinsert(&mut self, key: K, value: V) {
        unsafe {
            (*self.logic).hit(&key)
        }
        self.map.as_mut().unwrap().update(key, value);
    }
}

impl<K> Node<K> {
    /// New instance of a cold record node with the given key
    fn new(key: K) -> Self {
        Self {
            prev: ptr::null(),
            next: ptr::null(),
            key,
            // Flags for a resident cold record in its test period
            flags: 0b1100,
        }
    }

    /// The first reaccess of a cold record in its test period causes
    /// cold_capacity to increase. This method determines if that's the case
    /// for this node (record).
    fn check_cold_reaccess(&self) -> bool {
        self.flags & 0b111 == 0b100
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
            self.flags &= 0b1101;
        }
    }

    /// Change the record type to hot or cold
    fn set_hot(&mut self, hot: bool) {
        if hot {
            // When changing a cold record into hot, the reference bit also
            // disapears (and the test period bit is irrelevant).
            self.flags &= 0b1001;
            self.flags |= 1;
        } else {
            self.flags &= 0b1110;
        }
    }

    /// Is this node a hot record?
    fn is_hot(&self) -> bool {
        self.flags & 1 != 0
    }

    /// Does this node also hold the value for its key (in the separate hash map)?
    /// The logic data structure needs to keep this information itself.
    fn is_resident(&self) -> bool {
        self.flags & 0b1000 != 0
    }

    /// Set or unset our helper bit that says if the value is also present in
    /// the value hash map.
    fn set_resident(&mut self, resident: bool) {
        if resident {
            self.flags |= 8;
        } else {
            self.flags &= 0b0111;
        }
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
            self.flags &= 0b1011;
        }
    }

    /// Inserts this node behind the one at given pointer
    unsafe fn insert_behind(&mut self, node_ptr: *mut Self) {
        self.prev = (*node_ptr).prev;
        self.next = node_ptr;
        (*(node_ptr as *mut Node<K>)).prev = self;
        (*(self.prev as *mut Node<K>)).next = self;
    }

    /// Removes the node from a circular linked list (of size at least 2) by
    /// linking the previous and next node together
    fn remove(&self) {
        let mut_prev = self.prev as *mut Node<K>;
        let mut_next = self.next as *mut Node<K>;
        unsafe {
            (*mut_prev).next = self.next;
            (*mut_next).prev = self.prev;
        }
    }
}

impl<K: Clone + Eq + Hash> CLOCKProLogic<K> {
    /// Initiate an empty CLOCK-Pro logic data structure
    /// Besides the `capacity` number of key-value pairs stored in this data
    /// structure, there may also be up to another `capacity` of record only
    /// containing the key. You may want to consider this when chosing the
    /// `capacity`, especially if the keys are of similar size as the values.
    ///
    /// *Note that the `capacity` needs to be at least 4 for the structure to
    /// function properly.*
    fn new(capacity: usize) -> Self {
        Self {
            capacity,
            cold_capacity: capacity - 2,
            // There may be up to two times the capacity of records.
            // (in case the whole half is non-resident)
            map: StdMap::with_capacity(2 * capacity),
            hot_count: 0,
            resident_cold_count: 0,
            nonresident_cold_count: 0,
            hand_cold: ptr::null(),
            hand_hot: ptr::null(),
            hand_test: ptr::null(),
        }
    }

    /// Submit a *new* (not already present) key for caching.
    /// If a value for another key needs to be removed, the key gets returned.
    fn submit(&mut self, key: K) -> Option<K> {
        // If the key is present in a non-resident record, we reinsert it as a
        // hot record.
        let record = if let Some(nonresident_ptr) = self.map.get(&key) {
            let node = unsafe {
                &mut *(*nonresident_ptr as *mut Node<K>)
            };
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

        let mut eviction_key = None;
        if self.resident_cold_count + self.hot_count >= self.capacity {
            // Capacity reached. Decide on a value to free.
            eviction_key = Some(self.trigger_hand_cold());
        }

        // Now either insert a new record, or reinsert the found one as hot
        if let Some(node) = record {
            node.set_resident(true);
            self.reinsert_as_hot(node);
            self.hot_count += 1;
        } else {
            self.insert_new(key);
            self.resident_cold_count += 1;
        }

        eviction_key
    }

    /// Update the CLOCK-Pro state on a reaccess.
    fn hit(&mut self, key: &K) {
        if let Some(node_ptr) = self.map.get(key) {
            let node_mut = unsafe {
                &mut *(*node_ptr as *mut Node<K>)
            };
            // The first reaccess makes cold_capacity increase
            if node_mut.check_cold_reaccess() {
                self.increment_cold_capacity();
            }
            // On reaccess, we only mark the record as referenced
            node_mut.set_referenced(true);
        }
    }

    /// Inserts a completely new record as a resident cold one.
    fn insert_new(&mut self, key: K) {
        let new_node = Box::into_raw(Box::new(Node::new(key.clone())));
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
    /// (which doesn't need to be initiated), but doesn't change any counters
    fn reinsert_as_hot(&mut self, record: &mut Node<K>) {
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
    /// cold record to be able to insert a new one.
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
    /// The method ends when a value for eviction has been chosen.
    /// Finally, this method leaves hand_cold on a resident cold record node
    /// and returns the key who's value shall be evicted from the hash map.
    fn trigger_hand_cold(&mut self) -> K {
        // A key for eviction won't necessarily be chosen in this call already.
        // If it isn't, we need to call the function again.
        let mut evict_key = None;
        // Prepare a mutable reference to the record the hand points to, for
        // convenience.
        let hand = unsafe {
            &mut *(self.hand_cold as *mut Node<K>)
        };
        debug_assert!(!hand.is_hot());
        debug_assert!(hand.is_resident());
        if hand.is_test() {
            if hand.was_referenced() {
                // Record turns into a hot one.
                self.move_hand_cold_forward();
                self.resident_cold_count -= 1;
                hand.remove();
                self.reinsert_as_hot(hand);
                self.hot_count += 1;
            } else {
                // Remove the value, keep the record as a non-resident cold one.
                // If the total number of non-resident records were to thus exceed
                // the limit, trigger hand_test to remove one.
                if self.nonresident_cold_count >= self.capacity {
                    self.trigger_hand_test();
                }
                hand.set_resident(false);
                evict_key = Some(hand.key.clone());
                self.resident_cold_count -= 1;
                self.nonresident_cold_count += 1;
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
                // Remove from linked list
                hand.remove();
                // Free node and set the evict_key
                evict_key = unsafe {
                    Some((*Box::from_raw(hand)).key)
                };
                self.resident_cold_count -= 1;
            }
        }

        // Did we chose a key to evict, or do we have to call this function
        // again?
        match evict_key {
            None => self.trigger_hand_cold(),
            Some(key) => key,
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
        let hand_hot = unsafe { &mut *(self.hand_hot as *mut Node<K>) };
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
                let hand = &mut *(self.hand_hot as *mut Node<K>);
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
        let hand = unsafe { &mut *(self.hand_test as *mut Node<K>) };

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

// Drop implementations for our structs:

impl<K: Clone + Eq + Hash, V: Clone> Drop for CLOCKProTransactional<K, V> {
    fn drop(&mut self) {
        if self.logic_valid.get() {
            unsafe {
                Box::from_raw(self.logic.get());
            }
        }
    }
}

impl<'a, K: Clone + Eq + Hash, V: Clone> Drop for CLOCKProWriteTxn<'_, K, V> {
    fn drop(&mut self) {
        // Drop the whole logic data structure, because we must count with the
        // possibility that the cache has been modified, and therefore now
        // holds different data than what is recorded in 'logic'.
        if !self.logic_valid.get() {
            unsafe {
                Box::from_raw(self.logic);
            }
        }
    }
}

impl<K: Clone + Eq + Hash> Drop for CLOCKProLogic<K> {
    fn drop(&mut self) {
        if !self.hand_cold.is_null() {
            let mut current_ptr = unsafe {
                (*Box::from_raw(self.hand_cold as *mut Node<K>)).next
            };
            while current_ptr != self.hand_cold {
                current_ptr = unsafe {
                    (*Box::from_raw(current_ptr as *mut Node<K>)).next
                };
            }
        }
    }
}

#[cfg(test)]
mod test {
    use super::{CLOCKProTransactional, CLOCKProLogic, Node};
    use rand::{thread_rng, Rng};
    use std::fmt::{Debug, Display};
    use std::hash::Hash;

    #[test]
    fn simple() {
        // Checks the cache semantics with a 'simple' example use case.
        let cache = CLOCKProTransactional::new(6);
        let mut write = cache.write();
        for i in 0..6 {
            write.insert(i, 2 * i);
        }
        assert_eq!(write.get(&0), Some(&0));
        assert_eq!(write.get(&4), Some(&8));
        assert_eq!(write.get(&2), Some(&4));
        write.insert(6, 12);
        write.commit();
        check_clock_content(
            unsafe { &*cache.logic.get() },
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

        let mut write = cache.write();
        write.insert(7, 14);
        assert_eq!(write.get(&0), Some(&0));
        // check that a read transaction now only sees the old state ---
        let read = cache.read();
        assert_eq!(read.get(&3), Some(&6));
        assert_eq!(read.get(&5), Some(&10));
        assert_eq!(read.get(&1), None);
        assert_eq!(read.get(&7), None);
        // -------------------------------------------------------------
        write.commit();
        check_clock_content(
            unsafe { &*cache.logic.get() },
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

        let mut write = cache.write();
        write.insert(8, 16);
        assert_eq!(write.get(&7), Some(&14));
        write.commit();
        check_clock_content(
            unsafe { &*cache.logic.get() },
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
        let mut write = cache.write();
        write.insert(9, 18);
        write.insert(10, 20);
        write.insert(11, 22);
        write.commit();
        check_clock_content(
            unsafe { &*cache.logic.get() },
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
        let mut write = cache.write();
        write.insert(12, 24);
        write.insert(13, 26);
        write.insert(14, 28);
        write.insert(15, 30);
        write.insert(16, 32);
        write.commit();
        check_clock_content(
            unsafe { &*cache.logic.get() },
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
        let mut write = cache.write();
        assert_eq!(write.get(&16), Some(&32));
        assert_eq!(write.get(&15), Some(&30));
        assert_eq!(write.get(&10), None);
        write.insert(10, 20);
        write.commit();
        check_clock_content(
            unsafe { &*cache.logic.get() },
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

    /// Checks that the constents of the cache's linked list are what we expect.
    /// The given `expect` vector gives tuples of the expected values for
    /// * The key in the record
    /// * The hot bit status
    /// * The record being resident
    /// in the order they appear starting from `hand_cold` and moving forward
    /// through the circular linked list until the record behind `hand_cold`
    /// again.
    fn check_clock_content<K>(cache_logic: &CLOCKProLogic<K>, expect: Vec<(K, bool, bool)>)
    where
        K: Clone + Eq + Hash + Debug + Display,
    {
        let mut current = unsafe {
            &*cache_logic.hand_cold
        };
        let mut expect_hot_count = 0;
        let mut expect_resident_cold_count = 0;
        let mut expect_nonresident_cold_count = 0;
        let mut init = false;
        for (exp_key, exp_hot, exp_resident) in expect {
            if init {
                // Make sure we didn't cycle back to the first record
                assert!(current as *const Node<K> != cache_logic.hand_cold);
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
            current = unsafe {
                &*current.next
            };
        }
        // We must have circled back to `hand_cold`
        assert_eq!(current as *const Node<K>, cache_logic.hand_cold);
        assert_eq!(cache_logic.hot_count, expect_hot_count);
        assert_eq!(cache_logic.resident_cold_count, expect_resident_cold_count);
        assert_eq!(cache_logic.nonresident_cold_count, expect_nonresident_cold_count);
    }

    #[test]
    fn smoke_test() {
        // Without checking the cache semantics, this only makes sure the cache
        // always returns the correct number of elements.
        let mut rng = thread_rng();
        let cache = CLOCKProTransactional::new(25);
        let mut write = cache.write();
        // First, insert 25 elements to fill the cache
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
            // Every 300th iteration gets rolled back to also test logic recover.
            if iter % 300 != 0 {
                write.commit();
            }
        }
    }
}
