use crate::bpt_transactional::{KVMReadTxn, KVMWriteTxn, KVMap};
use ahash::AHasher;
use std::hash::Hash;
use std::hash::Hasher;

// A transactional key-value hash map implemented simply by generating a hash
// for a given key and using the transactional B+ tree to store it.
//
// The records inside the B+ tree are of two types (HMElement):
// * `One(K, V)`: when just a single record is present with the generated hash
// * `Vec(Vec<(K, V)>)`: once there is a second key with the same hash, a
//   vector is generated holding both (and potentially more) records.
//   This vector is not sorted in any way since we expect hash collisions to be
//   rare.

macro_rules! hash {
    ($k:expr) => {{
        let mut hasher = AHasher::new_with_keys(3, 7);
        $k.hash(&mut hasher);
        (hasher.finish())
    }};
}

#[derive(Clone)]
enum HMElement<K, V>
where
    K: Eq + Hash + Clone,
    V: Clone,
{
    One(K, V),
    Vec(Vec<(K, V)>),
}

/// A concurrently readable, transactional key-value hash map.
///
/// HashMap itself works only as an immutable handle. Modifications to the map
/// need to be done via HMWriteTxn write transactions and are only recorded
/// permanently once the transactions are commited (only one write transaction
/// is allowed at a time).
///
/// HMReadTxn read transactions provides snapshots to the current state of the
/// hash map, ie. they enable you to search through the records as they were at
/// the point of the transaction's creation.
///
/// the read and write transactions may be generated via the `read()` and
/// `write()` functions, respectively.
///
/// Currently, both the read and write txns provide this one read-only operation:
/// * search(&key): gives an (immutable) reference to the value corresponding to
///   this key
///
/// The write transaction also provides these modifying operations:
/// * `update(key, value)`: updates a value for given key, or inserts it into
///   the map if it isn't recorded already
/// * `remove(&key)`: removes given key's record inside the tree (or does
///   nothing it isn't recorded)
///
/// ## Example:
/// ```
/// let map = HashMap::new();
///
/// // create a HMWriteTxn handle to be able to modify the map
/// let mut write = map.write();
/// // only one write transaction can exist at a time
/// assert!(map.try_write().is_none());
///
/// // insert two records, update one and remove the other
/// write.update("first", 1);
/// write.update("second", 2);
/// write.update("second", 3);
/// write.remove(&"first");
///
/// // the write txn hasn't been committed yet, so a new read txn doesn't see
/// // the data yet
/// assert!(map.read().search(&"second").is_none());
///
/// // commit the transaction:
/// // (it is also possible to roll it back simply by having the transaction
/// // handle dropped)
/// write.commit();
/// // from now, a new write transaction may be created
///
/// // a new read transaction will now see the record made by the write txn:
/// let read = map.read();
/// assert_eq!(read.search(&"first"), None);
/// assert_eq!(read.search(&"second"), Some(&3));
/// ```
pub struct HashMap<K, V>
where
    K: Eq + Hash + Clone,
    V: Clone,
{
    tree: KVMap<u64, HMElement<K, V>>,
}

pub struct HMReadTxn<K, V>
where
    K: Eq + Hash + Clone,
    V: Clone,
{
    txn: KVMReadTxn<u64, HMElement<K, V>>,
}

pub struct HMWriteTxn<'a, K, V>
where
    K: Eq + Hash + Clone,
    V: Clone,
{
    txn: KVMWriteTxn<'a, u64, HMElement<K, V>>,
}

// IMPLEMENTATION:

impl<K, V> HashMap<K, V>
where
    K: Eq + Hash + Clone,
    V: Clone,
{
    /// Generate an empty HashMap handle.
    pub fn new() -> Self {
        Self { tree: KVMap::new() }
    }

    /// Generate a read transaction for the current map state.
    pub fn read(&self) -> HMReadTxn<K, V> {
        HMReadTxn {
            txn: self.tree.read(),
        }
    }

    /// Generate a write transaction enabling to modify the map.
    ///
    /// If another write transaction is still active, this will wait for it to
    /// get committed or rolled back.
    pub fn write(&self) -> HMWriteTxn<K, V> {
        HMWriteTxn {
            txn: self.tree.write(),
        }
    }

    /// Generates a write transaction enabling to modify the map, but only if
    /// there is no other write transaction currently active.
    pub fn try_write(&self) -> Option<HMWriteTxn<K, V>> {
        match self.tree.try_write() {
            None => None,
            Some(txn) => Some(HMWriteTxn { txn }),
        }
    }
}

impl<K, V> HMElement<K, V>
where
    K: Eq + Hash + Clone,
    V: Clone,
{
    fn search(&self, key: &K) -> Option<&V> {
        match self {
            Self::One(k, v) => {
                if k == key {
                    Some(&v)
                } else {
                    None
                }
            }
            Self::Vec(vec) => {
                for (k, v) in vec.iter() {
                    if k == key {
                        return Some(&v);
                    }
                }
                None
            }
        }
    }
}

impl<K, V> HMReadTxn<K, V>
where
    K: Eq + Hash + Clone,
    V: Clone,
{
    pub fn search(&self, key: &K) -> Option<&V> {
        match self.txn.search(&hash!(key)) {
            None => None,
            Some(elem) => elem.search(key),
        }
    }
}

impl<K, V> HMWriteTxn<'_, K, V>
where
    K: Eq + Hash + Clone,
    V: Clone,
{
    pub fn search(&self, key: &K) -> Option<&V> {
        match self.txn.search(&hash!(key)) {
            None => None,
            Some(elem) => elem.search(key),
        }
    }

    pub fn update(&mut self, key: K, val: V) {
        let hash = hash!(key);
        let update_element = match self.txn.search(&hash) {
            None => HMElement::One(key, val),
            Some(elem) => match elem {
                HMElement::One(k, v) => {
                    if *k == key {
                        HMElement::One(key, val)
                    } else {
                        HMElement::Vec(vec![(k.clone(), v.clone()), (key, val)])
                    }
                }
                HMElement::Vec(vec) => {
                    let mut vec = vec.clone();
                    let mut elem = None;
                    for e in vec.iter_mut() {
                        if e.0 == key {
                            elem = Some(&mut e.1);
                            break;
                        }
                    }
                    if let Some(elem) = elem {
                        *elem = val;
                    } else {
                        vec.push((key, val));
                    }
                    HMElement::Vec(vec)
                }
            },
        };
        self.txn.update(hash, update_element);
    }

    pub fn remove(&mut self, key: &K) {
        let hash = hash!(key);
        match self.txn.search(&hash) {
            None => return,
            Some(elem) => match elem {
                HMElement::One(k, _) => {
                    if k == key {
                        self.txn.remove(&hash);
                    }
                }
                HMElement::Vec(vec) => {
                    let mut idx = 0;
                    while idx < vec.len() && vec[idx].0 != *key {
                        idx += 1;
                    }
                    // key not present
                    if idx == vec.len() {
                        return;
                    }
                    // only two elements, make into One(..):
                    if vec.len() == 2 {
                        let update_one = if idx == 0 {
                            HMElement::One(vec[1].0.clone(), vec[1].1.clone())
                        } else {
                            HMElement::One(vec[0].0.clone(), vec[0].1.clone())
                        };
                        self.txn.update(hash, update_one);
                        return;
                    }
                    // remove just the one element:
                    let mut update_vec = Vec::with_capacity(vec.len() - 1);
                    let i = 0;
                    while i < vec.len() {
                        if i != idx {
                            update_vec.push(vec[i].clone());
                        }
                    }
                    self.txn.update(hash, HMElement::Vec(update_vec));
                }
            },
        }
    }

    pub fn commit(self) {
        self.txn.commit();
    }
}

#[cfg(test)]
mod test {
    use super::HashMap;
    use rand::{thread_rng, Rng};

    #[test]
    fn update_basic() {
        let map = HashMap::new();
        let mut write = map.write();
        write.update(65, 65);
        write.update(2, 2);
        write.update(1000, 1000);
        let mut read = map.read();
        assert!(
            read.search(&65).is_none(),
            "Key was written into map without committing write transaction."
        );
        write.commit();

        write = map.write();
        for i in 5..120 {
            write.update(i, i * 2);
        }

        read = map.read();
        assert!(
            read.search(&5).is_none(),
            "Key was written into map without committing write transaction."
        );
        assert_eq!(read.search(&65), Some(&65));

        assert_eq!(write.search(&2), Some(&2));
        assert_eq!(write.search(&1000), Some(&1000));
        for i in 5..120 {
            assert_eq!(i * 2, *write.search(&i).unwrap());
        }

        write.commit();
        read = map.read();
        for i in 5..120 {
            assert_eq!(i * 2, *read.search(&i).unwrap());
        }
    }

    // see description for the next macro (check_all)
    macro_rules! check_one {
        ($expect:expr, $actual:expr, $key:expr) => {
            match $expect {
                0 => {
                    if let Some(rec) = $actual {
                        panic!(
                            "No record expected for key {}, received ({}, {}).",
                            $key, rec.0, rec.1
                        );
                    }
                }
                e => match $actual {
                    None => panic!("Key {} should be stored, but no record found", $key),
                    Some(rec) => assert_eq!(
                        **rec,
                        ($key, e),
                        "Unexpected record. Expected ({}, {}), received ({}, {}).",
                        $key,
                        e,
                        rec.0,
                        rec.1
                    ),
                },
            }
        };
    }

    // In the randomized test, we generate random keys out of a 0..$count range
    // and record separately which elements should be present into a (count-sized)
    // array; this macro receives a reference to a transaction struct (no matter
    // read or write, it uses only search functions, which both have), the array
    // of records (named $members) and the $count parameter (giving the range of
    // keys we shall check)
    // the macro then makes a search query sequentially for each key of given
    // range and compares the result to what's in $members. values are tuples of
    // the form (key, members[key]) and should be missing when members[key] is 0
    // (ie. (_, 0) is never stored in the map)
    macro_rules! check_all {
        ($txn:expr, $members:expr, $count: expr) => {
            for j in 0..$count {
                let record = $txn.search(&j);
                check_one!($members[j], &record, j);
            }
        };
    }

    // The possible keys generated by the general test will be in the range
    // [0, GENERAL_MAX_KEY]
    const GENERAL_MAX_KEY: usize = 3000;
    // The number of query iterations in each of the 8 iterations in the general
    // test. This number should derive from GENERAL_MAX_KEY.
    const GENERAL_ITER_COUNT: usize = 1200;
    #[test]
    fn random_general() {
        let mut rng = thread_rng();
        let map: HashMap<usize, (usize, usize)> = HashMap::new();
        let mut member = [[0; GENERAL_MAX_KEY]; 2];
        let mut member_idx = 0;
        let mut write = map.write();
        for i in 0..8 {
            for j in 1..GENERAL_ITER_COUNT {
                let key = rng.gen_range(0, GENERAL_MAX_KEY);
                let choice = rng.gen_range(0, 5 + i);
                if choice == 0 {
                    // commit
                    member_idx = switch_idx(member_idx);
                    let read = map.read();
                    // check that no changes leaked from the uncommited write
                    // into a fresh read txn
                    check_all!(&read, &member[member_idx], GENERAL_MAX_KEY);
                    write.commit();
                    // 'update' member array:
                    member[member_idx] = member[switch_idx(member_idx)].clone();
                    write = map.write();
                } else if choice < 5 {
                    // update
                    write.update(key, (key, j));
                    member[member_idx][key as usize] = j;
                } else {
                    // remove
                    write.remove(&key);
                    member[member_idx][key as usize] = 0;
                }
            }
            check_all!(&write, &member[member_idx], GENERAL_MAX_KEY);
        }
    }
    fn switch_idx(idx: usize) -> usize {
        if idx == 0 {
            1
        } else {
            0
        }
    }
}
