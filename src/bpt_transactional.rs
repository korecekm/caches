// SPDX-FileCopyrightText: 2024 2023 Martin Koreček
//
// SPDX-License-Identifier: GPL-3.0-or-later

// # A concurrently readable, transactional B+ tree
// The underlying sequential data structure is the standard B+ tree. The "transactional" properties
// described in KVMap's docs are guaranteed with the method explained in section 3.1 of
// https://dl.acm.org/doi/10.1145/2501620.2501623.
// The root is protected with a Mutex that needs to be locked for a transaction's creation. Memory
// reclamation is guaranteed with the STD Arc. All nodes need to keep a transaction ID (txid) that
// increases with each write transaction. This number lets us know which nodes were created with an
// earlier write transaction (and can therefore not be modified with this one) and which were
// already created by this one.
// 
// DISCLAIMER: This is a transactional B+ tree made for a prototype transactional hash map.
// Implementing a transactional B+ tree is rather complicated and this code may be a little hard to
// orientate in. But this is not used anywhere in the thesis expect a comparison with the TrieMap
// The reader of this source file is expected to understand both how a standard B+ tree works and
// the method for making it transactional in the cited article.

#[cfg(test)]
use std::fmt::Display;
use std::mem::{self, MaybeUninit};
use std::sync::{Arc, Mutex, MutexGuard};

// The maximum number of child nodes
// ! This can currently not be changed as is, because certain functions in Node
// statically count on this parameter being 8 !
const B_PARAMETER: usize = 8;

// simulates mem::take for MaybeUninit, ::uninit() acting as the default value
macro_rules! take_mu {
    ($maybe_uninit:expr) => {
        mem::replace($maybe_uninit, MaybeUninit::uninit())
    };
}

// The 'pointer' to child nodes is simulated by an Arc reference Option
type Child<T> = Option<Arc<T>>;

// Branch node of the B+ tree
#[derive(Clone)]
struct Branch<K, V>
where
    K: Ord + Copy,
    V: Clone,
{
    txid: u32,
    key_count: u8,
    // Keys and references to child nodes are stored in separate arrays
    keys: [MaybeUninit<K>; B_PARAMETER - 1],
    refs: [Child<Node<K, V>>; B_PARAMETER],
}

// Leaf node of the B+ tree
#[derive(Clone)]
struct Leaf<K, V>
where
    K: Ord + Copy,
    V: Clone,
{
    txid: u32,
    key_count: u8,
    // Keys and references to child values are stored in separate arrays
    keys: [MaybeUninit<K>; B_PARAMETER],
    refs: [Child<V>; B_PARAMETER],
}

// A general node of the B+ tree
#[derive(Clone)]
enum Node<K, V>
where
    K: Ord + Copy,
    V: Clone,
{
    Branch(Branch<K, V>),
    Leaf(Leaf<K, V>),
}

/// A concurrently readable, transactional B+ tree holding Key-Value pairs
/// (ordered by keys).
///
/// KVMap itself works only as an immutable handle. Modifications to the tree
/// need to be done via KVMWriteTxn write transactions and are only recorded
/// permanently when these transactions get commited. KVMReadTxn transactions
/// provide snapshots to the current state of the tree, ie. they enable you to
/// search through the records as they were at the point of the transaction's
/// creation.
///
/// The read and write transactions may be generated via the `read()` and
/// `write()` functions, respectively.
///
/// ## Example:
/// ```
/// let map = KVMap::new();
///
/// // create a KVMWriteTxn handle to be able to modify the tree
/// let mut write = map.write();
/// // only one write transaction can exist at a time
/// assert!(map.try_write().is_none());
///
/// // insert three new values, update one of them and remove another
/// write.update(1, 'A');
/// write.update(2, 'B');
/// write.update(3, 'C');
/// write.update(2, 'D');
/// write.remove(&3);
///
/// // the write transaction hasn't been commited yet, and therefore isn't
/// // visible to a new read transaction
/// assert!(map.read().search(&1).is_none());
///
/// // commit the write transaction:
/// // (it is also possible to roll it back simply by dropping the transaction
/// // handle)
/// write.commit();
/// // from now, a new write transaction may be created
///
/// // a new read transaction will now see all of the records made by the write
/// // transaction
/// let read = map.read();
/// assert_eq!(read.search(&1), Some(&'A'));
/// assert_eq!(read.search(&2), Some(&'D'));
/// assert_eq!(read.search(&3), None);
/// ```
/// `search(&key)` is currently the only supported read-only operation
/// (provided both by the read and write transaction structs), giving an
/// `Option` with the corresponding value's (immutable) reference (or `None`
/// in case it isn't stored).
///
/// The currently supported modifying operations (only provided by the write
/// transaction) are
/// * `update(key, value)`, which updates a value for given key, or inserts it
///   into the tree if it isn't recorded yet
/// * `remove(&key)`, which removes given key's record inside the tree (or does
///    nothing if it isn't recorded)
pub struct KVMap<K, V>
where
    K: Ord + Copy,
    V: Clone,
{
    // Root node
    root: Mutex<Child<Node<K, V>>>,
    // Mutex providing the uniqueness of write transactions
    write: Mutex<()>,
}

/// Read snapshot for the `KVMap` transactional hash map
pub struct KVMReadTxn<K, V>
where
    K: Ord + Copy,
    V: Clone,
{
    // Reference to the root node
    root: Child<Node<K, V>>,
}

/// Write handle for the `KVMap` transactional hash map. Up to one instance of
/// a tree's write "transaction" may exist at a time. Changes made with the
/// handle only propagate globally after calling the `commit` method
pub struct KVMWriteTxn<'a, K, V>
where
    K: Ord + Copy,
    V: Clone,
{
    // This write transaction's txn ID
    txid: u32,
    // Reference to the global B+ tree handle
    caller: &'a KVMap<K, V>,
    // Reference to the root node (either the original, or this write
    // transaction's modified clone)
    root: Child<Node<K, V>>,
    // MutexGuard protecting the uniqueness of this write transaction
    _guard: MutexGuard<'a, ()>,
}

// IMPLEMENTATION:

unsafe impl<K, V> Send for KVMap<K, V>
where
    K: Ord + Copy,
    V: Clone,
{
}
unsafe impl<K, V> Sync for KVMap<K, V>
where
    K: Ord + Copy,
    V: Clone,
{
}

impl<K, V> KVMap<K, V>
where
    K: Ord + Copy,
    V: Clone,
{
    /// Generate an empty KVMap handle.
    pub fn new() -> Self {
        Self {
            root: Mutex::new(None),
            write: Mutex::new(()),
        }
    }

    /// Generate a read transaction for the current map state.
    pub fn read(&self) -> KVMReadTxn<K, V> {
        KVMReadTxn {
            root: match &*self.root.lock().unwrap() {
                None => None,
                Some(arc) => Some(arc.clone()),
            },
        }
    }

    /// Generate a write transaction enabling to modify the map.
    ///
    /// If another write transaction is still active, this will wait for it to
    /// get committed or rolled back.
    pub fn write(&self) -> KVMWriteTxn<K, V> {
        let guard = self.write.lock().unwrap();
        self.prepare_write_txn(guard)
    }

    /// Generates a write transaction enabling to modify the map, but only if
    /// there is no other write transaction currently active.
    pub fn try_write(&self) -> Option<KVMWriteTxn<K, V>> {
        let guard = self.write.try_lock();
        match guard {
            Err(_) => None,
            Ok(guard) => Some(self.prepare_write_txn(guard)),
        }
    }

    /// Once the `write` Mutex of the tree has been successfully locked, this
    /// prepares the write transaction handle. The MutexGuard for `write` is
    /// given in `guard`
    fn prepare_write_txn<'a>(&'a self, guard: MutexGuard<'a, ()>) -> KVMWriteTxn<'a, K, V> {
        let root = &*self.root.lock().unwrap();
        // Determine new transaction's id based on the old one in the map's
        // root.
        let txid = match root {
            None => 0,
            Some(arc) => match &**arc {
                Node::Leaf(ref leaf) => leaf.txid + 1,
                Node::Branch(ref branch) => branch.txid + 1,
            },
        };
        // Return the write handle itself
        KVMWriteTxn {
            txid,
            caller: self,
            root: match root {
                None => None,
                Some(arc) => Some((*arc).clone()),
            },
            _guard: guard,
        }
    }
}

impl<K, V> KVMReadTxn<K, V>
where
    K: Ord + Copy,
    V: Clone,
{
    /// Retrieves the value for given key, if present.
    pub fn search(&self, key: &K) -> Option<&V> {
        match &self.root {
            None => None,
            Some(arc) => Node::search(arc, key),
        }
    }

    /// Checks that all nodes obey the proper ordering of keys, and that the
    /// total number of stored records is as the given expected count.
    #[cfg(test)]
    fn check_bptree_properties(&self, expect_record_count: usize)
    where
        K: Display,
    {
        if let Some(ref arc_root) = self.root {
            // Check the properties in the root's subtree (the whole tree)
            let (_, count) = Node::check_bptree_properties(arc_root, None, None, true);
            assert_eq!(
                expect_record_count, count,
                "Tree was expected to hold {} elements. Actually detected {}.",
                expect_record_count, count
            );
        }
    }
}

// # HOW REMOVE WORKS:
// Aside from the key to be removed in the subtree, a node receives refs to its
// left and right neighbor (one of them may be None, but not both);
// If underflow happens, we first try to rotate from the right neighbor, then
// from the left; if neither are possible, neighbors reached lower limit and
// we merge with one of them, first trying merging with the right one, then the
// left; In either case, the node that's called is kept and the merged one
// (right or left) becomes unused
enum BPTRemoveResponse<K> {
    NoChange,                    // underflow didn't occur
    RotateLeft(MaybeUninit<K>),  // the key to the left should be changed for given value
    RotateRight(MaybeUninit<K>), // the key on idx corresponding to changed node should change
    MergeLeft,                   // node was merged with the one to the left
    MergeRight,                  // node was merged with the one to the right
}

impl<'a, K, V> KVMWriteTxn<'a, K, V>
where
    K: Ord + Copy,
    V: Clone,
{
    /// Retrieves the value for given key, if present.
    pub fn search(&self, key: &K) -> Option<&V> {
        match &self.root {
            None => None,
            Some(arc) => Node::search(arc, key),
        }
    }

    /// Update this key-value pair (i.e. insert it if key not present, or
    /// update the value for the key if it is).
    pub fn update(&mut self, key: K, val: V) {
        self.root = match mem::take(&mut self.root) {
            // Root is none. We create a new root with given key-value pair
            None => Node::init_root(self.txid, key, val),
            Some(arc) => {
                let mut arc = Node::modify_node(arc, self.txid);
                // Call update for the (sub)tree
                let response = Node::update(Arc::get_mut(&mut arc).unwrap(), key, val);
                // If the B+ tree's depth increases, we need to create a new
                // root node
                if let Some((new_key, right_child)) = response {
                    Node::new_root(self.txid, new_key, arc, right_child)
                } else {
                    Some(arc)
                }
            }
        }
    }

    /// Remove the record with given key, if present.
    pub fn remove(&mut self, key: &K) {
        if self.search(key).is_none() {
            return;
        }
        // We ensured key is present
        self.root = if let Some(arc_root) = mem::take(&mut self.root) {
            let mut arc_root = Node::modify_node(arc_root, self.txid);
            // Call apropriate remove function based on node type
            match &mut Arc::get_mut(&mut arc_root).unwrap() {
                Node::Branch(ref mut branch) => {
                    if self.remove_in_root_branch(branch, key) {
                        return;
                    }
                }
                Node::Leaf(ref mut leaf) => {
                    if self.remove_in_root_leaf(leaf, key) {
                        return;
                    }
                }
            }
            Some(arc_root)
        } else {
            panic!("Unreachable.");
        }
    }

    /// Returns true if the function modified self.root
    fn remove_in_root_branch(&mut self, branch: &mut Branch<K, V>, key: &K) -> bool {
        // find the corresponding child index
        let mut idx = 0;
        while idx < branch.key_count as usize && key > unsafe { &*branch.keys[idx].as_ptr() } {
            idx += 1;
        }
        // prepare neighboring nodes in case called child underflows
        let mut left = if idx == 0 {
            None
        } else {
            mem::take(&mut branch.refs[idx - 1])
        };
        let mut right = if idx < branch.key_count as usize {
            mem::take(&mut branch.refs[idx + 1])
        } else {
            None
        };
        // recurse into child corresponding to $key
        let mut called_arc =
            Node::modify_node(mem::take(&mut branch.refs[idx]).unwrap(), self.txid);
        let response = Arc::get_mut(&mut called_arc)
            .unwrap()
            .remove(key, &mut left, &mut right);
        // restore refs that needed to be taken because of recursion
        branch.refs[idx] = Some(called_arc);
        if idx > 0 {
            branch.refs[idx - 1] = left;
        }
        if idx < branch.key_count as usize {
            branch.refs[idx + 1] = right;
        }
        // mutate branch accordingly to remove response
        match response {
            BPTRemoveResponse::NoChange => {} // no action
            BPTRemoveResponse::RotateLeft(new_key) => {
                branch.keys[idx - 1] = new_key;
            }
            BPTRemoveResponse::RotateRight(new_key) => {
                branch.keys[idx] = new_key;
            }
            _ => {
                // Merge:
                // Two children merged into one:
                if branch.key_count == 1 {
                    self.root = mem::take(&mut branch.refs[idx]);
                    return true;
                }
                // otherwise, just fill formed gap:
                // this depends on whether left or right neighbor was merged
                let offset = match response {
                    BPTRemoveResponse::MergeLeft => {
                        branch.refs[idx - 1] = mem::take(&mut branch.refs[idx]);
                        idx - 1
                    }
                    BPTRemoveResponse::MergeRight => idx,
                    _ => panic!("Unreachable."),
                };
                for j in offset..(branch.key_count as usize - 1) {
                    branch.keys[j] = take_mu!(&mut branch.keys[j + 1]);
                    branch.refs[j + 1] = mem::take(&mut branch.refs[j + 2]);
                }
                branch.key_count -= 1;
            }
        }
        false
    }

    /// Returns true if the function modified self.root
    fn remove_in_root_leaf(&mut self, leaf: &mut Leaf<K, V>, key: &K) -> bool {
        // Just one key, root can be turned into None and txids will go from 0 again
        if leaf.key_count == 1 {
            self.root = None;
            self.txid = 0;
            return true;
        }

        // find corresponding index (key must be present)
        let mut idx = 0;
        while key > unsafe { &*leaf.keys[idx].as_ptr() } {
            idx += 1;
        }
        // fill formed gap
        for j in (idx + 1)..(leaf.key_count as usize) {
            leaf.keys[j - 1] = take_mu!(&mut leaf.keys[j]);
            leaf.refs[j - 1] = mem::take(&mut leaf.refs[j]);
        }
        leaf.key_count -= 1;

        false
    }

    /// Commit the changes done with this write transaction.
    ///
    /// If you wish to roll the changes back, simpy have the KVMWriteTxn handle
    /// dropped.
    pub fn commit(self) {
        // Exchange old root with the (potentially) modified one
        *self.caller.root.lock().unwrap() = self.root;
    }

    /// Checks that all nodes obey the proper ordering of keys, and that the
    /// total number of stored records is as the given expected count.
    #[cfg(test)]
    fn check_bptree_properties(&self, expect_record_count: usize)
    where
        K: Display,
    {
        if let Some(ref arc_root) = self.root {
            let (_, count) = Node::check_bptree_properties(arc_root, None, None, true);
            assert_eq!(
                expect_record_count, count,
                "Tree was expected to hold {} elements. Actually detected {}.",
                expect_record_count, count
            );
        }
    }
}

impl<K, V> Node<K, V>
where
    K: Ord + Copy,
    V: Clone,
{
    /// If given Node (Arc) has given txid, it is returned as is.
    /// Otherwise, the whole Node gets cloned with the given txid and a reference
    /// to the clone is returned.
    fn modify_node(node: Arc<Self>, txid: u32) -> Arc<Self> {
        let node_txid = match &*node {
            Node::Branch(ref branch) => branch.txid,
            Node::Leaf(ref leaf) => leaf.txid,
        };
        if node_txid == txid {
            node
        } else {
            let mut clone = (*node).clone();
            match &mut clone {
                Node::Branch(ref mut branch) => branch.txid = txid,
                Node::Leaf(ref mut leaf) => leaf.txid = txid,
            }
            Arc::new(clone)
        }
    }

    /// Initiate the root node with this key-value element.
    // Unfortunately, the way we use MaybeUninits requires the arrays to be
    // initiate manually like this (the [elem; count] requires elem to be
    // Clone)
    fn init_root(txid: u32, key: K, val: V) -> Child<Self> {
        Some(Arc::new(Node::Leaf(Leaf {
            txid,
            key_count: 1,
            keys: [
                MaybeUninit::new(key),
                MaybeUninit::uninit(),
                MaybeUninit::uninit(),
                MaybeUninit::uninit(),
                MaybeUninit::uninit(),
                MaybeUninit::uninit(),
                MaybeUninit::uninit(),
                MaybeUninit::uninit(),
            ],
            refs: [
                Some(Arc::new(val)),
                None,
                None,
                None,
                None,
                None,
                None,
                None,
            ],
        })))
    }

    /// Creates a new root when the tree's depth increases.
    /// Only needs the root key and the references (Arcs) to the left and right
    /// children of the key.
    fn new_root(
        txid: u32,
        key: K,
        left_child: Arc<Node<K, V>>,
        right_child: Arc<Node<K, V>>,
    ) -> Child<Self> {
        Some(Arc::new(Self::Branch(Branch {
            txid,
            key_count: 1,
            keys: [
                MaybeUninit::new(key),
                MaybeUninit::uninit(),
                MaybeUninit::uninit(),
                MaybeUninit::uninit(),
                MaybeUninit::uninit(),
                MaybeUninit::uninit(),
                MaybeUninit::uninit(),
            ],
            refs: [
                Some(left_child),
                Some(right_child),
                None,
                None,
                None,
                None,
                None,
                None,
            ],
        })))
    }

    /// Search for an element in this subtree.
    fn search<'a>(node: &'a Arc<Self>, key: &K) -> Option<&'a V> {
        // We proceed iteratively, moving deeper in the tree
        let mut node = node;
        'outer: loop {
            match &**node {
                // Current node is a branch node, "recurse" deeper
                Node::Branch(ref branch) => {
                    // Identify the right child node to seach in
                    for i in 0..(branch.key_count as usize) {
                        if key <= unsafe { &*branch.keys[i].as_ptr() } {
                            node = branch.refs[i].as_ref().unwrap();
                            continue 'outer;
                        }
                    }
                    // Move on to the child node
                    node = branch.refs[branch.key_count as usize].as_ref().unwrap();
                }
                // Leaf node, find given key
                Node::Leaf(ref leaf) => {
                    for i in 0..(leaf.key_count as usize) {
                        if key == unsafe { &*leaf.keys[i].as_ptr() } {
                            return Some(&*leaf.refs[i].as_ref().unwrap());
                        }
                    }
                    return None;
                }
            }
        }
    }

    /// Inserts or (if present) updates val for given key. If the node is split,
    /// given node will be made into the left one and a tuple will be returned,
    /// containing the median key (travelling up) and an arc to the right node.
    fn update(&mut self, key: K, val: V) -> Option<(K, Arc<Node<K, V>>)> {
        match self {
            Self::Branch(branch) => Self::update_in_branch(branch, key, val),
            Self::Leaf(leaf) => Self::update_in_leaf(leaf, key, val),
        }
    }

    /// Perform the update through a branch node
    fn update_in_branch(branch: &mut Branch<K, V>, key: K, val: V) -> Option<(K, Arc<Node<K, V>>)> {
        // find the correct child index for this key
        let mut idx = 0;
        while idx < (branch.key_count as usize) && key > unsafe { *branch.keys[idx].as_ptr() } {
            idx += 1;
        }
        let mut child = mem::take(&mut branch.refs[idx]).unwrap();
        child = Self::modify_node(child, branch.txid);
        let child_response = Self::update(Arc::get_mut(&mut child).unwrap(), key, val);
        branch.refs[idx] = Some(child);

        if let Some((insert_key, right_child)) = child_response {
            if (branch.key_count as usize) < B_PARAMETER - 1 {
                // branch hasn't reached its capacity:
                // move larger keys further right
                for j in (idx..(branch.key_count as usize)).rev() {
                    branch.keys[j + 1] = take_mu!(&mut branch.keys[j]);
                    branch.refs[j + 2] = mem::take(&mut branch.refs[j + 1]);
                }
                // store received data
                branch.keys[idx] = MaybeUninit::new(insert_key);
                branch.refs[idx + 1] = Some(right_child);
                branch.key_count += 1;
                None
            } else {
                // branch needs to be split
                Self::split_branch(branch, idx, insert_key, right_child)
            }
        } else {
            None
        }
    }

    /// Split a branch into two, according to standard B+ tree rules
    fn split_branch(
        branch: &mut Branch<K, V>,
        idx: usize,
        insert_key: K,
        right_arc: Arc<Node<K, V>>,
    ) -> Option<(K, Arc<Node<K, V>>)> {
        branch.key_count = (B_PARAMETER / 2) as u8;
        let mut right_branch = Branch {
            txid: branch.txid,
            key_count: ((B_PARAMETER / 2) - 1 + (B_PARAMETER % 2)) as u8,
            keys: [
                MaybeUninit::uninit(),
                MaybeUninit::uninit(),
                MaybeUninit::uninit(),
                MaybeUninit::uninit(),
                MaybeUninit::uninit(),
                MaybeUninit::uninit(),
                MaybeUninit::uninit(),
            ],
            refs: [None, None, None, None, None, None, None, None],
        };
        // We first copy all elements into a single array and then distribute
        // them into the two branches. That makes our implementation quite a
        // bit simpler, but will probably not be optimized by the compiler and
        // should ideally be rewritten.
        // It also leads to splits being asymmetric in the same way. A better
        // implementation would perhaps utilize idx in choosing which formed
        // branch has more children (the same goes with split_leaf, although in
        // opposite cases in relation to B_PARAMETER parity)
        let mut all_keys = [
            MaybeUninit::uninit(),
            MaybeUninit::uninit(),
            MaybeUninit::uninit(),
            MaybeUninit::uninit(),
            MaybeUninit::uninit(),
            MaybeUninit::uninit(),
            MaybeUninit::uninit(),
            MaybeUninit::uninit(),
        ];
        let mut all_refs = [None, None, None, None, None, None, None, None, None];
        // branch.refs[0] always stays
        for j in 0..idx {
            all_keys[j] = take_mu!(&mut branch.keys[j]);
            all_refs[j + 1] = mem::take(&mut branch.refs[j + 1]);
        }
        // Unify records
        all_keys[idx] = MaybeUninit::new(insert_key);
        all_refs[idx + 1] = Some(right_arc);
        for j in idx..(B_PARAMETER - 1) {
            all_keys[j + 1] = take_mu!(&mut branch.keys[j]);
            all_refs[j + 2] = mem::take(&mut branch.refs[j + 1]);
        }

        // Divide them right between the two nodes
        for j in 0..(B_PARAMETER / 2) {
            branch.keys[j] = take_mu!(&mut all_keys[j]);
            branch.refs[j + 1] = mem::take(&mut all_refs[j + 1]);
        }
        right_branch.refs[0] = mem::take(&mut all_refs[B_PARAMETER / 2 + 1]);
        for j in (B_PARAMETER / 2 + 1)..B_PARAMETER {
            right_branch.keys[j - (B_PARAMETER / 2) - 1] = take_mu!(&mut all_keys[j]);
            right_branch.refs[j - (B_PARAMETER / 2)] = mem::take(&mut all_refs[j + 1]);
        }

        Some((
            unsafe { all_keys[B_PARAMETER / 2].assume_init() },
            Arc::new(Node::Branch(right_branch)),
        ))
    }

    /// Perform the update in a leaf node
    fn update_in_leaf(leaf: &mut Leaf<K, V>, key: K, val: V) -> Option<(K, Arc<Node<K, V>>)> {
        // find the key's position (or overflow)
        let mut idx: usize = 0;
        while idx < (leaf.key_count as usize) && key > unsafe { *leaf.keys[idx].as_ptr() } {
            idx += 1;
        }

        // key is already stored
        if idx < (leaf.key_count as usize) && key == unsafe { *leaf.keys[idx].as_ptr() } {
            leaf.refs[idx] = Some(Arc::new(val));
            return None;
        }

        // leaf hasn't reached its capacity
        if (leaf.key_count as usize) < B_PARAMETER {
            // move larger keys further 'right'
            for j in (idx..(leaf.key_count as usize)).rev() {
                leaf.keys[j + 1] = take_mu!(&mut leaf.keys[j]);
                leaf.refs[j + 1] = mem::take(&mut leaf.refs[j]);
            }
            // store new data
            leaf.keys[idx] = MaybeUninit::new(key);
            leaf.refs[idx] = Some(Arc::new(val));
            leaf.key_count += 1;
            return None;
        }

        // the node needs to be split
        Self::split_leaf(leaf, idx, key, val)
    }

    /// Split a leaf node into two, according to standard B+ tree rules
    fn split_leaf(
        leaf: &mut Leaf<K, V>,
        idx: usize,
        key: K,
        val: V,
    ) -> Option<(K, Arc<Node<K, V>>)> {
        leaf.key_count = ((B_PARAMETER / 2) + 1) as u8;
        let mut right_leaf = Leaf {
            txid: leaf.txid,
            key_count: ((B_PARAMETER / 2) + (B_PARAMETER % 2)) as u8,
            keys: [
                MaybeUninit::uninit(),
                MaybeUninit::uninit(),
                MaybeUninit::uninit(),
                MaybeUninit::uninit(),
                MaybeUninit::uninit(),
                MaybeUninit::uninit(),
                MaybeUninit::uninit(),
                MaybeUninit::uninit(),
            ],
            refs: [None, None, None, None, None, None, None, None],
        };
        // We first copy all elements into a single array and then distribute
        // them into the two leaves. That makes our implementation quite a bit
        // simpler, but will probably not be optimized by the compiler and
        // should ideally be rewritten.
        let mut all_keys = [
            MaybeUninit::uninit(),
            MaybeUninit::uninit(),
            MaybeUninit::uninit(),
            MaybeUninit::uninit(),
            MaybeUninit::uninit(),
            MaybeUninit::uninit(),
            MaybeUninit::uninit(),
            MaybeUninit::uninit(),
            MaybeUninit::uninit(),
        ];
        // Unify records
        let mut all_refs = [None, None, None, None, None, None, None, None, None];
        for j in 0..idx {
            all_keys[j] = take_mu!(&mut leaf.keys[j]);
            all_refs[j] = mem::take(&mut leaf.refs[j]);
        }
        all_keys[idx] = MaybeUninit::new(key);
        all_refs[idx] = Some(Arc::new(val));
        for j in idx..B_PARAMETER {
            all_keys[j + 1] = take_mu!(&mut leaf.keys[j]);
            all_refs[j + 1] = mem::take(&mut leaf.refs[j]);
        }
        // Split the records between the two leaves:
        let new_key = unsafe { all_keys[B_PARAMETER / 2].clone().assume_init() };
        for j in 0..((B_PARAMETER / 2) + 1) {
            leaf.keys[j] = take_mu!(&mut all_keys[j]);
            leaf.refs[j] = mem::take(&mut all_refs[j]);
        }
        for j in 0..((B_PARAMETER / 2) + (B_PARAMETER % 2)) {
            right_leaf.keys[j] = take_mu!(&mut all_keys[j + (B_PARAMETER / 2) + 1]);
            right_leaf.refs[j] = mem::take(&mut all_refs[j + (B_PARAMETER / 2) + 1]);
        }

        Some((new_key, Arc::new(Node::Leaf(right_leaf))))
    }

    /// Perform a remove in this subtree (see "HOW REMOVE WORKS" above)
    fn remove(
        &mut self,
        key: &K,
        left_neighbor: &mut Child<Self>,
        right_neighbor: &mut Child<Self>,
    ) -> BPTRemoveResponse<K> {
        match self {
            Node::Branch(ref mut branch) => {
                Self::remove_from_branch(branch, key, left_neighbor, right_neighbor)
            }
            Node::Leaf(ref mut leaf) => {
                Self::remove_from_leaf(leaf, key, left_neighbor, right_neighbor)
            }
        }
    }

    // (see "HOW REMOVE WORKS" above)
    fn remove_from_branch(
        branch: &mut Branch<K, V>,
        key: &K,
        left: &mut Child<Self>,
        right: &mut Child<Self>,
    ) -> BPTRemoveResponse<K> {
        // find corresponding child index
        let mut idx = 0;
        while idx < branch.key_count as usize && key > unsafe { &*branch.keys[idx].as_ptr() } {
            idx += 1;
        }
        // prepare neighboring nodes in case child underflows
        let mut left_child = if idx == 0 {
            None
        } else {
            mem::take(&mut branch.refs[idx - 1])
        };
        let mut right_child = if idx < branch.key_count as usize {
            mem::take(&mut branch.refs[idx + 1])
        } else {
            None
        };
        // recurse into child corresponding to $key
        let mut called_arc =
            Node::modify_node(mem::take(&mut branch.refs[idx]).unwrap(), branch.txid);
        let response =
            Arc::get_mut(&mut called_arc)
                .unwrap()
                .remove(key, &mut left_child, &mut right_child);
        //restore refs that needed to be taken for recursion
        branch.refs[idx] = Some(called_arc);
        if idx > 0 {
            branch.refs[idx - 1] = left_child;
        }
        if idx < branch.key_count as usize {
            branch.refs[idx + 1] = right_child;
        }
        // mutate branch accordingly to remove response from recursion
        match response {
            BPTRemoveResponse::NoChange => return response,
            BPTRemoveResponse::RotateLeft(new_key) => {
                branch.keys[idx - 1] = new_key;
                return BPTRemoveResponse::NoChange;
            }
            BPTRemoveResponse::RotateRight(new_key) => {
                branch.keys[idx] = new_key;
                return BPTRemoveResponse::NoChange;
            }
            BPTRemoveResponse::MergeLeft => {
                branch.refs[idx - 1] = mem::take(&mut branch.refs[idx]);
                for j in idx..(branch.key_count as usize) {
                    branch.keys[j - 1] = take_mu!(&mut branch.keys[j]);
                    branch.refs[j] = mem::take(&mut branch.refs[j + 1]);
                }
            }
            BPTRemoveResponse::MergeRight => {
                for j in idx..(branch.key_count as usize - 1) {
                    branch.keys[j] = take_mu!(&mut branch.keys[j + 1]);
                    branch.refs[j + 1] = mem::take(&mut branch.refs[j + 2]);
                }
            }
        }

        // Branch lost a key, in case of underflow, further mutations need to be done
        // (the key_count hasn't been mutated yet, but structurally, the branch acts as a
        //  branch with key_count - 1 keys)

        let min_keys = ((B_PARAMETER / 2) + (B_PARAMETER % 2)) as u8;
        // no underflow
        if branch.key_count >= min_keys {
            branch.key_count -= 1;
            return BPTRemoveResponse::NoChange;
        }

        // first, we try rotating
        if let Some(response) = Self::try_rotate_in_branch(branch, left, right) {
            return response;
        }

        // we must merge two neighbors
        Self::merge_branches(branch, left, right)
    }

    // Attempt a B+ tree rotation from either side
    fn try_rotate_in_branch(
        branch: &mut Branch<K, V>,
        left: &mut Child<Self>,
        right: &mut Child<Self>,
    ) -> Option<BPTRemoveResponse<K>> {
        let min_keys = ((B_PARAMETER / 2) + (B_PARAMETER % 2)) as u8;
        let mut response = None;
        // See if any rotation is possible, it will be executed eventualy.
        // first, try rotation from right neighbor.
        // We may already generate a proper remove response, that will also
        // give us the information about which rotation is possible, if any
        if let Some(ref neighbor) = right {
            if let Node::Branch(ref right_branch) = &**neighbor {
                if right_branch.key_count >= min_keys {
                    response = Some(BPTRemoveResponse::RotateRight(right_branch.keys[0].clone()));
                }
            } else {
                panic!("Unreachable.");
            }
        }
        if response.is_none() {
            if let Some(ref neighbor) = left {
                if let Node::Branch(ref left_branch) = &**neighbor {
                    if left_branch.key_count >= min_keys {
                        response = Some(BPTRemoveResponse::RotateLeft(
                            left_branch.keys[left_branch.key_count as usize - 1].clone(),
                        ));
                    }
                } else {
                    panic!("Unreachable.");
                }
            }
        }

        // if possible, execute the rotation itself
        if let Some(ref rotation) = response {
            match rotation {
                // Left rotation possible
                BPTRemoveResponse::RotateLeft(_) => {
                    let mut mut_left = Self::modify_node(mem::take(left).unwrap(), branch.txid);
                    // Move current records further right to free space for
                    // rotated element
                    for j in (0..(branch.key_count as usize - 1)).rev() {
                        branch.keys[j + 1] = take_mu!(&mut branch.keys[j]);
                        branch.refs[j + 2] = mem::take(&mut branch.refs[j + 1]);
                    }
                    branch.refs[1] = mem::take(&mut branch.refs[0]);
                    // Rotate the record itself from the (now modifiable) left
                    // neighbor
                    if let Node::Branch(ref mut left_branch) = Arc::get_mut(&mut mut_left).unwrap()
                    {
                        let take_ref =
                            mem::take(&mut left_branch.refs[left_branch.key_count as usize]);
                        let new_key = take_ref.as_ref().unwrap().rightmost_key();
                        branch.keys[0] = new_key;
                        branch.refs[0] = take_ref;
                        left_branch.key_count -= 1;
                    }
                    *left = Some(mut_left);
                }
                // Right rotation possible
                BPTRemoveResponse::RotateRight(_) => {
                    let mut mut_right = Self::modify_node(mem::take(right).unwrap(), branch.txid);
                    let new_key = (&**branch.refs[branch.key_count as usize - 1].as_ref().unwrap())
                        .rightmost_key();
                    branch.keys[branch.key_count as usize - 1] = new_key;
                    if let Node::Branch(ref mut right_branch) =
                        Arc::get_mut(&mut mut_right).unwrap()
                    {
                        // Rotate the leftmost element from the right neighbor
                        branch.refs[branch.key_count as usize] =
                            mem::take(&mut right_branch.refs[0]);
                        // Move the neighbor's records accordingly to fill
                        // formed gap
                        right_branch.refs[0] = mem::take(&mut right_branch.refs[1]);
                        for j in 0..(right_branch.key_count as usize - 1) {
                            right_branch.keys[j] = take_mu!(&mut right_branch.keys[j + 1]);
                            right_branch.refs[j + 1] = mem::take(&mut right_branch.refs[j + 2]);
                        }
                        right_branch.key_count -= 1;
                    } else {
                        panic!("Unreachable.");
                    }
                    *right = Some(mut_right);
                }
                _ => panic!("Unreachable."),
            }
        }

        response
    }

    fn merge_branches(
        branch: &mut Branch<K, V>,
        left: &mut Child<Self>,
        right: &mut Child<Self>,
    ) -> BPTRemoveResponse<K> {
        // try merging right neighbor
        if let Some(_) = right {
            let new_key =
                (&**branch.refs[branch.key_count as usize - 1].as_ref().unwrap()).rightmost_key();
            branch.keys[branch.key_count as usize - 1] = new_key;
            // Arc counting forces us to take the Rcs in case it has current txid
            let mut mut_right = Self::modify_node(mem::take(right).unwrap(), branch.txid);
            if let Node::Branch(ref mut right_branch) = Arc::get_mut(&mut mut_right).unwrap() {
                branch.refs[branch.key_count as usize] = mem::take(&mut right_branch.refs[0]);
                for j in 0..(right_branch.key_count as usize) {
                    branch.keys[branch.key_count as usize + j] =
                        take_mu!(&mut right_branch.keys[j]);
                    branch.refs[branch.key_count as usize + j + 1] =
                        mem::take(&mut right_branch.refs[j + 1]);
                }
                branch.key_count += right_branch.key_count;
            } else {
                panic!("Unreachable.");
            }
            return BPTRemoveResponse::MergeRight;
        }

        // try merging left neighbor
        if let Some(_) = left {
            // Arc counting forces us to take the Rcs in case it has current txid
            let mut mut_left = Self::modify_node(mem::take(left).unwrap(), branch.txid);
            if let Node::Branch(ref mut left_branch) = Arc::get_mut(&mut mut_left).unwrap() {
                let new_key = (&**left_branch.refs[left_branch.key_count as usize]
                    .as_ref()
                    .unwrap())
                    .rightmost_key();
                // move current branch content right so that it goes after records from left neighbor
                for j in (0..(branch.key_count as usize - 1)).rev() {
                    branch.keys[left_branch.key_count as usize + j + 1] =
                        take_mu!(&mut branch.keys[j]);
                    branch.refs[left_branch.key_count as usize + j + 2] =
                        mem::take(&mut branch.refs[j + 1]);
                }
                branch.keys[left_branch.key_count as usize] = new_key;
                branch.refs[left_branch.key_count as usize + 1] = mem::take(&mut branch.refs[0]);
                // clone neighbor content to this branch
                branch.refs[0] = mem::take(&mut left_branch.refs[0]);
                for j in 0..(left_branch.key_count as usize) {
                    branch.keys[j] = take_mu!(&mut left_branch.keys[j]);
                    branch.refs[j + 1] = mem::take(&mut left_branch.refs[j + 1]);
                }
                branch.key_count += left_branch.key_count;
            } else {
                panic!("Unreachable.");
            }
            return BPTRemoveResponse::MergeLeft;
        }

        panic!("Invalid remove case: remove was called on a branch with no neighbors given.");
    }

    // (see "HOW REMOVE WORKS" above)
    fn remove_from_leaf(
        leaf: &mut Leaf<K, V>,
        key: &K,
        left: &mut Child<Self>,
        right: &mut Child<Self>,
    ) -> BPTRemoveResponse<K> {
        // find corresponding index (key must be present)
        let mut idx = 0;
        while key > unsafe { &*leaf.keys[idx].as_ptr() } {
            idx += 1;
        }

        let min_keys = ((B_PARAMETER / 2) + (B_PARAMETER % 2)) as u8;
        // underflow doesn't happen
        if leaf.key_count > min_keys {
            // simply fill formed gap
            for j in (idx + 1)..(leaf.key_count as usize) {
                leaf.keys[j - 1] = take_mu!(&mut leaf.keys[j]);
                leaf.refs[j - 1] = mem::take(&mut leaf.refs[j]);
            }
            leaf.key_count -= 1;
            return BPTRemoveResponse::NoChange;
        }

        // first, we try rotating
        if let Some(response) = Self::try_rotate_in_leaf(leaf, idx, left, right) {
            return response;
        }

        // we must merge two neighbors
        Self::merge_leafs(leaf, idx, left, right)
    }

    fn try_rotate_in_leaf(
        leaf: &mut Leaf<K, V>,
        idx: usize,
        left: &mut Child<Self>,
        right: &mut Child<Self>,
    ) -> Option<BPTRemoveResponse<K>> {
        let min_keys = ((B_PARAMETER / 2) + (B_PARAMETER % 2)) as u8;
        let mut response = None;
        // first see if rotating from right neighbor is possilbe
        // (splitting this into deciding if any rotation is possible and executing the rotation
        // itself seems structuraly simpler, as the execution requires potential node cloning)
        if let Some(ref neighbor) = right {
            if let Node::Leaf(ref right_leaf) = &**neighbor {
                if right_leaf.key_count > min_keys {
                    response = Some(BPTRemoveResponse::RotateRight(right_leaf.keys[0].clone()));
                }
            } else {
                panic!("Unreachable.");
            }
        }
        if response.is_none() {
            // see if rotating from left neighbor is possible
            if let Some(ref neighbor) = left {
                if let Node::Leaf(ref left_leaf) = &**neighbor {
                    if left_leaf.key_count > min_keys {
                        response = Some(BPTRemoveResponse::RotateLeft(
                            left_leaf.keys[left_leaf.key_count as usize - 2].clone(),
                        ));
                    }
                } else {
                    panic!("Unreachable.");
                }
            }
        }

        // if possible, execute the rotation itself
        if let Some(ref rotation) = response {
            match rotation {
                BPTRemoveResponse::RotateLeft(_) => {
                    // get a mutable version of the left neighbor
                    // (it may still hold an old txid and require cloning)
                    let mut mut_left = Self::modify_node(mem::take(left).unwrap(), leaf.txid);
                    if let Node::Leaf(ref mut left_leaf) = Arc::get_mut(&mut mut_left).unwrap() {
                        // move records one position to the right to create space for rotated record
                        for j in (0..idx).rev() {
                            leaf.keys[j + 1] = take_mu!(&mut leaf.keys[j]);
                            leaf.refs[j + 1] = mem::take(&mut leaf.refs[j]);
                        }
                        // rotate last record from left neighbor
                        leaf.keys[0] =
                            take_mu!(&mut left_leaf.keys[left_leaf.key_count as usize - 1]);
                        leaf.refs[0] =
                            mem::take(&mut left_leaf.refs[left_leaf.key_count as usize - 1]);
                        left_leaf.key_count -= 1;
                    } else {
                        panic!("Unreachable.");
                    }
                    *left = Some(mut_left);
                }
                BPTRemoveResponse::RotateRight(_) => {
                    // get a mutable version of the right neighbor
                    // (which may still hold an old txid and require cloning)
                    let mut mut_right = Self::modify_node(mem::take(right).unwrap(), leaf.txid);
                    if let Node::Leaf(ref mut right_leaf) = Arc::get_mut(&mut mut_right).unwrap() {
                        // fill gap created by removing record at index $idx
                        for j in (idx + 1)..(leaf.key_count as usize) {
                            leaf.keys[j - 1] = take_mu!(&mut leaf.keys[j]);
                            leaf.refs[j - 1] = mem::take(&mut leaf.refs[j]);
                        }
                        // rotate record
                        leaf.keys[leaf.key_count as usize - 1] = take_mu!(&mut right_leaf.keys[0]);
                        leaf.refs[leaf.key_count as usize - 1] = mem::take(&mut right_leaf.refs[0]);
                        // move neighbor records one position left to fill generated gap
                        for j in 0..(right_leaf.key_count as usize - 1) {
                            right_leaf.keys[j] = take_mu!(&mut right_leaf.keys[j + 1]);
                            right_leaf.refs[j] = mem::take(&mut right_leaf.refs[j + 1]);
                        }
                        right_leaf.key_count -= 1;
                    } else {
                        panic!("Unreachable.");
                    }
                    *right = Some(mut_right);
                }
                _ => panic!("Unreachable."),
            }
        }

        response
    }

    fn merge_leafs(
        leaf: &mut Leaf<K, V>,
        idx: usize,
        left: &mut Child<Self>,
        right: &mut Child<Self>,
    ) -> BPTRemoveResponse<K> {
        // Try merging right neighbor
        if let Some(_) = right {
            // fill the generated by removing record at index idx
            for j in (idx + 1)..(leaf.key_count as usize) {
                leaf.keys[j - 1] = take_mu!(&mut leaf.keys[j]);
                leaf.refs[j - 1] = mem::take(&mut leaf.refs[j]);
            }
            // clone all records from the neighbor
            // Arc counting forces us to take the Rcs in case it has current txid
            let mut mut_right = Self::modify_node(mem::take(right).unwrap(), leaf.txid);
            if let Node::Leaf(ref mut right_leaf) = Arc::get_mut(&mut mut_right).unwrap() {
                for j in 0..(right_leaf.key_count as usize) {
                    leaf.keys[leaf.key_count as usize + j - 1] = take_mu!(&mut right_leaf.keys[j]);
                    leaf.refs[leaf.key_count as usize + j - 1] = mem::take(&mut right_leaf.refs[j]);
                }
                leaf.key_count += right_leaf.key_count - 1;
                return BPTRemoveResponse::MergeRight;
            } else {
                panic!("Unreachable.");
            }
        }

        // Try merging left neighbor
        if let Some(_) = left {
            // Arc counting forces us to take the Rcs in case it has current txid
            let mut mut_left = Self::modify_node(mem::take(left).unwrap(), leaf.txid);
            if let Node::Leaf(ref mut left_leaf) = Arc::get_mut(&mut mut_left).unwrap() {
                // move current leaf content right so that it goes after records from left neighbor
                for j in ((idx + 1)..(leaf.key_count as usize)).rev() {
                    leaf.keys[left_leaf.key_count as usize + j - 1] = take_mu!(&mut leaf.keys[j]);
                    leaf.refs[left_leaf.key_count as usize + j - 1] = mem::take(&mut leaf.refs[j]);
                }
                for j in (0..idx).rev() {
                    leaf.keys[left_leaf.key_count as usize + j] = take_mu!(&mut leaf.keys[j]);
                    leaf.refs[left_leaf.key_count as usize + j] = mem::take(&mut leaf.refs[j]);
                }
                // clone neighbor content to this leaf
                for j in 0..(left_leaf.key_count as usize) {
                    leaf.keys[j] = take_mu!(&mut left_leaf.keys[j]);
                    leaf.refs[j] = mem::take(&mut left_leaf.refs[j]);
                }
                leaf.key_count += left_leaf.key_count - 1;
                return BPTRemoveResponse::MergeLeft;
            } else {
                panic!("Unreachable");
            }
        }

        panic!("Invalid remove case: remove was called on a leaf with no neighbors given");
    }

    /// Utility function for remove to determine a new separator.
    /// (the key gets cloned)
    fn rightmost_key(&self) -> MaybeUninit<K> {
        match self {
            Node::Branch(ref branch) => {
                (&*branch.refs[branch.key_count as usize].as_ref().unwrap()).rightmost_key()
            }
            Node::Leaf(ref leaf) => leaf.keys[leaf.key_count as usize - 1].clone(),
        }
    }

    /// Checks B+ tree invariants;
    /// Returns the depth and number of elements of the subtree rooted in given
    /// node.
    /// The `least_lim` and `most_lim` are the bounds the keys in this node may
    /// lay in, so that the right ordering is kept.
    #[cfg(test)]
    fn check_bptree_properties(
        node: &Arc<Self>,
        least_lim: Option<&K>,
        most_lim: Option<&K>,
        root: bool,
    ) -> (usize, usize)
    where
        K: Display,
    {
        let mut least_lim = least_lim;
        match &**node {
            Node::Branch(ref branch) => {
                // Check that the branch has the right number of child nodes
                // (no lower limit for root node)
                if !root {
                    let min_keys = (B_PARAMETER / 2) - 1 + (B_PARAMETER % 2);
                    assert!(branch.key_count >= min_keys as u8,
                        "Non-root branch nodes are expected to hold at least {} keys, found one with {}.", min_keys, branch.key_count);
                }
                assert!(
                    branch.key_count < B_PARAMETER as u8,
                    "Found branch node with {} keys. Maximum is {}.",
                    branch.key_count,
                    B_PARAMETER - 1
                );
                // Recurse the check to children, summing up to total number of
                // records
                let mut count = 0;
                let (d, cnt) = Self::check_bptree_properties(
                    branch.refs[0].as_ref().unwrap(),
                    least_lim,
                    unsafe { Some(&*branch.keys[0].as_ptr()) },
                    false,
                );
                count += cnt;
                // Check the right ordering of keys
                for i in 0..(branch.key_count as usize) {
                    if let Some(least) = least_lim {
                        assert!(
                            least < unsafe { &*branch.keys[i].as_ptr() },
                            "Branch key idx {} expected to be over {}, but was {}.",
                            i,
                            least,
                            unsafe { &*branch.keys[i].as_ptr() }
                        );
                    }
                    if let Some(most) = most_lim {
                        assert!(
                            most >= unsafe { &*branch.keys[i].as_ptr() },
                            "Branch key idx {} expected to be at most {}, but was {}.",
                            i,
                            most,
                            unsafe { *branch.keys[i].as_ptr() }
                        );
                    }
                    least_lim = unsafe { Some(&*branch.keys[i].as_ptr()) };
                    let mlim_subtree = if (i + 1) < (branch.key_count as usize) {
                        unsafe { Some(&*branch.keys[i + 1].as_ptr()) }
                    } else {
                        most_lim
                    };
                    let (d_now, cnt_now) = Self::check_bptree_properties(
                        branch.refs[i + 1].as_ref().unwrap(),
                        least_lim,
                        mlim_subtree,
                        false,
                    );
                    assert_eq!(
                        d, d_now,
                        "Nonequal depths of branch subtrees ({} and {}).",
                        d, d_now
                    );
                    count += cnt_now;
                }
                (d + 1, count)
            }
            Node::Leaf(ref leaf) => {
                // Check that the leaf has the right number of child nodes
                // (no lower limit for root node)
                if !root {
                    let min_keys = (B_PARAMETER / 2) + (B_PARAMETER % 2);
                    assert!(
                        leaf.key_count >= min_keys as u8,
                        "Non-root leaves are expected to hold at least {} keys, found one with {}.",
                        min_keys,
                        leaf.key_count
                    );
                }
                assert!(
                    leaf.key_count <= B_PARAMETER as u8,
                    "Found leaf node with {} keys. Maximum is {}.",
                    leaf.key_count,
                    B_PARAMETER
                );
                // Check key ordering
                for i in 0..(leaf.key_count as usize) {
                    if let Some(least) = least_lim {
                        assert!(
                            least < unsafe { &*leaf.keys[i].as_ptr() },
                            "Leaf key idx {} expected to be over {}, but was {}.",
                            i,
                            least,
                            unsafe { &*leaf.keys[i].as_ptr() }
                        );
                    }
                    if let Some(most) = most_lim {
                        assert!(
                            most >= unsafe { &*leaf.keys[i].as_ptr() },
                            "Leaf key idx {} expected to be at most {}, but was {}.",
                            i,
                            most,
                            unsafe { &*leaf.keys[i].as_ptr() }
                        );
                    }
                    assert!(leaf.refs[i].is_some());

                    least_lim = unsafe { Some(&*leaf.keys[i].as_ptr()) };
                }
                (1, leaf.key_count as usize)
            }
        }
    }
}

#[cfg(test)]
mod test {
    use super::KVMap;
    use rand::{thread_rng, Rng};

    #[test]
    fn update_basic() {
        // A simple test that tests if updates do what we expect
        let map = KVMap::new();
        let mut write = map.write();
        write.update(65, 65);
        write.update(2, 2);
        write.update(1000, 1000);
        write.check_bptree_properties(3);
        // Check that a read snapshot doesn't have the data before it is
        // committed.
        let mut read = map.read();
        assert!(read.search(&2).is_none());
        assert!(read.search(&65).is_none());
        assert!(read.search(&1000).is_none());
        assert_eq!(65, *write.search(&65).unwrap());
        write.commit();

        write = map.write();
        for i in 5..120 {
            write.update(i, i * 4);
        }
        // State after first commit
        read = map.read();
        write.check_bptree_properties(117);
        read.check_bptree_properties(3);

        write.commit();
        // State after the second commit
        read = map.read();
        read.check_bptree_properties(117);
        assert_eq!(2, *read.search(&2).unwrap());
        assert_eq!(1000, *read.search(&1000).unwrap());
        for i in 5..120 {
            assert_eq!(i * 4, *read.search(&i).unwrap());
        }
    }

    // Checks that a record for a key is what we expect
    macro_rules! check_record {
        ($record:expr, $expected:expr, $iter:expr) => {
            match $expected {
                // Expecting no record, assert there realy is none
                0 => assert_eq!(
                    $record,
                    None,
                    "Unexpected record for key {}. Key hasn't been inserted. Record is {:?}",
                    $iter,
                    $record.unwrap()
                ),
                // Expected key "e"
                e => match $record {
                    // No record at all
                    None => panic!(
                        "Key {} has been inserted, but no record for it was received",
                        $iter
                    ),
                    // Check it is indeed the right key-value pair
                    Some(rec) => assert_eq!(
                        *rec,
                        ($iter as u32, e),
                        "Unexpected record. Expected ({}, {}), received ({}, {})",
                        $iter,
                        e,
                        rec.0,
                        rec.1,
                    ),
                },
            }
        };
    }

    #[test]
    fn update_random() {
        // Randomized test of the behavior for updates only.
        let mut rng = thread_rng();
        let map = KVMap::new();
        let mut write;
        let mut count = 0;
        // We keep this record of what keys should currently be present
        let mut member = [0; 1000];
        for _ in 0..30 {
            // Write randomized records to the tree
            write = map.write();
            for i in 1..31 {
                let key = rng.gen_range(0, 1000);
                if member[key as usize] == 0 {
                    count += 1;
                }
                write.update(key, (key, i));
                member[key as usize] = i;
                write.check_bptree_properties(count);
            }
            write.commit();
            // Check there are exactly the inserted records
            let read = map.read();
            for i in 0..1000 {
                let record = read.search(&(i as u32));
                check_record!(record, member[i], i);
            }
            map.read().check_bptree_properties(count);
        }
    }

    #[test]
    fn remove_basic() {
        // A simple test of the remove method's functionality
        let map = KVMap::new();
        let mut write = map.write();
        write.update(1, 4);
        write.update(50, 200);
        write.update(100, 400);
        write.check_bptree_properties(3);
        assert!(map.read().search(&1).is_none());
        assert_eq!(4, *write.search(&1).unwrap());
        assert_eq!(400, *write.search(&100).unwrap());
        // After ensuring records have been written correctly, remove some
        write.remove(&1);
        write.check_bptree_properties(2);
        write.remove(&100);
        write.check_bptree_properties(1);
        assert!(write.search(&1).is_none());
        assert!(write.search(&100).is_none());

        // New record and a modification
        for i in 40..61 {
            write.update(i, i);
        }
        let mut count = 21;

        write.commit();
        // Check with a read snapshot
        let mut read = map.read();
        read.check_bptree_properties(count);
        assert_eq!(50, *read.search(&50).unwrap());

        // Several other removals
        write = map.write();
        let mut i = 40;
        while i < 61 {
            write.remove(&i);
            count -= 1;
            i += 2;
            write.check_bptree_properties(count);
        }
        write.commit();
        // Again, ensure remove performed correctly
        read = map.read();
        i = 41;
        while i < 61 {
            assert!(read.search(&(i - 1)).is_none());
            assert_eq!(i, *read.search(&i).unwrap());
            i += 2;
        }

        // Final iteration of the process
        write = map.write();
        i = 41;
        while i < 61 {
            write.remove(&i);
            count -= 1;
            i += 2;
            write.check_bptree_properties(count);
        }
        write.update(20, 20);
        write.check_bptree_properties(1);
    }

    #[test]
    fn remove_random() {
        // Randomized test for `remove`
        let mut rng = thread_rng();
        let map = KVMap::new();
        let mut write;
        let mut count = 0;
        // We keep this record of what keys should currently be present
        let mut member = [0; 1000];
        for i in 0..8 {
            // Perform randomized updates/removes with the write handle
            write = map.write();
            for j in 1..550 {
                let key = rng.gen_range(0, 1000);
                let choice = rng.gen_range(0, 3 + i);
                if choice < 3 {
                    // update
                    if member[key as usize] == 0 {
                        count += 1;
                    }
                    write.update(key, (key, j));
                    member[key as usize] = j;
                } else {
                    // remove
                    if member[key as usize] != 0 {
                        count -= 1;
                    }
                    write.remove(&key);
                    member[key as usize] = 0;
                }
                write.check_bptree_properties(count);
            }
            write.commit();
            // After commit, check exactly the expected records are present
            let read = map.read();
            for j in 0..1000 {
                let record = read.search(&(j as u32));
                check_record!(record, member[j], j);
            }
        }
        map.read().check_bptree_properties(count);
    }
}
