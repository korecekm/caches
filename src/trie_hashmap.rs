use ahash::AHasher;
use std::hash::Hash;
use std::hash::Hasher;
use std::mem;
use std::sync::{Arc, Mutex, MutexGuard};

// A concurrently readable, transactional key-value map.
// # Sequential DS description:
// Our trie works as an 8-ary postfix tree, where nodes at depth D have 8
// children corresponding to the possible values of the D-th LEAST significant
// bit triplet in a key's hash. Leaf node's children are vectors of key-value
// pairs, where the actual records are held. These leaves are at a fixed depth
// 5 (which also means that we aren't using the full extent of the hash).
// The selected trie properties, ie number of significant hash bits for each
// node and the tree depth, may be changed using the constants following the
// hash macro definition (no other changes needed).
// Note: this design lets us only hold 8 references in each node and nothing
// more (except transaction id as we'll see) and seems to be a very accurate
// tree-based extension of the classical hash table implementations.
// # EXAMPLE: search for value with key K:
// 1) Hash K using the hash macro (let H := hash!(K))
// 2) let (current) node be the root node and current depth be 1
//    - if root is None, return None, because there are no records at all
// 3) ITERATE DEPTH TIMES: Apply a three-bit mask to the (3*depth)-th least
//    significant bits of H to determine the order of the child to 'recurse' to
//    -> the current node (or rather the found Vec if we're at final depth)
//       will now be determined as the child at the found order in current node
//       ( return None if this child is unset )
// 4) We now hold a Vec of (key, value) pairs (in no particular order), simply
//    search for the pair with key == K, if present.
// # Transactional (and concurently readable) extension:
// We take advantage of the ATOMIC reference counting. Each node now also holds
// its transaction id (txid) and also the leaf-child vectors are stored in
// pairs of the form (txid, Vec).
// Every mutating function (ie update, remove in the WriteTxn) clones the whole
// path it traverses, that doesn't hold this transaction's txid, making it hold
// this txid. This way, only nodes newly created by this write transaction
// (with current txid) are ever modified and the Nodes with 'older' transaction
// IDs stay unmodified for any read transactions.
//
// # What we assume:
// - a good hash function
// - a fixed amount of stored values corresponding to the 8^5 maximum stored
//   key-value pair vectors, so that collisions aren't too likely

// Uses AHasher to get a u32 hash for given key
macro_rules! hash {
    ($k:expr) => {{
        let mut hasher = AHasher::new_with_keys(3, 7);
        $k.hash(&mut hasher);
        ((hasher.finish() % 0x100000000) as u32)
    }};
}

// (used by Iterator logic)
macro_rules! new_ptr {
    ($from:expr) => {{
        Box::into_raw(Box::new($from))
    }};
}

const DEPTH: usize = 5; // how many nodes until we reach Vec
const BIT_COUNT: usize = 3; // the number of bits that are significant for each node
const MASK: u32 = 0x7; // BIT_COUNT ones to use as a mask
const CHILD_COUNT: usize = 8; // 2^BIT_COUNT (= the number of Refs in each node)

#[derive(Clone)]
struct Branch<K, V>
where
    K: Eq + Hash + Clone,
    V: Clone,
{
    txid: u32,
    refs: [Ref<K, V>; CHILD_COUNT],
}
#[derive(Clone)]
struct Leaf<K, V>
where
    K: Eq + Hash + Clone,
    V: Clone,
{
    txid: u32,
    refs: [Elem<K, V>; CHILD_COUNT],
}

#[derive(Clone)]
enum Node<K, V>
where
    K: Eq + Hash + Clone,
    V: Clone,
{
    Branch(Branch<K, V>),
    Leaf(Leaf<K, V>),
}

type Ref<K, V> = Option<Arc<Node<K, V>>>;
// elem also holds txid (the u32 in the tuple)
type Elem<K, V> = Option<Arc<(u32, Vec<(K, V)>)>>;

/// A concurrently readable, transactional key-value hash map.
///
/// TrieMap itself works only as an immutable handle. Modifications to the map
/// need to be done via TMWriteTxn write transactions and are only recorded
/// permanently once the transactions are commited (only one write transaction
/// is allowed at a time).
///
/// TMReadTxn read transactions provide snapshots to the current state of the
/// hash map, ie. they enable you to search through the records as they were at
/// the point of the transaction's creation.
///
/// the read and write transactions may be generated via the `read()` and
/// `write()` functions, respectively.
///
/// Currently, both the read and write txns provide two read-only operations:
/// * search(&key): gives an (immutable) reference to the value corresponding to
///   this key
/// * `iter_keys()`: generates an iterator giving (immutable) references to all
///   the recorded keys; this essentially works as a random iteration through
///   the keys
///
/// The write transaction also provides these modifying operations:
/// * `update(key, value)`: updates a value for given key, or inserts it into
///   the map if it isn't recorded already
/// * `remove(&key)`: removes given key's record inside the tree (or does
///   nothing it isn't recorded)
///
/// ## Example:
/// ```
/// let map = TrieMap::new();
///
/// // create a TMWriteTxn handle to be able to modify the map
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
/// // the data
/// assert!(map.read().search(&"second").is_none());
///
/// // commit the write transaction:
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
pub struct TrieMap<K, V>
where
    K: Eq + Hash + Clone,
    V: Clone,
{
    root: Mutex<Ref<K, V>>,
    write: Mutex<()>,
}

pub struct TMReadTxn<K, V>
where
    K: Eq + Hash + Clone,
    V: Clone,
{
    root: Ref<K, V>,
}

pub struct TMWriteTxn<'a, K, V>
where
    K: Eq + Hash + Clone,
    V: Clone,
{
    txid: u32,
    caller: &'a TrieMap<K, V>,
    root: Ref<K, V>,
    _guard: MutexGuard<'a, ()>,
}

unsafe impl<K: Eq + Hash + Clone, V: Clone> Send for TrieMap<K, V>
{
}
unsafe impl<K: Eq + Hash + Clone, V: Clone> Sync for TrieMap<K, V>
{
}

// IMPLEMENTATION:

impl<K, V> TrieMap<K, V>
where
    K: Eq + Hash + Clone,
    V: Clone,
{
    /// Generate an empty TrieMap handle.
    pub fn new() -> Self {
        Self {
            root: Mutex::new(None),
            write: Mutex::new(()),
        }
    }

    /// Generate a read transaction for the current map state.
    pub fn read(&self) -> TMReadTxn<K, V> {
        TMReadTxn {
            root: match &*self.root.lock().unwrap() {
                None => None,
                Some(arc) => Some(Arc::clone(arc)),
            },
        }
    }

    /// Generate a write transaction enabling to modify the map.
    ///
    /// If another write transaction is still active, this will wait for it to
    /// get committed or rolled back.
    pub fn write(&self) -> TMWriteTxn<K, V> {
        let guard = self.write.lock().unwrap();
        self.prepare_write_txn(guard)
    }

    /// Generates a write transaction enabling to modify the map, but only if
    /// there is no other write transaction currently active.
    pub fn try_write(&self) -> Option<TMWriteTxn<K, V>> {
        let guard = self.write.try_lock();
        match guard {
            Err(_) => None,
            Ok(guard) => Some(self.prepare_write_txn(guard)),
        }
    }

    fn prepare_write_txn<'a>(&'a self, write_guard: MutexGuard<'a, ()>) -> TMWriteTxn<K, V> {
        let root = &*self.root.lock().unwrap();
        let txid = match root {
            None => 0,
            Some(arc) => match &**arc {
                Node::Leaf(ref leaf) => leaf.txid + 1,
                Node::Branch(ref branch) => branch.txid + 1,
            },
        };
        TMWriteTxn {
            txid,
            caller: self,
            root: match root {
                None => None,
                Some(arc) => Some(Arc::clone(arc)),
            },
            _guard: write_guard,
        }
    }
}

impl<K, V> TMReadTxn<K, V>
where
    K: Eq + Hash + Clone,
    V: Clone,
{
    pub fn search(&self, key: &K) -> Option<&V> {
        let vec = Node::find_vec(&self.root, hash!(key));
        match vec {
            None => None,
            Some(vec) => Node::search_in_vec(vec, key),
        }
    }

    pub fn iter_keys<'a>(&'a self) -> TMKeyIter<'a, K, V> {
        TMKeyIter::new(&self.root)
    }
}

impl<'a, K, V> TMWriteTxn<'a, K, V>
where
    K: Eq + Hash + Clone,
    V: Clone,
{
    pub fn search(&self, key: &K) -> Option<&V> {
        let vec = Node::find_vec(&self.root, hash!(key));
        match vec {
            None => None,
            Some(vec) => Node::search_in_vec(vec, key),
        }
    }

    pub fn iter_keys(&'a self) -> TMKeyIter<'a, K, V> {
        TMKeyIter::new(&self.root)
    }

    pub fn update(&mut self, key: K, val: V) {
        let hash = hash!(key);
        // If root isn't yet stored, create a new one, otherwise clone or use
        // the stored one, based on its txid
        let mut mut_arc = match &self.root {
            None => Arc::new(Node::empty_branch(self.txid)),
            Some(_) => Node::modify_node(mem::take(&mut self.root).unwrap(), self.txid),
        };
        // Now update the inside the root that we know can be modified.
        // Last parameter specifies the zero*3 shifts needed for our three-bit
        // mask at current depth (= 1).
        Node::update(&mut mut_arc, key, val, hash, 0);
        self.root = Some(mut_arc);
    }

    pub fn remove(&mut self, key: &K) {
        let hash = hash!(key);
        // see if key's present:
        let vec = Node::find_vec(&self.root, hash);
        if let Some(vec) = vec {
            if Node::search_in_vec(vec, key).is_some() {
                // perform remove
                let update_arc = mem::take(&mut self.root).unwrap();
                self.root = Node::remove(update_arc, key, hash, self.txid, 0);
            }
        }
    }

    /// Commit the changes done with this write transaction.
    /// 
    /// If you wish to roll the changes back, simpy have the TMWriteTxn handle
    /// dropped.
    pub fn commit(self) {
        *self.caller.root.lock().unwrap() = self.root;
    }
}

impl<K, V> Node<K, V>
where
    K: Eq + Hash + Clone,
    V: Clone,
{
    fn empty_branch(txid: u32) -> Self {
        Self::Branch(Branch {
            txid,
            refs: Default::default(),
        })
    }

    fn empty_leaf(txid: u32) -> Self {
        Self::Leaf(Leaf {
            txid,
            refs: Default::default(),
        })
    }

    /// if given Node (Arc) has given txid, it is returned as is.
    /// Otherwise, the whole Node gets cloned with the given txid and a reference
    /// to this clone is returned
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

    /// The part of a search that traverses the whole trie and gets to the
    /// corresponding Vec (or hits a None)
    fn find_vec(root: &Ref<K, V>, hash: u32) -> Option<&Vec<(K, V)>> {
        let mut node = root;
        let mut depth = 0;
        while depth < DEPTH {
            let idx = ((hash >> (depth * BIT_COUNT)) & MASK) as usize;
            match node {
                None => return None,
                Some(arc) => match &**arc {
                    Self::Branch(ref branch) => {
                        debug_assert!(depth != DEPTH - 1, "Invalid state: branch node found at maximum depth, where only leaf nodes are allowed.");
                        node = &branch.refs[idx];
                    }
                    Self::Leaf(ref leaf) => {
                        debug_assert!(
                            depth == DEPTH - 1,
                            "Invalid state: leaf node found at non-maximum depth."
                        );
                        match &leaf.refs[idx] {
                            None => return None,
                            Some(arc_vec) => return Some(&(**arc_vec).1),
                        }
                    }
                },
            }
            depth += 1;
        }
        panic!("Unreachable.");
    }

    /// Searches through a (K, V)-pair Vec for a pair, where K == key.
    /// If found, &V gets returned.
    fn search_in_vec<'a>(vec: &'a Vec<(K, V)>, key: &K) -> Option<&'a V> {
        for (k, v) in vec.iter() {
            if k == key {
                return Some(&v);
            }
        }
        None
    }

    fn update(node: &mut Arc<Node<K, V>>, key: K, val: V, hash: u32, depth: usize) {
        // Given Arc always has the right txid and may therefore be modified.
        let idx = ((hash >> (depth * BIT_COUNT)) & MASK) as usize;
        match Arc::get_mut(node).unwrap() {
            Node::Branch(ref mut branch) => {
                debug_assert!(
                    depth < DEPTH - 1,
                    "Invalid state: update ran into a branch node at leaf depth."
                );
                match branch.refs[idx] {
                    None => {
                        let mut new_ref = Arc::new(if depth == DEPTH - 2 {
                            Node::empty_leaf(branch.txid)
                        } else {
                            Node::empty_branch(branch.txid)
                        });
                        Self::update(&mut new_ref, key, val, hash, depth + 1);
                        branch.refs[idx] = Some(new_ref)
                    }
                    Some(_) => {
                        let mut arc = Node::modify_node(
                            mem::take(&mut branch.refs[idx]).unwrap(),
                            branch.txid,
                        );
                        Self::update(&mut arc, key, val, hash, depth + 1);
                        branch.refs[idx] = Some(arc);
                    }
                }
            }
            Node::Leaf(ref mut leaf) => {
                debug_assert!(
                    depth == DEPTH - 1,
                    "Invalid state: update ran into a leaf node in low depth."
                );
                match leaf.refs[idx] {
                    None => leaf.refs[idx] = Some(Arc::new((leaf.txid, vec![(key, val)]))),
                    Some(ref mut arc) => {
                        let (txid, old_vec) = &**arc;
                        if *txid == leaf.txid {
                            Self::update_in_vec(&mut Arc::get_mut(arc).unwrap().1, key, val);
                        } else {
                            let mut new_ref = Arc::new((leaf.txid, old_vec.clone()));
                            Self::update_in_vec(
                                &mut (*Arc::get_mut(&mut new_ref).unwrap()).1,
                                key,
                                val,
                            );
                            leaf.refs[idx] = Some(new_ref);
                        }
                    }
                }
            }
        }
    }

    fn update_in_vec(vec: &mut Vec<(K, V)>, key: K, val: V) {
        for elem in vec.iter_mut() {
            if elem.0 == key {
                elem.1 = val;
                return;
            }
        }
        vec.push((key, val));
    }

    fn remove(mut node: Arc<Node<K, V>>, key: &K, hash: u32, txid: u32, depth: usize) -> Ref<K, V> {
        // node is not given as a &mut Arc as in update, but as an actual consumed Arc, which doesn't
        // necessarily hold current txid (that's so we don't preemptively clone a node just to make
        // it None)
        let idx = ((hash >> (depth * BIT_COUNT)) & MASK) as usize;
        match &*node {
            Node::Branch(ref branch) => {
                debug_assert!(
                    depth < DEPTH - 1,
                    "Invalid state: remove ran into a branch node at leaf depth."
                );
                // We want to call Self::remove on the corresponding child, and if that becomes None, while being
                // the last Some value among the children, None shall be returned (as this node would otherwise
                // just be a dead end).
                // However, we can't just access the refs, because they are behind an Arc and the assumption we
                // are working with a branch node needs to be done again, too.
                // So we first make an intermediate Arc where Self::removed is applied on the right child.
                let intermediate = if branch.txid == txid {
                    let mut_node = Arc::get_mut(&mut node).unwrap();
                    if let Node::Branch(ref mut branch) = mut_node {
                        let modify = mem::take(&mut branch.refs[idx]).unwrap();
                        branch.refs[idx] = Self::remove(modify, key, hash, txid, depth + 1);
                        node
                    } else {
                        panic!("Unreachable.");
                    }
                } else {
                    let mut clone = Self::modify_node(node, txid);
                    if let Node::Branch(ref mut branch) = Arc::get_mut(&mut clone).unwrap() {
                        let modify = mem::take(&mut branch.refs[idx]).unwrap();
                        branch.refs[idx] = Self::remove(modify, key, hash, txid, depth + 1);
                        clone
                    } else {
                        panic!("Unreachable.");
                    }
                };
                // Here we check, if by chance the last Some value has been removed:
                if let Node::Branch(ref branch) = &*intermediate {
                    if branch.refs[idx].is_none() {
                        let mut some_count = 0;
                        for elem in &branch.refs {
                            if elem.is_some() {
                                some_count += 1;
                            }
                        }
                        if some_count == 0 {
                            return None;
                        }
                    }
                    // otherwise, we just return the intermediate as is (nonempty recordes are still stored)
                    Some(intermediate)
                } else {
                    panic!("Unreachable.");
                }
            }
            Node::Leaf(ref leaf) => {
                debug_assert!(
                    depth == DEPTH - 1,
                    "Invalid state: remove ran into a leaf node in low depth."
                );
                // First, see if there's just one value in the corresponding value vector
                if leaf.refs[idx].as_ref().unwrap().1.len() < 2 {
                    let mut some_count = 0;
                    for elem in &leaf.refs {
                        if elem.is_some() {
                            some_count += 1;
                        }
                    }
                    // In a leaf node, we don't have to recurse to the child and may check if there's a single
                    // stored value first.
                    if some_count < 2 {
                        return None;
                    }

                    // remove the corresponding vector
                    let mut mut_arc = Self::modify_node(node, txid);
                    let mut_node = Arc::get_mut(&mut mut_arc).unwrap();
                    if let Node::Leaf(ref mut mut_leaf) = mut_node {
                        mut_leaf.refs[idx] = None;
                    } else {
                        panic!("Unreachable.");
                    }
                    return Some(mut_arc);
                }

                // Now there are multiple values in the vector, remove the right one:
                let mut mut_arc = Self::modify_node(node, txid);
                let mut_node = Arc::get_mut(&mut mut_arc).unwrap();
                if let Node::Leaf(ref mut mut_leaf) = mut_node {
                    let vec_txid = &(*mut_leaf.refs[idx].as_ref().unwrap()).0;
                    if *vec_txid == txid {
                        // we may legally mutate this vector
                        let vec = &mut Arc::get_mut(mut_leaf.refs[idx].as_mut().unwrap())
                            .unwrap()
                            .1;
                        // see where the key is stored:
                        let mut key_idx = 0;
                        while vec[key_idx].0 != *key {
                            key_idx += 1;
                        }
                        // now simply remove the element
                        vec[key_idx] = vec[vec.len() - 1].clone();
                        vec.remove(vec.len() - 1);
                    } else {
                        let old_vec = &(*mut_leaf.refs[idx].as_ref().unwrap()).1;
                        let mut new_ref = Arc::new((txid, Vec::with_capacity(old_vec.len() - 1)));
                        let new_vec = &mut (*Arc::get_mut(&mut new_ref).unwrap()).1;
                        for elem in old_vec {
                            if elem.0 != *key {
                                new_vec.push(elem.clone());
                            }
                        }
                        mut_leaf.refs[idx] = Some(new_ref);
                    }
                } else {
                    panic!("Unreachable.");
                }
                Some(mut_arc)
            }
        }
    }
}

// iterator logic:

// The Iter basically simulates a recursive iter function. There are three
// states corresponding to iteration states, BranchIter, LeafIter and ElemIter.
// Each has a reference to the corresponding node (a Vec in the case of
// ElemIter, ie. basically the actual leaf node in our structure)
//
// All three of these IterStates hold values as so: (index, &ref, *mut parent_state),
// which represents the current index to be processed in the referenced structure,
// ref: the reference itself, and a mutable ptr to the parent state.
//
// This essentially provides a stack simulating the recursion, as stated. The
// 'root' state is always IterState::Done, which lets us know iteration is
// complete.

enum IterState<'a, K, V>
where
    K: Eq + Hash + Clone,
    V: Clone,
{
    Done,
    BranchIter(usize, &'a Branch<K, V>, *mut IterState<'a, K, V>),
    LeafIter(usize, &'a Leaf<K, V>, *mut IterState<'a, K, V>),
    ElemIter(usize, &'a Vec<(K, V)>, *mut IterState<'a, K, V>),
}

pub struct TMKeyIter<'a, K, V>
where
    K: Eq + Hash + Clone,
    V: Clone,
{
    state: *mut IterState<'a, K, V>,
}

impl<'a, K, V> TMKeyIter<'a, K, V>
where
    K: Eq + Hash + Clone,
    V: Clone,
{
    // generate the beginning of the simulated stack, ie. first of all an
    // IterState::Done 'node', and if provided $root is Some, also a
    // connected (having the Done as a parent node) corresponding to the root
    // node's type (branch or leaf).
    fn new(root: &'a Ref<K, V>) -> Self {
        let done_ptr = new_ptr!(IterState::Done);
        Self {
            state: match root {
                None => done_ptr,
                Some(ref node) => {
                    match &**node {
                        Node::Branch(ref branch) => new_ptr!(IterState::BranchIter(0, branch, done_ptr)),
                        Node::Leaf(ref leaf) => new_ptr!(IterState::LeafIter(0, leaf, done_ptr)),
                    }
                }
            }
        }
    }

    // responsible for calling the correct type of iteration behavior
    fn next_key(&mut self) -> Option<&'a K> {
        match unsafe { &mut *self.state } {
            IterState::Done => None,
            IterState::BranchIter(ref mut idx, branch, parent) => self.branch_next(branch, idx, *parent),
            IterState::LeafIter(ref mut idx, leaf, parent) => self.leaf_next(leaf, idx, *parent),
            IterState::ElemIter(ref mut idx, vec, parent) => self.elem_next(vec, idx, *parent),
        }
    }

    fn branch_next(&mut self, branch: &'a Branch<K, V>, idx: &mut usize, parent: *mut IterState<'a, K, V>) -> Option<&'a K> {
        // find the first index in line that isn't None
        while *idx < CHILD_COUNT {
            *idx += 1;
            // a Some child node was find, simulate recursion into it:
            if let Some(ref arc_node) = branch.refs[*idx - 1] {
                self.state = match &**arc_node {
                    Node::Branch(ref branch) => new_ptr!(IterState::BranchIter(0, branch, self.state)),
                    Node::Leaf(ref leaf) => new_ptr!(IterState::LeafIter(0, leaf, self.state)),
                };
                return self.next_key();
            }
        }
        // All child nodes have been processed:

        // free the space taken by the current IterState struct
        unsafe {
            Box::from_raw(self.state);
        }
        // bactrack to the parent state (either branch state, or Done, if this branch is the map's root)
        self.state = parent;
        self.next_key()
    }

    fn leaf_next(&mut self, leaf: &'a Leaf<K, V>, idx: &mut usize, parent: *mut IterState<'a, K, V>) -> Option<&'a K> {
        // find the first index in line that isn't None
        while *idx < CHILD_COUNT {
            *idx += 1;
            if let Some(ref arc_elem) = leaf.refs[*idx - 1] {
                // a Some child vector was find, simulate recursion into it:
                let (_, ref vec) = &**arc_elem;
                self.state = new_ptr!(IterState::ElemIter(
                    0, vec, self.state
                ));
                return self.next_key();
            }
        }
        // All child vectors have been processed:

        // free the space taken by the current IterState struct
        unsafe {
            Box::from_raw(self.state);
        }
        // backtrack to the parent state (branch node state)
        self.state = parent;
        self.next_key()
    }

    fn elem_next(&mut self, elems: &'a Vec<(K, V)>, idx: &mut usize, parent: *mut IterState<'a, K, V>) -> Option<&'a K> {
        if *idx < elems.len() {
            // if any element hasn't yet been returned return it and increase the idx
            *idx += 1;
            Some(&elems[*idx - 1].0)
        } else {
            // all elements in this vector have already been returned:

            // free the space taken by the current IterState struct
            unsafe {
                Box::from_raw(self.state);
            }
            // backtrack to the parent state (leaf node state)
            self.state = parent;
            self.next_key()
        }
    }
}

impl<'a, K, V> Iterator for TMKeyIter<'a, K, V>
where
    K: Eq + Hash + Clone,
    V: Clone,
{
    type Item = &'a K;
    
    fn next(&mut self) -> Option<Self::Item> {
        self.next_key()
    }
}

impl<'a, K, V> Drop for TMKeyIter<'a, K, V>
where
    K: Eq + Hash + Clone,
    V: Clone,
{
    fn drop(&mut self) {
        let mut current = self.state;
        loop {
            let current_box = unsafe {
                Box::from_raw(current)
            };
            current = match &*current_box {
                IterState::Done => return,
                IterState::BranchIter(_, _, parent) => *parent,
                IterState::LeafIter(_, _, parent) => *parent,
                _ => panic!("Unreachable."),  // ElemIter never becomes a parent node
            };
        }
    }
}


// TESTS:

#[cfg(test)]
mod test {
    use super::TrieMap;
    use rand::{thread_rng, Rng};

    #[test]
    fn update_basic() {
        let map = TrieMap::new();
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

    #[test]
    fn remove_basic() {
        let map = TrieMap::new();
        let mut write = map.write();
        for i in 6..11 {
            write.update(i, ());
        }
        write.remove(&8);
        assert!(write.search(&7).is_some());
        assert!(write.search(&8).is_none());
        assert!(write.search(&9).is_some());
        write.commit();

        write = map.write();
        write.remove(&6);
        write.remove(&10);
        write.update(8, ());
        let read = map.read();
        for i in 6..11 {
            if i == 8 {
                assert!(read.search(&i).is_none());
            } else {
                assert!(read.search(&i).is_some());
            }
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
                        ($key as u32, e),
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

    // In the randomized tests, we generate random keys out of a 0..count range
    // and record separately which elements should be present into a (count-sized)
    // array; this macro receives a reference to a transaction struct (no matter
    // read or write, it uses only search functions, which both have), the array
    // of records (named members) and the count parameters (giving the range of
    // keys we shall check)
    // the macro then makes a search query sequentially for each key of given
    // range and compares the result to what's in $members. values are tuples of
    // the form (key, members[key]) and should be missing when members[key] is 0
    // ((_, 0) is never stored in the map)
    macro_rules! check_all {
        ($txn:expr, $members:expr, $count: expr) => {
            for j in 0..$count {
                let record = $txn.search(&(j as u32));
                check_one!($members[j], &record, j);
            }
        };
    }

    #[test]
    fn random_update() {
        let mut rng = thread_rng();
        let map: TrieMap<u32, (u32, usize)> = TrieMap::new();
        let mut member = [[0; 5000]; 2];
        let mut member_idx = 0;
        let mut write = map.write();
        for i in 0..3 {
            for j in 1..2000 {
                let key = rng.gen_range(0, 5000);
                let choice = rng.gen_range(0, 4 + i);
                if choice < 4 {
                    // update
                    write.update(key, (key, j));
                    member[member_idx][key as usize] = j;
                } else {
                    // search
                    let record = write.search(&key);
                    check_one!(member[member_idx][key as usize], &record, key);
                }
            }
            let read = map.read();
            check_all!(&write, &member[member_idx], 5000);
            member_idx = switch_idx(member_idx);
            check_all!(&read, &member[member_idx], 5000);
            write.commit();
            write = map.write();
            member[member_idx] = member[switch_idx(member_idx)].clone();
        }
        let read = map.read();
        check_all!(&read, &member[switch_idx(member_idx)], 5000);
    }

    #[test]
    fn random_general() {
        let mut rng = thread_rng();
        let map: TrieMap<u32, (u32, usize)> = TrieMap::new();
        let mut member = [[0; 5000]; 2];
        let mut member_idx = 0;
        let mut write = map.write();
        for i in 0..8 {
            for j in 1..2000 {
                let key = rng.gen_range(0, 5000);
                let choice = rng.gen_range(0, 5 + i);
                if choice == 0 {
                    // commit
                    member_idx = switch_idx(member_idx);
                    let read = map.read();
                    // check that no changes leaked into a fresh read txn:
                    check_all!(&read, &member[member_idx], 5000);
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
            check_all!(&write, &member[member_idx], 5000);
        }
    }

    fn switch_idx(idx: usize) -> usize {
        if idx == 0 {
            1
        } else {
            0
        }
    }

    #[test]
    fn iter_keys() {
        let mut rng = thread_rng();
        // check a couple shorter iterations
        for _ in 0..20 {
            perform_iter_keys_test(rng.gen_range(1, 300));
        }
        // check a longer one
        perform_iter_keys_test(30000);
    }

    fn perform_iter_keys_test(count: usize) {
        let map = TrieMap::new();
        let mut write = map.write();
        for i in 0..count {
            write.update(i, ());
        }
        write.commit();

        let mut success_count = 0;
        let mut hit = vec![false; count];
        for key_ref in map.read().iter_keys() {
            assert!(!hit[*key_ref as usize], "Key {} was retrieved more than once", *key_ref);
            hit[*key_ref as usize] = true;
            success_count += 1;
        }
        assert_eq!(count, success_count, "Only {} keys were retrieved", success_count);
    }
}
