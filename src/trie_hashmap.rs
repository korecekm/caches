use ahash::AHasher;
use std::hash::Hash;
use std::hash::Hasher;
use std::mem;
use std::sync::{Arc, Mutex, MutexGuard};

macro_rules! hash {
    ($k:expr) => {{
        let mut hasher = AHasher::new_with_keys(3, 7);
        $k.hash(&mut hasher);
        ((hasher.finish() % 0x100000000) as u32)
    }};
}

const DEPTH: usize = 5; // how many nodes until we reach Vec
const BIT_COUNT: usize = 3; // the number of bits that are significant for each node
const MASK: u32 = 0x7; // BIT_COUNT ones to use as a mask
const CHILD_COUNT: usize = 8; // 2^BIT_COUNT (= the number of Refs in each node)

// TODO optimize alignment
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

// IMPLEMENTATION:
impl<K, V> TrieMap<K, V>
where
    K: Eq + Hash + Clone,
    V: Clone,
{
    pub fn new() -> Self {
        Self {
            root: Mutex::new(None),
            write: Mutex::new(()),
        }
    }

    pub fn read(&self) -> TMReadTxn<K, V> {
        TMReadTxn {
            root: match &*self.root.lock().unwrap() {
                None => None,
                Some(arc) => Some(Arc::clone(arc)),
            },
        }
    }

    pub fn write(&self) -> TMWriteTxn<K, V> {
        let guard = self.write.lock().unwrap();
        self.prepare_write_txn(guard)
    }

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

    pub fn update(&mut self, key: K, val: V) {
        let hash = hash!(key);
        let mut mut_arc = match &self.root {
            None => Arc::new(Node::empty_branch(self.txid)),
            Some(_) => Node::modify_node(mem::take(&mut self.root).unwrap(), self.txid),
        };
        Node::update(&mut mut_arc, key, val, hash, 0);
        self.root = Some(mut_arc);

        /*
        self.root = Some(match &self.root {
            None => {
                let mut new_arc = Arc::new(Node::empty_branch(self.txid));
                Node::update(&mut new_arc, key, val, hash, 0);
                new_arc
            }
            Some(_) => {
                let mut update_arc = Node::modify_node(mem::take(&mut self.root).unwrap(), self.txid);
                Node::update(&mut update_arc, key, val, hash, 0);
                update_arc
            }
        });*/
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
    /*
        pub fn remove(&mut self, key: &K) {
            let hash = hash!(key);
            let vec = Node::find_vec(&self.root, hash);
            if let Some(vec) = &vec {
                if Node::search_in_vec(vec, key).is_none() {
                    return;
                }
                if vec.len() < 2 {
                    let update_arc = mem::take(&mut self.root).unwrap();
                    self.root = Node::remove_path(update_arc, self.txid, hash, 0);
                    if self.root.is_none() {
                        self.txid = 0;
                    }
                } else {
                    let mut update_arc = Node::modify_node(mem::take(&mut self.root).unwrap(), self.txid);
                    Node::clone_and_remove(&mut update_arc, key, hash, 0);
                    self.root = Some(update_arc);
                }
            }
        }
    */
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

    fn search_in_vec<'a>(vec: &'a Vec<(K, V)>, key: &K) -> Option<&'a V> {
        for (k, v) in vec.iter() {
            if k == key {
                return Some(&v);
            }
        }
        None
    }

    fn update(node: &mut Arc<Node<K, V>>, key: K, val: V, hash: u32, depth: usize) {
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

    // when removing by key, we first see whether the containing Vec has just
    // one element, if yes, we call remove_path, which simply removes the
    // references and (if all refs are turned to None) Nodes on the path to
    // given hash;
    // if the Vec is longer, we call clone_and_remove, which simply clones the
    // path according to given txid and removec the key from the Vec
    // !! the Arc received by remove_path doesn't necessarily have required txid
    fn remove_path(mut node: Arc<Node<K, V>>, txid: u32, hash: u32, depth: usize) -> Ref<K, V> {
        let idx = ((hash >> (depth * BIT_COUNT)) & MASK) as usize;
        match &*node {
            Node::Branch(ref branch) => {
                debug_assert!(
                    depth < DEPTH - 1,
                    "Invalid state: remove ran into a branch node at leaf depth."
                );
                let intermediate = if branch.txid == txid {
                    let mut_node = Arc::get_mut(&mut node).unwrap();
                    if let Node::Branch(ref mut branch) = mut_node {
                        let modify =
                            Self::modify_node(mem::take(&mut branch.refs[idx]).unwrap(), txid);
                        branch.refs[idx] = Self::remove_path(modify, txid, hash, depth + 1);
                        node
                    } else {
                        panic!("Unreachable.");
                    }
                } else {
                    let mut clone = Self::modify_node(node, txid);
                    if let Node::Branch(ref mut branch) = Arc::get_mut(&mut clone).unwrap() {
                        let modify = mem::take(&mut branch.refs[idx]).unwrap();
                        branch.refs[idx] = Self::remove_path(modify, txid, hash, depth + 1);
                        clone
                    } else {
                        panic!("Unreachable.");
                    }
                };
                if let Node::Branch(ref branch) = &*intermediate {
                    if branch.refs[idx].is_none() {
                        let mut none_count = 0;
                        for elem in &branch.refs {
                            if elem.is_none() {
                                none_count += 1;
                            }
                        }
                        if none_count == 0 {
                            return None;
                        }
                    }
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
                let mut none_count = 0;
                for elem in &leaf.refs {
                    if elem.is_none() {
                        none_count += 1;
                    }
                }
                if none_count < 2 {
                    None
                } else {
                    if leaf.txid == txid {
                        let mut_node = Arc::get_mut(&mut node).unwrap();
                        if let Node::Leaf(ref mut mut_leaf) = mut_node {
                            mut_leaf.refs[idx] = None;
                        } else {
                            panic!("Unreachable.");
                        }
                        Some(node)
                    } else {
                        let mut clone = Self::modify_node(node, txid);
                        if let Node::Leaf(ref mut clone_leaf) = Arc::get_mut(&mut clone).unwrap() {
                            clone_leaf.refs[idx] = None;
                        } else {
                            panic!("Unreachable.");
                        }
                        Some(clone)
                    }
                }
            }
        }
    }

    fn remove(mut node: Arc<Node<K, V>>, key: &K, hash: u32, txid: u32, depth: usize) -> Ref<K, V> {
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

    fn clone_and_remove(node: &mut Arc<Node<K, V>>, key: &K, hash: u32, depth: usize) {
        let idx = ((hash >> (depth * BIT_COUNT)) & MASK) as usize;
        match Arc::get_mut(node).unwrap() {
            Node::Branch(ref mut branch) => {
                debug_assert!(
                    depth < DEPTH - 1,
                    "Invalid state: remove ran into a branch node at leaf depth."
                );
                let mut arc =
                    Node::modify_node(mem::take(&mut branch.refs[idx]).unwrap(), branch.txid);
                Self::clone_and_remove(&mut arc, key, hash, depth + 1);
                branch.refs[idx] = Some(arc);
            }
            Node::Leaf(ref mut leaf) => {
                debug_assert!(
                    depth == DEPTH - 1,
                    "Invalid state: remove ran into a leaf node in low depth."
                );
                let txid = &(*leaf.refs[idx].as_ref().unwrap()).0;
                if *txid == leaf.txid {
                    let vec = &mut Arc::get_mut(leaf.refs[idx].as_mut().unwrap()).unwrap().1;
                    vec[idx] = vec[vec.len() - 1].clone();
                    vec.remove(vec.len() - 1);
                } else {
                    let old_vec = &(*leaf.refs[idx].as_ref().unwrap()).1;
                    let mut new_ref = Arc::new((leaf.txid, Vec::with_capacity(old_vec.len() - 1)));
                    let mut i = 0;
                    while i < old_vec.len() {
                        if i != idx {
                            (*Arc::get_mut(&mut new_ref).unwrap())
                                .1
                                .push(old_vec[i].clone());
                        }
                        i += 1;
                    }
                    leaf.refs[idx] = Some(new_ref);
                }
            }
        }
    }
}

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
}
