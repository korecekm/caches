use std::ptr;

// Sequential B+ tree
// Each node contains two arrays
// ref_i <= key_i < ref_{i+1}

// !
// For now, working only with a single node size and u32 keys
// !

// This code is meant mainly for practice (although it is a working B+ tree).
// If it were meant for other people to read more thoroughly, it would need to be restructured a bit.
// Also, splits in insert are done via a helper array, which the compiler presumably won't optimize out. For better performance, this may be rewritten to split in place.
// The most important flaw though, is the in memory alignment of the node structs and their exact size to get the most out of the cache.
// (heuristics say about double the cache line is optimal, so often about 128 bytes)

// The maximum number of child nodes
const B_PARAMETER: usize = 10;

// TODO optimize alignment
struct BPTBranch<V> {
    key_count: u8,
    keys: [u32; B_PARAMETER - 1],
    ptrs: [*mut BPTNode<V>; B_PARAMETER],
}
struct BPTLeaf<V> {
    key_count: u8,
    keys: [u32; B_PARAMETER],
    ptrs: [*mut V; B_PARAMETER],
}

enum BPTNode<V> {
    Branch(BPTBranch<V>),
    Leaf(BPTLeaf<V>),
}

// # HOW REMOVE WORKS:
// Aside from the key to be removed in the subtree, a node receives ptrs to its
// left and right neighbor (one of them may be null, but not both);
// If underflow happens, we first try to rotate from the right neighbor, then
// from the left; if neither are possible, neighbors reached lower limit and
// we merge with one of them, first trying merging with the right one, then the
// left; In either case, the node that's called is kept and the merged one
// (right or left) is dropped and its pointer in the parent node can therefore
// be removed without a memory leak occuring.
enum BPTRemoveResponse {
    NoChange,         // underflow didn't occur
    RotateLeft(u32),  // the key to the left should be changed for given value
    RotateRight(u32), // the key on idx corresponding to changed node should change
    MergeLeft,        // node was merged with the one to the left
    MergeRight,       // node was merged with the one to the right
}

struct BPTree<V> {
    root: *mut BPTNode<V>,
}

impl<V> BPTree<V> {
    fn new() -> Self {
        Self {
            root: ptr::null::<BPTNode<V>>() as *mut _,
        }
    }

    /// Tries returning value reference for given key;
    /// Returns None if key wasn't found
    fn search<'a>(&'a self, key: &u32) -> Option<&'a V> {
        if self.root.is_null() {
            None
        } else {
            let mut node = unsafe { &*self.root };
            'outer: loop {
                match node {
                    BPTNode::Branch(ref branch) => {
                        for i in 0..(branch.key_count as usize) {
                            if *key <= branch.keys[i] {
                                unsafe {
                                    node = &*branch.ptrs[i];
                                }
                                continue 'outer;
                            }
                        }
                        unsafe {
                            node = &*branch.ptrs[branch.key_count as usize];
                        }
                    }
                    BPTNode::Leaf(ref leaf) => {
                        for i in 0..(leaf.key_count as usize) {
                            if *key == leaf.keys[i] {
                                unsafe {
                                    return leaf.ptrs[i].as_ref()
                                }
                            }
                        }
                        return None
                    }
                }
            }
        }
    }

    /// Inserts or (if present) updates value for given key
    fn update(&mut self, key: u32, val: V) {
        if self.root.is_null() {
            self.root = BPTNode::init_root(key, val);
        } else {
            if let Some((new_key, right_child)) = unsafe { (*self.root).update(key, val) } {
                self.root = BPTNode::new_root(new_key, self.root, right_child);
            }
        }
    }

    /// Removes record for given key, if present
    fn remove(&mut self, key: &u32) {
        if !self.root.is_null() {
            match unsafe { &mut *self.root } {
                BPTNode::Branch(ref mut branch) => {
                    let mut idx = 0;
                    while idx < branch.key_count as usize && *key > branch.keys[idx] {
                        idx += 1;
                    }
                    let left = if idx == 0 {
                        ptr::null::<BPTNode<V>>() as *mut _
                    } else {
                        branch.ptrs[idx - 1]
                    };
                    let right = if idx < branch.key_count as usize {
                        branch.ptrs[idx + 1]
                    } else {
                        ptr::null::<BPTNode<V>>() as *mut _
                    };
                    let called_node = branch.ptrs[idx];
                    let response = unsafe { (*called_node).remove(key, left, right) };
                    match response {
                        BPTRemoveResponse::RotateLeft(new_key) => branch.keys[idx - 1] = new_key,
                        BPTRemoveResponse::RotateRight(new_key) => branch.keys[idx] = new_key,
                        BPTRemoveResponse::MergeLeft => {
                            // both children were merged
                            if branch.key_count == 1 {
                                unsafe {
                                    Box::from_raw(self.root);
                                }
                                self.root = called_node;
                                return;
                            }
                            // otherwise, just fill formed gap:
                            branch.ptrs[idx - 1] = branch.ptrs[idx];
                            for j in idx..(branch.key_count as usize) {
                                branch.keys[j - 1] = branch.keys[j];
                                branch.ptrs[j] = branch.ptrs[j + 1];
                            }
                            branch.key_count -= 1;
                        }
                        BPTRemoveResponse::MergeRight => {
                            // both children were merged
                            if branch.key_count == 1 {
                                unsafe {
                                    Box::from_raw(self.root);
                                }
                                self.root = called_node;
                                return;
                            }
                            // otherwise, just fill formed gap:
                            for j in idx..(branch.key_count as usize - 1) {
                                branch.keys[j] = branch.keys[j + 1];
                                branch.ptrs[j + 1] = branch.ptrs[j + 2];
                            }
                            branch.key_count -= 1;
                        }
                        _ => {}
                    }
                }
                BPTNode::Leaf(ref mut leaf) => {
                    let mut idx = 0;
                    while idx < leaf.key_count as usize && *key > leaf.keys[idx] {
                        idx += 1;
                    }

                    // no record for given key
                    if idx == leaf.key_count as usize || leaf.keys[idx] != *key {
                        return;
                    }

                    // simply fill the formed gap
                    for j in (idx + 1)..(leaf.key_count as usize) {
                        leaf.keys[j - 1] = leaf.keys[j];
                        leaf.ptrs[j - 1] = leaf.ptrs[j];
                    }
                    leaf.key_count -= 1;
                }
            }
        }
    }

    #[cfg(test)]
    fn check_bptree_properties(&self, expected_record_count: usize) {
        if !self.root.is_null() {
            unsafe {
                let (_, count) = (*self.root).check_bptree_properties(None, None, true);
                assert_eq!(expected_record_count, count,
                    "Tree was expected to hold {} elements. Actually detected {}.", expected_record_count, count);
            }
        }
    }
}

impl<V> BPTNode<V> {
    fn init_root(key: u32, val: V) -> *mut Self {
        let mut root = BPTLeaf {
            key_count: 1,
            keys: [0; B_PARAMETER],
            ptrs: [ptr::null::<V>() as *mut V; B_PARAMETER],
        };
        root.keys[0] = key;
        root.ptrs[0] = Box::into_raw(Box::new(val));
        Box::into_raw(Box::new(BPTNode::Leaf(root)))
    }

    // creates a root node with one key (and two child nodes) after root split
    fn new_root(key: u32, left_child: *mut Self, right_child: *mut Self) -> *mut Self {
        let mut root = BPTBranch {
            key_count: 1,
            keys: [0; B_PARAMETER - 1],
            ptrs: [ptr::null::<BPTNode<V>>() as *mut _; B_PARAMETER],
        };
        root.keys[0] = key;
        root.ptrs[0] = left_child;
        root.ptrs[1] = right_child;
        Box::into_raw(Box::new(BPTNode::Branch(root)))
    }

    /// Inserts or (if present) updates val for given key. If the node is split,
    /// this node will be converted into the left one and a tuple is returned
    /// containing the median key (travelling up) and a pointer to the right node.
    fn update(&mut self, key: u32, val: V) -> Option<(u32, *mut Self)> {
        match self {
            BPTNode::Branch(branch) => {
                let mut idx = 0;
                while idx < (branch.key_count as usize) && key > branch.keys[idx] {
                    idx += 1;
                }
                let child_response = unsafe { (*branch.ptrs[idx]).update(key, val) };
                match child_response {
                    Some((insert_key, right_child)) => {
                        // branch hasn't reached its capacity
                        if (branch.key_count as usize) < B_PARAMETER - 1 {
                            // move larger keys further right
                            for j in (idx..(branch.key_count as usize)).rev() {
                                branch.keys[j + 1] = branch.keys[j];
                                branch.ptrs[j + 2] = branch.ptrs[j + 1];
                            }
                            // store received data
                            branch.keys[idx] = insert_key;
                            branch.ptrs[idx + 1] = right_child;
                            branch.key_count += 1;
                            return None;
                        }

                        // split the node
                        branch.key_count = (B_PARAMETER / 2) as u8;
                        let mut right_branch = BPTBranch {
                            key_count: ((B_PARAMETER / 2) - 1 + (B_PARAMETER % 2)) as u8,
                            keys: [0; B_PARAMETER - 1],
                            ptrs: [ptr::null::<BPTNode<V>>() as *mut _; B_PARAMETER],
                        };
                        let mut all_keys = [0; B_PARAMETER];
                        let mut all_ptrs = [ptr::null::<BPTNode<V>>() as *mut _ ; B_PARAMETER + 1];
                        // all_ptrs[0] = branch.ptrs[0]; // actually not needed
                        for j in 0..idx {
                            all_keys[j] = branch.keys[j];
                            all_ptrs[j + 1] = branch.ptrs[j + 1];
                        }
                        all_keys[idx] = insert_key;
                        all_ptrs[idx + 1] = right_child;
                        for j in idx..(B_PARAMETER - 1) {
                            all_keys[j + 1] = branch.keys[j];
                            all_ptrs[j + 2] = branch.ptrs[j + 1];
                        }

                        for j in idx..(B_PARAMETER / 2) {
                            branch.keys[j] = all_keys[j];
                            branch.ptrs[j + 1] = all_ptrs[j + 1];
                        }
                        right_branch.ptrs[0] = all_ptrs[B_PARAMETER / 2 + 1];
                        for j in (B_PARAMETER / 2 + 1)..B_PARAMETER {
                            right_branch.keys[j - (B_PARAMETER / 2) - 1] = all_keys[j];
                            right_branch.ptrs[j - (B_PARAMETER / 2)] = all_ptrs[j + 1];
                        }

                        Some((all_keys[B_PARAMETER / 2], Box::into_raw(Box::new(BPTNode::Branch(right_branch)))))
                    }
                    None => None,
                }
            }
            BPTNode::Leaf(leaf) => Self::update_in_leaf(leaf, key, val)
        }
    }

    fn update_in_leaf(leaf: &mut BPTLeaf<V>, key: u32, val: V) -> Option<(u32, *mut Self)> {
        let mut idx: usize = 0;
        while idx < (leaf.key_count as usize) && key > leaf.keys[idx] {
            idx += 1;
        }

        // key is already stored
        if idx < (leaf.key_count as usize) && key == leaf.keys[idx] {
            leaf.ptrs[idx] = Box::into_raw(Box::new(val));
            return None;
        }

        // leaf hasn't reached its capacity
        if (leaf.key_count as usize) < B_PARAMETER {
            // move larger keys further 'right'
            for j in (idx..(leaf.key_count as usize)).rev() {
                leaf.keys[j + 1] = leaf.keys[j];
                leaf.ptrs[j + 1] = leaf.ptrs[j];
            }
            // store new data
            leaf.keys[idx] = key;
            leaf.ptrs[idx] = Box::into_raw(Box::new(val));
            leaf.key_count += 1;
            return None;
        }

        // the node needs to be split
        leaf.key_count = ((B_PARAMETER / 2) + 1) as u8;
        let mut right_leaf = BPTLeaf {
            key_count: ((B_PARAMETER / 2) + (B_PARAMETER % 2)) as u8,
            keys: [0; B_PARAMETER],
            ptrs: [ptr::null::<V>() as *mut V; B_PARAMETER],
        };
        let mut all_keys = [0; B_PARAMETER + 1];
        let mut all_ptrs = [ptr::null::<V>() as *mut V; B_PARAMETER + 1];
        for j in 0..idx {
            all_keys[j] = leaf.keys[j];
            all_ptrs[j] = leaf.ptrs[j];
        }
        all_keys[idx] = key;
        all_ptrs[idx] = Box::into_raw(Box::new(val));
        for j in idx..B_PARAMETER {
            all_keys[j + 1] = leaf.keys[j];
            all_ptrs[j + 1] = leaf.ptrs[j];
        }

        for j in idx..((B_PARAMETER / 2) + 1) {
            leaf.keys[j] = all_keys[j];
            leaf.ptrs[j] = all_ptrs[j];
        }
        for j in 0..((B_PARAMETER / 2) + (B_PARAMETER % 2)) {
            right_leaf.keys[j] = all_keys[j + B_PARAMETER / 2 + 1];
            right_leaf.ptrs[j] = all_ptrs[j + B_PARAMETER / 2 + 1];
        }

        Some((all_keys[B_PARAMETER / 2], Box::into_raw(Box::new(BPTNode::Leaf(right_leaf)))))
    }

    fn remove(&mut self, key: &u32, left_neighbor: *mut Self, right_neighbor: *mut Self) -> BPTRemoveResponse {
        match self {
            BPTNode::Branch(ref mut branch) => Self::remove_from_branch(branch, key, left_neighbor, right_neighbor),
            BPTNode::Leaf(ref mut leaf) => Self::remove_from_leaf(leaf, key, left_neighbor, right_neighbor),
        }
    }

    fn remove_from_branch(branch: &mut BPTBranch<V>, key: &u32, left: *mut Self, right: *mut Self) -> BPTRemoveResponse {
        let mut idx = 0;
        while idx < branch.key_count as usize && branch.keys[idx] < *key {
            idx += 1;
        }
        let left_child = if idx == 0 {
            ptr::null::<BPTNode<V>>() as *mut _
        } else {
            branch.ptrs[idx - 1]
        };
        let right_child = if idx < branch.key_count as usize {
            branch.ptrs[idx + 1]
        } else {
            ptr::null::<BPTNode<V>>() as *mut _
        };
        let response = unsafe { (*branch.ptrs[idx]).remove(key, left_child, right_child) };

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
                branch.ptrs[idx - 1] = branch.ptrs[idx];
                for j in idx..(branch.key_count as usize) {
                    branch.keys[j - 1] = branch.keys[j];
                    branch.ptrs[j] = branch.ptrs[j + 1];
                }
            }
            BPTRemoveResponse::MergeRight => {
                for j in idx..(branch.key_count as usize - 1) {
                    branch.keys[j] = branch.keys[j + 1];
                    branch.ptrs[j + 1] = branch.ptrs[j + 2];
                }
            }
        }
        
        // Branch lost a key, if underflow happened, deal with it:
        // The node is now transformed so that it acts as a branch with key_count - 1 keys

        let min_keys = ((B_PARAMETER / 2) + (B_PARAMETER % 2)) as u8;
        // no underflow
        if branch.key_count >= min_keys {
            branch.key_count -= 1;
            return BPTRemoveResponse::NoChange;
        }

        // convert neighbors into Option<&mut Branch> (and assert they are branch nodes)
        let mut l = if !left.is_null() {
            if let BPTNode::Branch(ref mut neighbor) = unsafe { &mut *left } {
                Some(neighbor)
            } else {
                panic!("Invalid remove case: leaf node was provided as a neighbor of a branch node.");
            }
        } else { None };
        let mut r = if !right.is_null() {
            if let BPTNode::Branch(ref mut neighbor) = unsafe { &mut *right } {
                Some(neighbor)
            } else {
                panic!("Invalid remove case: leaf node was provided as a neighbor of a branch node.");
            }
        } else { None };

        // try rotating from right neighbor
        if let Some(ref mut neighbor) = r {
            if neighbor.key_count >= min_keys {
                let take_ptr = neighbor.ptrs[0];
                let rotate_key = neighbor.keys[0];
                let new_key = unsafe { (*branch.ptrs[branch.key_count as usize - 1]).rightmost_key() };
                branch.keys[branch.key_count as usize - 1] = new_key;
                branch.ptrs[branch.key_count as usize] = take_ptr;
                neighbor.ptrs[0] = neighbor.ptrs[1];
                for j in 0..(neighbor.key_count as usize - 1) {
                    neighbor.keys[j] = neighbor.keys[j + 1];
                    neighbor.ptrs[j + 1] = neighbor.ptrs[j + 2];
                }
                neighbor.key_count -= 1;
                return BPTRemoveResponse::RotateRight(rotate_key);
            }
        }
        // try rotating from left neighbor
        if let Some(ref mut neighbor) = l {
            if neighbor.key_count >= min_keys {
                let take_ptr = neighbor.ptrs[neighbor.key_count as usize];
                let rotate_key = neighbor.keys[neighbor.key_count as usize - 1];
                let new_key = unsafe { (*take_ptr).rightmost_key() };
                for j in (0..(branch.key_count as usize - 1)).rev() {
                    branch.keys[j + 1] = branch.keys[j];
                    branch.ptrs[j + 2] = branch.ptrs[j + 1];
                }
                branch.ptrs[1] = branch.ptrs[0];
                branch.keys[0] = new_key;
                branch.ptrs[0] = take_ptr;
                neighbor.key_count -= 1;
                return BPTRemoveResponse::RotateLeft(rotate_key);
            }
        }

        // try merging right neighbor
        if let Some(neighbor) = r {
            let new_key = unsafe { (*branch.ptrs[branch.key_count as usize - 1]).rightmost_key() };
            branch.keys[branch.key_count as usize - 1] = new_key;
            branch.ptrs[branch.key_count as usize] = neighbor.ptrs[0];
            for j in 0..(neighbor.key_count as usize) {
                branch.keys[branch.key_count as usize + j] = neighbor.keys[j];
                branch.ptrs[branch.key_count as usize + 1 + j] = neighbor.ptrs[j + 1];
            }
            branch.key_count += neighbor.key_count;
            unsafe {
                Box::from_raw(right);
            }
            return BPTRemoveResponse::MergeRight;
        }
        // try merging left neighbor
        if let Some(neighbor) = l {
            let new_key = unsafe { (*neighbor.ptrs[neighbor.key_count as usize]).rightmost_key() };
            for j in (0..(branch.key_count as usize - 1)).rev() {
                branch.keys[neighbor.key_count as usize + 1 + j] = branch.keys[j];
                branch.ptrs[neighbor.key_count as usize + 2 + j] = branch.ptrs[j + 1];
            }
            branch.keys[neighbor.key_count as usize] = new_key;
            branch.ptrs[neighbor.key_count as usize + 1] = branch.ptrs[0];
            branch.ptrs[0] = neighbor.ptrs[0];
            for j in 0..(neighbor.key_count as usize) {
                branch.keys[j] = neighbor.keys[j];
                branch.ptrs[j + 1] = neighbor.ptrs[j + 1];
            }
            branch.key_count += neighbor.key_count;
            unsafe {
                Box::from_raw(left);
            }
            return BPTRemoveResponse::MergeLeft;
        }
        
        panic!("Invalid remove case: remove was called on a branch with no neighbors given.");
    }

    fn remove_from_leaf(leaf: &mut BPTLeaf<V>, key: &u32, left: *mut Self, right: *mut Self) -> BPTRemoveResponse {
        let mut idx = 0;
        while idx < leaf.key_count as usize && leaf.keys[idx] < *key {
            idx += 1;
        }

        // there's no record for given key
        if idx == leaf.key_count as usize || leaf.keys[idx] != *key {
            return BPTRemoveResponse::NoChange;
        }
        
        let min_keys = ((B_PARAMETER / 2) + (B_PARAMETER % 2)) as u8;
        // underflow doesn't occur
        if leaf.key_count > min_keys {
            // move records further to the right one place left to fill formed gap
            for j in (idx + 1)..(leaf.key_count as usize) {
                leaf.keys[j - 1] = leaf.keys[j];
                leaf.ptrs[j - 1] = leaf.ptrs[j];
            }
            leaf.key_count -= 1;
            return BPTRemoveResponse::NoChange;
        }

        // convert neighbors into Option<&mut Leaf> (and assert they are leaf nodes)
        let mut l = if !left.is_null() {
            if let BPTNode::Leaf(ref mut neighbor) = unsafe { &mut *left } {
                Some(neighbor)
            } else {
                panic!("Invalid remove case: branch node was provided as a neighbor of a leaf node.");
            }
        } else { None };
        let mut r = if !right.is_null() {
            if let BPTNode::Leaf(ref mut neighbor) = unsafe { &mut *right } {
                Some(neighbor)
            } else {
                panic!("Invalid remove case: branch node was provided as a neighbor of a leaf node.");
            }
        } else { None };

        // try rotating from right neighbor
        if let Some(ref mut neighbor) = r {
            if neighbor.key_count > min_keys {
                let take_key = neighbor.keys[0];
                let take_ptr = neighbor.ptrs[0];
                for j in (idx + 1)..(leaf.key_count as usize) {
                    leaf.keys[j - 1] = leaf.keys[j];
                    leaf.ptrs[j - 1] = leaf.ptrs[j];
                }
                leaf.keys[leaf.key_count as usize - 1] = take_key;
                leaf.ptrs[leaf.key_count as usize - 1] = take_ptr;
                for j in 0..(neighbor.key_count as usize - 1) {
                    neighbor.keys[j] = neighbor.keys[j + 1];
                    neighbor.ptrs[j] = neighbor.ptrs[j + 1];
                }
                neighbor.key_count -= 1;
                return BPTRemoveResponse::RotateRight(take_key);
            }
        }
        // try rotating from left neighbor
        if let Some(ref mut neighbor) = l {
            if neighbor.key_count > min_keys {
                let take_key = neighbor.keys[neighbor.key_count as usize - 1];
                let take_ptr = neighbor.ptrs[neighbor.key_count as usize - 1];
                let rotation_key = neighbor.keys[neighbor.key_count as usize - 2];
                for j in (0..idx).rev() {
                    leaf.keys[j + 1] = leaf.keys[j];
                    leaf.ptrs[j + 1] = leaf.ptrs[j];
                }
                leaf.keys[0] = take_key;
                leaf.ptrs[0] = take_ptr;
                neighbor.key_count -= 1;
                return BPTRemoveResponse::RotateLeft(rotation_key);
            }
        }

        // try merging right neighbor
        if let Some(neighbor) = r {
            for j in (idx + 1)..(leaf.key_count as usize) {
                leaf.keys[j - 1] = leaf.keys[j];
                leaf.ptrs[j - 1] = leaf.ptrs[j];
            }
            for j in 0..(neighbor.key_count as usize) {
                leaf.keys[leaf.key_count as usize + j - 1] = neighbor.keys[j];
                leaf.ptrs[leaf.key_count as usize + j - 1] = neighbor.ptrs[j];
            }
            leaf.key_count += neighbor.key_count - 1;
            unsafe {
                Box::from_raw(right);
            }
            return BPTRemoveResponse::MergeRight;
        }
        // try merging left neighbor
        if let Some(neighbor) = l {
            for j in ((idx + 1)..(leaf.key_count as usize)).rev() {
                leaf.keys[neighbor.key_count as usize + j - 1] = leaf.keys[j];
                leaf.ptrs[neighbor.key_count as usize + j - 1] = leaf.ptrs[j];
            }
            for j in (0..idx).rev() {
                leaf.keys[neighbor.key_count as usize + j] = leaf.keys[j];
                leaf.ptrs[neighbor.key_count as usize + j] = leaf.ptrs[j];
            }
            for j in 0..(neighbor.key_count as usize) {
                leaf.keys[j] = neighbor.keys[j];
                leaf.ptrs[j] = neighbor.ptrs[j];
            }
            leaf.key_count += neighbor.key_count - 1;
            unsafe {
                Box::from_raw(left);
            }
            return BPTRemoveResponse::MergeLeft;
        }

        panic!("Invalid remove case: remove was called on a leaf with no neighbors given.");
    }

    /// Utility function for remove to determine a new separator
    fn rightmost_key(&self) -> u32 {
        match self {
            BPTNode::Branch(ref branch) => unsafe { (*branch.ptrs[branch.key_count as usize]).rightmost_key() },
            BPTNode::Leaf(ref leaf) => leaf.keys[leaf.key_count as usize - 1],
        }
    }

    fn free(&mut self) {
        match self {
            BPTNode::Leaf(leaf) => {
                for i in 0..(leaf.key_count as usize) {
                    unsafe { Box::from_raw(leaf.ptrs[i]) };
                }
            }
            BPTNode::Branch(branch) => {
                for i in 0..(branch.key_count as usize + 1) {
                    unsafe {
                        (*branch.ptrs[i]).free();
                        Box::from_raw(branch.ptrs[i]);
                    }
                }
            }
        }
    }

    // Checks B+ invariants;
    // Returns the depth and number of elements of the subtree rooted in this node
    #[cfg(test)]
    fn check_bptree_properties(&self, least_lim: Option<u32>, most_lim: Option<u32>, root: bool) -> (usize, usize) {
        let mut least_lim = least_lim;
        match self {
            BPTNode::Branch(branch) => {
                if !root {
                    let min_keys = (B_PARAMETER / 2) - 1 + (B_PARAMETER % 2);
                    assert!(branch.key_count >= min_keys as u8,
                        "Non-root branch nodes are expected to hold at least {} keys, found one with {}.", min_keys, branch.key_count);
                }
                assert!(branch.key_count < B_PARAMETER as u8);
                let mut count = 0;
                let (d, cnt) = unsafe { (*branch.ptrs[0]).check_bptree_properties(least_lim, Some(branch.keys[0]), false) };
                count += cnt;
                for i in 0..(branch.key_count as usize) {
                    if let Some(lim) = least_lim {
                        assert!(lim < branch.keys[i], "Branch key idx {} expected to be over {}, but was {}.", i, lim, branch.keys[i]);
                    }
                    if let Some(lim) = most_lim {
                        assert!(lim >= branch.keys[i], "Branch key idx {} expected to be at most {}, but was {}.", i, lim, branch.keys[i]);
                    }
                    least_lim = Some(branch.keys[i]);
                    let mlim_subtree = if i + 1 < (branch.key_count as usize) {
                        Some(branch.keys[i + 1])
                    } else { most_lim };
                    let (d_now, cnt_now) = unsafe { (*branch.ptrs[i + 1]).check_bptree_properties(least_lim, mlim_subtree, false) };
                    assert_eq!(d, d_now, "Nonequal depths of branch subtrees.");
                    count += cnt_now;
                }
                (d + 1, count)
            }
            BPTNode::Leaf(leaf) => {
                if !root {
                    let min_keys = (B_PARAMETER / 2) + (B_PARAMETER % 2);
                    assert!(leaf.key_count >= min_keys as u8,
                        "Non-root leaves are expected to hold at least {} keys, found one with {}.", min_keys, leaf.key_count);
                }
                assert!(leaf.key_count <= B_PARAMETER as u8);
                for i in 0..(leaf.key_count as usize) {
                    if let Some(lim) = least_lim {
                        assert!(lim < leaf.keys[i], "Leaf key idx {} expected to be over {}, but was {}.", i, lim, leaf.keys[i]);
                    }
                    if let Some(lim) = most_lim {
                        assert!(lim >= leaf.keys[i], "Leaf key idx {} expected to be at most {}, but was {}.", i, lim, leaf.keys[i]);
                    }
                    assert!(!leaf.ptrs[i].is_null());

                    least_lim = Some(leaf.keys[i]);
                }
                (1, leaf.key_count as usize)
            }
        }
    }
}

impl<V> Drop for BPTree<V> {
    fn drop(&mut self) {
        if !self.root.is_null() {
            unsafe {
                (*self.root).free();
                Box::from_raw(self.root);
            }
        }
    }
}

#[cfg(test)]
mod test {
    use super::BPTree;
    use rand::{thread_rng, Rng};

    #[test]
    fn update_basic() {
        let mut map = BPTree::new();
        map.update(65, 65);
        map.update(2, 2);
        map.update(1000, 1000);
        map.check_bptree_properties(3);
        assert_eq!(65, *map.search(&65).unwrap());
        
        for i in 5..120 {
            map.update(i, i * 4);
        }
        map.check_bptree_properties(117);
        assert_eq!(2, *map.search(&2).unwrap());
        assert_eq!(1000, *map.search(&1000).unwrap());
        for i in 5..120 {
            assert_eq!(i * 4, *map.search(&i).unwrap());
        }
    }

    #[test]
    fn random_update() {
        let mut rng = thread_rng();
        let mut map = BPTree::new();
        let mut count = 0;
        let mut member = [0; 1000];
        for _ in 0..20 {
            for i in 1..31 {
                let key = rng.gen_range(0, 1000);
                if member[key as usize] == 0 {
                    count += 1;
                }
                map.update(key, (key, i));
                member[key as usize] = i;
                map.check_bptree_properties(count);
            }
            for i in 0..1000 {
                let record = map.search(&(i as u32));
                match member[i] {
                    0 => assert_eq!(record, None,
                        "Unexpected record for key {}, key hasn't been inserted. Record is {:?}", i, record.unwrap()),
                    e => {
                        match record {
                            None => panic!("Key {} has been inserted, but no record for it was received.", i),
                            Some(rec) => assert_eq!(*rec, (i as u32, e),
                                "Unexpected record. Expected ({}, {}), received ({}, {})", i, e, rec.0, rec.1),
                        }
                    }
                }
            }
        }
        map.check_bptree_properties(count);
    }

    #[test]
    fn remove_basic() {
        let mut map = BPTree::new();
        map.update(1, 4);
        map.update(50, 200);
        map.update(100, 400);
        map.check_bptree_properties(3);
        assert_eq!(4, *map.search(&1).unwrap());
        assert_eq!(400, *map.search(&100).unwrap());
        map.remove(&1);
        map.check_bptree_properties(2);
        map.remove(&100);
        map.check_bptree_properties(1);
        assert!(map.search(&1).is_none());
        assert!(map.search(&100).is_none());

        for i in 40..61 {
            map.update(i, i);
        }
        let mut count = 21;
        map.check_bptree_properties(count);
        assert_eq!(50, *map.search(&50).unwrap());
        let mut i = 40;
        while i < 61 {
            map.remove(&(i));
            count -= 1;
            i += 2;
            map.check_bptree_properties(count);
        }
        i = 41;
        while i < 61 {
            assert!(map.search(&(i - 1)).is_none());
            assert_eq!(i, *map.search(&i).unwrap());
            i += 2;
        }
        i = 41;
        while i < 61 {
            map.remove(&i);
            count -= 1;
            i += 2;
            map.check_bptree_properties(count);
        }
    }

    #[test]
    fn random_remove() {
        let mut rng = thread_rng();
        let mut map = BPTree::new();
        let mut count = 0;
        let mut member = [0; 1000];
        for i in 0..6 {
            for j in 1..550 {
                let key = rng.gen_range(0, 1000);
                let choice = rng.gen_range(0, 3 + i);
                if choice < 3 {
                    // update
                    if member[key as usize] == 0 {
                        count += 1;
                    }
                    map.update(key, (key, j));
                    member[key as usize] = j;
                } else {
                    // remove
                    if member[key as usize] != 0 {
                        count -= 1;
                    }
                    map.remove(&key);
                    member[key as usize] = 0;
                }
                map.check_bptree_properties(count);
            }
            for j in 0..1000 {
                let record = map.search(&(j as u32));
                match member[j] {
                    0 => assert_eq!(record, None,
                        "Unexpected record for key {}, key shouldn't be stored. Record is {:?}", j, record.unwrap()),
                    e => {
                        match record {
                            None => panic!("Key {} should be stored, but no record for it was received.", j),
                            Some(rec) => assert_eq!(*rec, (j as u32, e),
                                "Unexpected record. Expected ({}, {}), received ({}, {})", j, e, rec.0, rec.1),
                        }
                    }
                }
            }
        }
        map.check_bptree_properties(count);
    }
}
