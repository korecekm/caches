// An implementation of a doubly linked list, that we use in our cache
// implementations mainly as a queue.
//
// This is NOT a general DLL implementation, it is solely intended to serve the
// cache data structures in this project. It also provides special functions
// for which the cache implementations need to know our DLL semantics.

use std::mem;
use std::ptr::NonNull;

// Rather than using a simple pointer, our semantics will use options with
// NonNull to better ensure correct usage.
type Link<V> = Option<NonNull<DLNode<V>>>;

/// Doubly-linked list strictly for the use of our cache data structures
pub struct DLList<V> {
    pub(crate) head: Link<V>,
    pub(crate) tail: Link<V>,
    pub size: usize,
}

// A node only needs its stored element and pointers to its neighbors
pub struct DLNode<V> {
    pub(crate) prev: Link<V>,
    pub(crate) next: Link<V>,
    pub(crate) elem: V,
}

impl<V> DLNode<V> {
    /// Create a node of our DLL with no neighbors set yet.
    ///
    /// *(Such function should normally not be set as `pub`, but we will only
    /// use this in our cache implementations with the knowledge of the list
    /// semantics)*
    pub(crate) fn new(elem: V) -> Self {
        Self {
            prev: None,
            next: None,
            elem,
        }
    }

    /// Move this node to front of the queue (also needs a mutable reference
    /// to the list (queue) itself)
    pub fn move_to_front(&mut self, queue: &mut DLList<V>) {
        let prev_node = mem::take(&mut self.prev);
        if let Some(mut prev) = prev_node {
            // We checked that the node really isn't at the front yet.
            // Remove the node from its current location and bring it to the
            // front.
            match mem::take(&mut self.next) {
                // The node was the tail node. The 'previous' one becomes the
                // tail now.
                None => unsafe {
                    prev.as_mut().next = None;
                    queue.tail = Some(prev);
                },
                // Link the 'previous' and 'next' neighbors together
                Some(mut next) => unsafe {
                    next.as_mut().prev = Some(prev);
                    prev.as_mut().next = Some(next);
                },
            }
            // Reinsert the node as the head element
            queue.insert_head(self as *mut _)
        }
    }

    /// Remove this node from the given list.
    /// ! note that for a node inside a NonNull, this doesn't deallocate its'
    /// memory !
    pub(crate) fn remove(&mut self, queue: &mut DLList<V>) {
        let prev_node = mem::take(&mut self.prev);
        let next_node = mem::take(&mut self.next);
        // Either link the neighbors of this node together, if it had both
        // neighbors, or update the head/tail status
        if let Some(mut prev) = prev_node {
            unsafe {
                prev.as_mut().next = next_node;
            }
        } else {
            queue.head = next_node;
        }
        if let Some(mut next) = next_node {
            unsafe {
                next.as_mut().prev = prev_node;
            }
        } else {
            queue.tail = prev_node;
        }
        queue.size -= 1;
    }
}

impl<V> DLList<V> {
    /// Create an empty doubly linked list
    pub fn new() -> Self {
        Self {
            head: None,
            tail: None,
            size: 0,
        }
    }

    /// Inserts the given Node as the queue head.
    ///
    /// ! since it is a utility function not made for public use, it doesn't
    /// increase the list's size, you may need to do that manually !
    pub(crate) fn insert_head(&mut self, node: *mut DLNode<V>) {
        match self.head {
            None => {
                // The list was empty until now
                self.head = NonNull::new(node);
                self.tail = NonNull::new(node);
            }
            Some(mut head) => {
                // Push in front of the old head node
                unsafe {
                    head.as_mut().prev = NonNull::new(node);
                    (*node).next = mem::take(&mut self.head);
                }
                self.head = NonNull::new(node);
            }
        }
    }

    /// Push an element to the head of the list.
    /// *(corresponds to a queue `push`)*
    pub fn push_front(&mut self, elem: V) {
        self.insert_head(Box::into_raw(Box::new(DLNode::new(elem))));
        self.size += 1;
    }

    /// Pops the tail element of the list (if any).
    ///
    /// *(corresponds to a queue `pop`)*
    pub fn pop_back(&mut self) -> Option<V> {
        let tail = mem::take(&mut self.tail);
        tail.map(|node| unsafe {
            // Free the node
            let node = Box::from_raw(node.as_ptr());
            // Update the list's tail
            if let Some(mut prev) = node.prev {
                prev.as_mut().next = None;
                self.tail = Some(prev);
            } else {
                self.head = None;
            }
            self.size -= 1;
            // Return the elem from the freed tail node
            node.elem
        })
    }

    /// Get a reference to the element at the back of this list (if any).
    pub fn get_back<'a>(&'a self) -> Option<&V> {
        self.tail.map(|node| unsafe { &(*node.as_ptr()).elem })
    }

    /// Get an iterator to the elements in the list from head to tail
    pub fn iter<'a>(&'a self) -> DLListIter<'a, V> {
        DLListIter::new(&self.head)
    }
}

impl<V> Drop for DLList<V> {
    fn drop(&mut self) {
        // Frees the nodes from head to tail
        let mut current = self.head;
        while let Some(mut node) = current {
            unsafe {
                current = node.as_mut().next;
                // Free current node
                Box::from_raw(node.as_ptr());
            }
        }
    }
}

/// Iterator over the references to elements in our list (in the order from
/// head to tail)
pub struct DLListIter<'a, V> {
    // Keeps a link to the 'current' node.
    current: &'a Link<V>,
}

impl<'a, V> DLListIter<'a, V> {
    pub fn new(head: &'a Link<V>) -> Self {
        // The 'current' node starts at the head
        Self { current: head }
    }
}

impl<'a, V> Iterator for DLListIter<'a, V> {
    type Item = &'a V;

    fn next(&mut self) -> Option<Self::Item> {
        // Each time, we return the reference to the element in the `current`
        // node and move `current` one node forward.
        // If `current` is None, we have finished the iteration and return None
        match self.current {
            Some(ref node_ptr) => unsafe {
                self.current = &node_ptr.as_ref().next;
                Some(&node_ptr.as_ref().elem)
            },
            None => None,
        }
    }
}

// Test:

#[cfg(test)]
mod test {
    use super::DLList;
    use rand::{thread_rng, Rng};

    #[test]
    fn random() {
        // tests list works as a valid queue
        let mut rng = thread_rng();
        let mut list = DLList::new();
        // We keep a 'journal' of pushed elements
        let mut journal = vec![];
        // `journal_idx` tells us which element of our journal is expected to
        // be popped next (in a FIFO order, that is)
        let mut journal_idx = 0;
        // First, we push 10 elements at random
        for _ in 0..10 {
            let x = rng.gen_range(0, 512);
            list.push_front(x);
            journal.push(x);
        }
        let mut total_inserted = 10;
        for _ in 0..1000 {
            // if `choice > 1`, we try popping from the queue, otherwise we
            // push_front
            let mut choice = 0;
            // Popping makes no sense if list is empty
            if list.size > 0 {
                choice = rng.gen_range(0, 5);
            }
            if choice > 1 {
                // Pop an element and make sure it is the one we expect
                let x = list.pop_back();
                assert_eq!(x.unwrap(), journal[journal_idx]);
                journal_idx += 1;
            } else {
                // Push a new random element into the queue
                let x = rng.gen_range(0, 512);
                list.push_front(x);
                journal.push(x);
                total_inserted += 1;
            }
            assert_eq!(list.size, total_inserted - journal_idx);
        }
        // Pop the last kept elements and check they are the expected ones
        while journal_idx < total_inserted {
            let x = list.pop_back();
            assert_eq!(x.unwrap(), journal[journal_idx]);
            journal_idx += 1;
        }
        assert_eq!(list.pop_back(), None);
    }

    #[test]
    fn iter_simple() {
        // Tests the most basic function of our iterator
        let mut list = DLList::new();
        for i in 0..10 {
            list.push_front(i);
        }
        let mut iter = 9;
        for elem in list.iter() {
            assert_eq!(elem, &iter);
            iter -= 1;
        }
    }
}
