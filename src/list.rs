use std::mem;
use std::ptr::NonNull;

type Link<V> = Option<NonNull<DLNode<V>>>;

// Doubly-linked list
pub struct DLList<V> {
    pub(crate) head: Link<V>,
    pub(crate) tail: Link<V>,
    pub size: usize,
}

pub struct DLNode<V> {
    pub(crate) prev: Link<V>,
    pub(crate) next: Link<V>,
    pub(crate) elem: V,
}

impl<V> DLNode<V> {
    pub fn new(elem: V) -> Self {
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
            // Node actually isn't at the front yet
            match mem::take(&mut self.next) {
                None => unsafe {
                    prev.as_mut().next = None;
                    queue.tail = Some(prev);
                },
                Some(mut next) => unsafe {
                    next.as_mut().prev = Some(prev);
                    prev.as_mut().next = Some(next);
                },
            }
            queue.insert_head(self as *mut _)
        }
    }

    /// Remove this node from the given list.
    /// ! note that for a node inside a NonNull, this doesn't deallocate its'
    /// memory !
    pub fn remove(&mut self, queue: &mut DLList<V>) {
        let prev_node = mem::take(&mut self.prev);
        let next_node = mem::take(&mut self.next);
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
    pub fn new() -> Self {
        Self {
            head: None,
            tail: None,
            size: 0,
        }
    }

    /// Inserts the given Node as the queue head.
    /// ! since it is a utility function not made for public use, it doesn't
    /// increase the list's size, you may need to do that manually.
    pub(crate) fn insert_head(&mut self, node: *mut DLNode<V>) {
        match self.head {
            None => {
                self.head = NonNull::new(node);
                self.tail = NonNull::new(node);
            }
            Some(mut head) => {
                unsafe {
                    head.as_mut().prev = NonNull::new(node);
                    (*node).next = mem::take(&mut self.head);
                }
                self.head = NonNull::new(node);
            }
        }
    }

    pub fn push_front(&mut self, elem: V) {
        self.insert_head(Box::into_raw(Box::new(DLNode::new(elem))));
        self.size += 1;
    }

    pub fn pop_back(&mut self) -> Option<V> {
        let tail = mem::take(&mut self.tail);
        tail.map(|node| unsafe {
            let node = Box::from_raw(node.as_ptr());
            if let Some(mut prev) = node.prev {
                prev.as_mut().next = None;
                self.tail = Some(prev);
            } else {
                self.head = None;
            }
            self.size -= 1;
            node.elem
        })
    }

    /// Get a reference to the element at the back of this list (if there are any elements).
    pub fn get_back<'a>(&'a self) -> Option<&V> {
        self.tail.map(|node| unsafe { &(*node.as_ptr()).elem })
    }

    pub fn iter<'a>(&'a self) -> DLListIter<'a, V> {
        DLListIter::new(&self.head)
    }
}

impl<V> Drop for DLList<V> {
    fn drop(&mut self) {
        let mut current = self.head;
        while let Some(mut node) = current {
            unsafe {
                current = node.as_mut().next;
                Box::from_raw(node.as_ptr());
            }
        }
    }
}

pub struct DLListIter<'a, V> {
    current: &'a Link<V>,
}

impl<'a, V> DLListIter<'a, V> {
    pub fn new(head: &'a Link<V>) -> Self {
        Self { current: head }
    }
}

impl<'a, V> Iterator for DLListIter<'a, V> {
    type Item = &'a V;

    fn next(&mut self) -> Option<Self::Item> {
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
        let mut journal = vec![];
        let mut journal_idx = 0;
        for _ in 0..10 {
            let x = rng.gen_range(0, 512);
            list.push_front(x);
            journal.push(x);
        }
        let mut total_inserted = 10;
        for _ in 0..1000 {
            let mut choice = 0; // if > 1, we try popping from the queue, otherwise we push_front
            if list.size > 0 {
                choice = rng.gen_range(0, 5);
            }
            if choice > 1 {
                let x = list.pop_back();
                assert_eq!(x.unwrap(), journal[journal_idx]);
                journal_idx += 1;
            } else {
                let x = rng.gen_range(0, 512);
                list.push_front(x);
                journal.push(x);
                total_inserted += 1;
            }
        }
        assert_eq!(list.size, total_inserted - journal_idx);
        while journal_idx < total_inserted {
            let x = list.pop_back();
            assert_eq!(x.unwrap(), journal[journal_idx]);
            journal_idx += 1;
        }
        assert_eq!(list.pop_back(), None);
    }

    #[test]
    fn iter_simple() {
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
