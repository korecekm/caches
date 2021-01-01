use crate::cache::Cache;
use std::collections::HashMap;
use std::ptr::NonNull;
use std::hash::Hash;
use std::mem;

struct LRUCache<
        K: Clone + Eq + Hash,
        V,
    > {
    capacity: usize,
    map: HashMap<K, NonNull<DLNode<(K, V)>>>,
    list: DLList<(K, V)>,
}

// Doubly-linked list
struct DLList<V> {
    head: Option<NonNull<DLNode<V>>>,
    tail: Option<NonNull<DLNode<V>>>,
    pub(crate) size: usize,
}

struct DLNode<V> {
    prev: Option<NonNull<DLNode<V>>>,
    next: Option<NonNull<DLNode<V>>>,
    elem: V,
}

impl<K: Clone + Eq + Hash, V> LRUCache<K, V> {
    pub(crate) fn new(capacity: usize) -> Self {
        Self {
            capacity,
            map: HashMap::with_capacity(capacity),
            list: DLList::new(),
        }
    }
}

impl<K: Clone + Eq + Hash, V> Cache<K, V> for LRUCache<K, V> {
    fn try_get<'a>(&'a mut self, key: &K) -> Option<&'a V> {
        let mut list = &mut self.list;
        self.map.get_mut(key).map(|node| unsafe {
            let prev_node = mem::take(&mut (node.as_mut()).prev);
            if let Some(mut prev) = prev_node {
                let mut node = Box::from_raw(node.as_mut());
                match mem::take(&mut node.as_mut().next) {
                    None => {
                        prev.as_mut().next = None;
                        list.tail = Some(prev);
                    }
                    Some(mut next) => {
                        next.as_mut().prev = Some(prev);
                        prev.as_mut().next = Some(next);
                    }
                }
                list.insert_head(Box::into_raw(node));
            }
            
            &node.as_ref().elem.1
        })
    }

    /// Expects that key isn't already present!
    fn insert(&mut self, key: K, value: V) {
        if self.list.size == self.capacity {
            if let Some((k, _)) = self.list.pop_back() {
                self.map.remove(&k);
            }
        }
        let mut node = NonNull::new(Box::into_raw(Box::new(DLNode::new((key.clone(), value))))).unwrap();
        self.map.insert(key, node);
        unsafe { self.list.insert_head(node.as_mut() as *mut DLNode<_>); }
        self.list.size += 1;
    }
}

// Util:

impl<V> DLNode<V> {
    pub(crate) fn new(elem: V) -> Self {
        Self {
            prev: None,
            next: None,
            elem,
        }
    }
}

impl<V> DLList<V> {
    pub(crate) fn new() -> Self {
        Self {
            head: None,
            tail: None,
            size: 0,
        }
    }

    fn insert_head(&mut self, node: *mut DLNode<V>) {
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

    pub(crate) fn push_front(&mut self, elem: V) {
        self.insert_head(Box::into_raw(Box::new(DLNode::new(elem))));
        self.size += 1;
    }

    pub(crate) fn pop_back(&mut self) -> Option<V> {
        let tail = mem::take(&mut self.tail);
        tail.map(|node| unsafe {
            let node = Box::from_raw(node.as_ptr());
            if let Some(mut prev) = node.prev {
                unsafe { prev.as_mut().next = None; }
                self.tail = Some(prev);
            } else {
                self.head = None;
            }
            self.size -= 1;
            node.elem
        })
    }
}

// Test:

#[cfg(test)]
mod test {
    use crate::cache::Cache;
    use super::{DLList, LRUCache};
    use rand::{thread_rng, Rng};

    #[test]
    fn lru_simple() {
        let mut lru = LRUCache::new(3);
        assert_eq!(lru.try_get(&1), None);
        lru.insert(1, 'A');
        assert_eq!(lru.try_get(&2), None);
        lru.insert(2, 'B');
        assert_eq!(lru.try_get(&2), Some(&'B'));
        assert_eq!(lru.try_get(&1), Some(&'A'));
        assert_eq!(lru.try_get(&3), None);
        lru.insert(3, 'C');
        assert_eq!(lru.try_get(&4), None);
        lru.insert(4, 'D');

        assert_eq!(lru.try_get(&2), None);
        assert_eq!(lru.list.size, 3);
        for i in [ (1, 'A'), (3, 'C'), (4, 'D') ].iter() {
            assert_eq!(lru.list.pop_back(), Some(*i));
        }
        assert_eq!(lru.list.size, 0);
        assert_eq!(lru.list.pop_back(), None);
    }

    #[test]
    fn list_random() {
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
            let mut choice = 0;  // if > 1, we try popping from the queue, otherwise we push_front
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
}
