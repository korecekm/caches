use crate::list::{DLList, DLNode};
use std::collections::HashMap;
use std::hash::Hash;
use std::ptr::NonNull;

pub struct LRUCache<K: Clone + Eq + Hash, V> {
    capacity: usize,
    map: HashMap<K, NonNull<DLNode<(K, V)>>>,
    list: DLList<(K, V)>,
}

impl<K: Clone + Eq + Hash, V> LRUCache<K, V> {
    pub fn new(capacity: usize) -> Self {
        Self {
            capacity,
            map: HashMap::with_capacity(capacity),
            list: DLList::new(),
        }
    }

    pub fn get<'a>(&'a mut self, key: &K) -> Option<&'a V> {
        match self.map.get_mut(key) {
            Some(node) => unsafe {
                node.as_mut().move_to_front(&mut self.list);
                Some(&node.as_ref().elem.1)
            }
            None => None,
        }
    }

    /// Expects that key isn't already present!
    pub fn insert(&mut self, key: K, value: V) {
        if self.list.size == self.capacity {
            if let Some((k, _)) = self.list.pop_back() {
                self.map.remove(&k);
            }
        }
        let mut node =
            NonNull::new(Box::into_raw(Box::new(DLNode::new((key.clone(), value))))).unwrap();
        self.map.insert(key, node);
        unsafe {
            self.list.insert_head(node.as_mut() as *mut DLNode<_>);
        }
        self.list.size += 1;
    }
}

// Test:

#[cfg(test)]
mod test {
    use super::LRUCache;

    #[test]
    fn simple() {
        let mut lru = LRUCache::new(3);
        assert_eq!(lru.get(&1), None);
        lru.insert(1, 'A');
        assert_eq!(lru.get(&2), None);
        lru.insert(2, 'B');
        assert_eq!(lru.get(&2), Some(&'B'));
        assert_eq!(lru.get(&2), Some(&'B'));
        assert_eq!(lru.get(&1), Some(&'A'));
        assert_eq!(lru.get(&3), None);
        lru.insert(3, 'C');
        assert_eq!(lru.get(&4), None);
        lru.insert(4, 'D');

        assert_eq!(lru.get(&2), None);
        assert_eq!(lru.list.size, 3);
        for i in [(1, 'A'), (3, 'C'), (4, 'D')].iter() {
            assert_eq!(lru.list.pop_back(), Some(*i));
        }
        assert_eq!(lru.list.size, 0);
        assert_eq!(lru.list.pop_back(), None);
    }
}
