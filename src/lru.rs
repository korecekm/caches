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
            },
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

    /// Like get, but removing the record from the cache.
    /// This is useful when this LRU is a thread-local cache and the thread
    /// currently has write privilege to a global transactional cache, ie if
    /// a record is present in our local cache, we can remove it from here and
    /// include it in the global cache instead.
    pub fn extract(&mut self, key: &K) -> Option<V> {
        if let Some(node) = self.map.remove(key) {
            let mut node = unsafe { *Box::from_raw(node.as_ptr()) };
            node.remove(&mut self.list);
            Some(node.elem.1)
        } else {
            None
        }
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

    #[test]
    fn extract_simple() {
        let mut lru = LRUCache::new(5);
        assert_eq!(lru.extract(&7), None);
        for i in 1..11 {
            lru.insert(i, 2 * i);
        }
        assert_eq!(lru.extract(&5), None);

        assert_eq!(lru.list.size, 5);
        assert_eq!(lru.extract(&7), Some(14));
        assert_eq!(lru.list.size, 4);
        assert_eq!(lru.extract(&9), Some(18));
        assert_eq!(lru.list.size, 3);

        for elem in [(6, 12), (8, 16), (10, 20)].iter() {
            assert_eq!(lru.list.pop_back(), Some(*elem));
        }
        assert_eq!(lru.list.size, 0);
        assert_eq!(lru.list.pop_back(), None);
    }
}
