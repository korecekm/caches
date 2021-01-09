use crate::cache::Cache;
use crate::list::{DLNode, DLList};
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

impl<K: Clone + Eq + Hash, V> LRUCache<K, V> {
    fn new(capacity: usize) -> Self {
        Self {
            capacity,
            map: HashMap::with_capacity(capacity),
            list: DLList::new(),
        }
    }
}

impl<K: Clone + Eq + Hash, V> Cache<K, V> for LRUCache<K, V> {
    fn try_get<'a>(&'a mut self, key: &K) -> Option<&'a V> {
        let list = &mut self.list;
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

// Test:

#[cfg(test)]
mod test {
    use crate::cache::Cache;
    use super::LRUCache;

    #[test]
    fn simple() {
        let mut lru = LRUCache::new(3);
        assert_eq!(lru.try_get(&1), None);
        lru.insert(1, 'A');
        assert_eq!(lru.try_get(&2), None);
        lru.insert(2, 'B');
        assert_eq!(lru.try_get(&2), Some(&'B'));
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
}
