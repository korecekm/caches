use crate::list::{DLList, DLNode};
use std::collections::HashMap;
use std::hash::Hash;
use std::ptr::NonNull;

enum RecordType {
    Q1Elem,
    Q2Elem,
    LRUElem,
}

struct Record<K, V> {
    rec_type: RecordType,
    key: K,
    value: V,
}

/// 2Q cache
pub struct QCache<K: Clone + Eq + Hash, V> {
    q1_capacity: usize,
    q2_capacity: usize,
    lru_capacity: usize,
    map: HashMap<K, NonNull<DLNode<Record<K, V>>>>,
    queue1: DLList<Record<K, V>>,
    queue2: DLList<Record<K, V>>,
    lru: DLList<Record<K, V>>,
}

impl<K: Clone + Eq + Hash, V> QCache<K, V> {
    pub fn new(q1_capacity: usize, q2_capacity: usize, lru_capacity: usize) -> Self {
        Self {
            q1_capacity,
            q2_capacity,
            lru_capacity,
            map: HashMap::with_capacity(q1_capacity + q2_capacity + lru_capacity),
            queue1: DLList::new(),
            queue2: DLList::new(),
            lru: DLList::new(),
        }
    }

    pub fn get<'a>(&'a mut self, key: &K) -> Option<&'a V> {
        match self.map.get(key) {
            Some(node_ptr) => {
                let node_ptr = node_ptr.clone();
                Some(self.access(node_ptr))
            }
            None => None,
        }
    }

    fn access<'a>(&'a mut self, node_ref: NonNull<DLNode<Record<K, V>>>) -> &'a V {
        let node = unsafe { &mut (*node_ref.as_ptr()) };
        match node.elem.rec_type {
            RecordType::Q2Elem => {
                // move a record inside the second queue to the main queue on new access
                node.elem.rec_type = RecordType::LRUElem;
                node.remove(&mut self.queue2);
                // in case the LRU would overflow, remove the last element
                if self.lru.size == self.lru_capacity {
                    if let Some(record) = self.lru.pop_back() {
                        self.map.remove(&record.key);
                    }
                }
                self.lru.insert_head(node as *mut DLNode<_>);
                self.lru.size += 1;
            }
            RecordType::LRUElem => {
                // classical LRU behavior
                node.move_to_front(&mut self.lru);
            }
            // no change for the first queue
            _ => {}
        }
        &node.elem.value
    }

    /// Expects that the key isn't already present
    pub fn insert(&mut self, key: K, value: V) {
        if self.queue1.size == self.q1_capacity {
            if let Some(mut record) = self.queue1.pop_back() {
                let last_key = record.key.clone();
                record.rec_type = RecordType::Q2Elem;
                let record_ptr =
                    NonNull::new(Box::into_raw(Box::new(DLNode::new(record)))).unwrap();
                self.insert_into_q2(record_ptr);
                self.map.insert(last_key, record_ptr);
            }
        }
        let mut new_record = NonNull::new(Box::into_raw(Box::new(DLNode::new(Record {
            rec_type: RecordType::Q1Elem,
            key: key.clone(),
            value,
        }))))
        .unwrap();
        self.map.insert(key, new_record);
        unsafe {
            self.queue1
                .insert_head(new_record.as_mut() as *mut DLNode<_>);
        }
        self.queue1.size += 1;
    }

    fn insert_into_q2(&mut self, mut node: NonNull<DLNode<Record<K, V>>>) {
        if self.queue2.size == self.q2_capacity {
            if let Some(record) = self.queue2.pop_back() {
                self.map.remove(&record.key);
            }
        }
        unsafe {
            self.queue2.insert_head(node.as_mut() as *mut DLNode<_>);
        }
        self.queue2.size += 1;
    }
}

#[cfg(test)]
mod test {
    use super::QCache;

    #[test]
    fn simple() {
        let mut qq = QCache::new(2, 2, 3);
        assert_eq!(qq.get(&1), None);
        for i in 1..5 {
            qq.insert(i, 2 * i);
        }
        assert_eq!(qq.get(&3), Some(&6));
        assert_eq!(qq.get(&4), Some(&8));
        qq.insert(5, 10);
        qq.insert(6, 12);
        assert_eq!(qq.get(&1), None);
        assert_eq!(qq.get(&2), None);
        // 3 gets moved to the LRU
        assert_eq!(qq.get(&3), Some(&6));
        assert_eq!(qq.get(&6), Some(&12));
        qq.insert(7, 14);
        qq.insert(8, 16);
        assert_eq!(qq.get(&4), None);
        // 5 enters the LRU
        assert_eq!(qq.get(&5), Some(&10));
        assert_eq!(qq.get(&7), Some(&14));
        qq.insert(9, 18);
        qq.insert(10, 20);
        // all these modify the LRU:
        assert_eq!(qq.get(&7), Some(&14));
        assert_eq!(qq.get(&3), Some(&6));
        assert_eq!(qq.get(&8), Some(&16));

        assert_eq!(qq.get(&5), None);
        let expect = [8, 3, 7];
        let mut idx = 0;
        for elem in qq.lru.iter() {
            assert_eq!((elem.key, elem.value), (expect[idx], (expect[idx] * 2)));
            idx += 1;
        }
    }
}
