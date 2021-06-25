use crate::list::{DLList, DLNode};
use std::collections::HashMap;
use std::hash::Hash;
use std::mem::{self, MaybeUninit};
use std::ptr::NonNull;

enum Record<K, V> {
    Q1Elem(NonNull<DLNode<(K, Box<V>)>>),
    Q2Elem(NonNull<DLNode<(K, Box<V>)>>),
    LFUElem(usize, Box<V>),
}

/// 2Q cache where the primary (last) 'queue' is an LFU rather than LRU
pub struct QQLFUCache<K: Clone + Eq + Hash, V, const LFU_CAPACITY: usize> {
    q1_capacity: usize,
    q2_capacity: usize,
    map: HashMap<K, Record<K, V>>,
    queue1: DLList<(K, Box<V>)>,
    queue2: DLList<(K, Box<V>)>,
    lfu_heap: MaybeUninit<[(K, u32); LFU_CAPACITY]>,
    // the current number of elements that are actually initiated inside the heap
    lfu_size: usize,
}

impl<K: Clone + Eq + Hash, V, const LFU_CAPACITY: usize> QQLFUCache<K, V, LFU_CAPACITY> {
    pub fn new(q1_capacity: usize, q2_capacity: usize) -> Self {
        Self {
            q1_capacity,
            q2_capacity,
            map: HashMap::with_capacity(q1_capacity + q2_capacity + LFU_CAPACITY),
            queue1: DLList::new(),
            queue2: DLList::new(),
            lfu_heap: MaybeUninit::uninit(),
            lfu_size: 0,
        }
    }

    pub fn get<'a>(&'a mut self, key: &K) -> Option<&'a V> {
        match self.map.get(key) {
            Some(Record::Q1Elem(node_ptr)) => Some(
                // calling this function is a necessary workaround
                Self::get_value_from_q1_node(node_ptr.clone()),
            ),
            Some(Record::Q2Elem(node_ptr)) => {
                let node_ptr = node_ptr.clone();
                Some(self.move_to_lfu(node_ptr))
            }
            Some(Record::LFUElem(idx, _)) => {
                let idx = idx.clone();
                Some(self.access_in_lfu(key, idx))
            }
            None => None,
        }
    }

    pub fn insert(&mut self, key: K, value: V) {
        if self.queue1.size == self.q1_capacity {
            if let Some((evict_key, evict_value)) = self.queue1.pop_back() {
                let last_key = evict_key.clone();
                let record_ptr = NonNull::new(Box::into_raw(Box::new(DLNode::new((
                    evict_key,
                    evict_value,
                )))))
                .unwrap();
                self.insert_into_q2(record_ptr);
                self.map.insert(last_key, Record::Q2Elem(record_ptr));
            }
        }
        let mut new_record = NonNull::new(Box::into_raw(Box::new(DLNode::new((
            key.clone(),
            Box::new(value),
        )))))
        .unwrap();
        self.map.insert(key, Record::Q1Elem(new_record));
        unsafe {
            self.queue1
                .insert_head(new_record.as_mut() as *mut DLNode<_>);
        }
        self.queue1.size += 1;
    }

    fn insert_into_q2(&mut self, mut node: NonNull<DLNode<(K, Box<V>)>>) {
        if self.queue2.size == self.q2_capacity {
            if let Some((record_key, _)) = self.queue2.pop_back() {
                self.map.remove(&record_key);
            }
        }
        unsafe {
            self.queue2.insert_head(node.as_mut() as *mut DLNode<_>);
        }
        self.queue2.size += 1;
    }

    /// 'extracts' a value reference from the given node pointer
    fn get_value_from_q1_node<'a>(node_ptr: NonNull<DLNode<(K, Box<V>)>>) -> &'a V
    where
        K: 'a,
    {
        let (_, ref val_ref) = unsafe { &(*node_ptr.as_ptr()).elem };
        &**val_ref
    }

    /// Moves a record from the second queue to the LFU (on reaccess).
    /// Returns a reference to the value.
    fn move_to_lfu<'a>(&'a mut self, node_ptr: NonNull<DLNode<(K, Box<V>)>>) -> &'a V {
        let mut node = unsafe { Box::from_raw(node_ptr.as_ptr()) };
        node.remove(&mut self.queue2);

        // move to the LFU:
        let (key, value) = node.elem;
        if self.lfu_size < LFU_CAPACITY {
            // the heap hasn't yet reached the capacity
            let heap_idx = self.insert_into_heap((key.clone(), 0));
            self.map
                .insert(key.clone(), Record::LFUElem(heap_idx, value));
        } else {
            // eviction necessary
            let remove_key = unsafe { &(*(self.lfu_heap.as_ptr() as *mut (K, u32)).offset(0)).0 };
            self.map.remove(remove_key);

            // replace it with the new one
            unsafe {
                (self.lfu_heap.as_ptr() as *mut (K, u32))
                    .offset(0)
                    .write((key.clone(), 0));
            }
            let mut heap_idx = 0;
            self.heap_bubble_down(&mut heap_idx);
            self.map
                .insert(key.clone(), Record::LFUElem(heap_idx, value));
        }
        if let Record::LFUElem(_, val_ref) = self.map.get(&key).unwrap() {
            val_ref
        } else {
            panic!("Unreachable.");
        }
    }

    /// Raises the freq counter of the LFU heap element at index $heap_idx and
    /// returns a reference to the corresponding value.
    fn access_in_lfu<'a>(&'a mut self, key: &K, mut heap_idx: usize) -> &'a V {
        self.increment_freq(&mut heap_idx);
        // A necessary workaround to avoid illegal multiple references
        if let Some(Record::LFUElem(ref mut idx, ref val)) = self.map.get_mut(key) {
            *idx = heap_idx;
            &**val
        } else {
            panic!("Unreachable");
        }
    }

    /// Insert a new element into the LFU heap and returns the index it gets.
    /// This expects that the heap hasn't yet reached its' given capacity.
    fn insert_into_heap(&mut self, new_elem: (K, u32)) -> usize {
        // add $new_elem as the last element
        unsafe {
            (self.lfu_heap.as_ptr() as *mut (K, u32))
                .offset(self.lfu_size as isize)
                .write(new_elem);
        }
        // 'bubble up' to correct position according to the freq counter
        let mut heap_idx = self.lfu_size;
        self.heap_bubble_up(&mut heap_idx);
        self.lfu_size += 1;
        heap_idx
    }

    /// Increments the frequency counter (second value in the tuple) of the heap element
    /// at array index $heap_idx, potentially increasing this index accordingly
    fn increment_freq(&mut self, heap_idx: &mut usize) {
        unsafe {
            (*self.lfu_heap.as_mut_ptr())[*heap_idx].1 += 1;
        }
        self.heap_bubble_down(heap_idx);
    }

    /// Makes the heap element at index $heap_idx move 'down' in the heap
    /// according to the freq counter, ie. towards higher counter values
    fn heap_bubble_down(&mut self, heap_idx: &mut usize) {
        // The element is already in a leaf node
        if self.lfu_size <= 2 * (*heap_idx) + 1 {
            return;
        }

        let heap_ref = unsafe { &*self.lfu_heap.as_ptr() };
        let child_idx1 = 2 * (*heap_idx) + 1;
        let child_idx2 = 2 * (*heap_idx) + 2;
        let swap_idx = if self.lfu_size == 2 * (*heap_idx) + 2 {
            child_idx1
        } else if heap_ref[child_idx2].1 < heap_ref[child_idx1].1 {
            child_idx2
        } else {
            child_idx1
        };

        if heap_ref[swap_idx].1 <= heap_ref[*heap_idx].1 {
            self.swap_in_heap(*heap_idx, swap_idx);
            *heap_idx = swap_idx;
            self.heap_bubble_down(heap_idx);
        }
    }

    /// Moves the heap element at index $heap_idx 'up' in the heap, ie. towards
    /// lower freq counter values.
    /// (this is useful mainly when inserting a new heap value, where the
    /// element is first inserted as the very last heap-array value and only
    /// then moves 'up' in the heap, according to it's freq count, which is at
    /// that point 0)
    /// Freq counter at $heap_idx is expected to be at zero
    fn heap_bubble_up(&mut self, heap_idx: &mut usize) {
        if *heap_idx == 0 {
            return;
        }
        let parent_idx = (*heap_idx - 1) / 2;
        let parent_freq = unsafe { (*self.lfu_heap.as_ptr())[parent_idx].1 };
        if parent_freq > 0 {
            self.swap_in_heap(*heap_idx, parent_idx);
            *heap_idx = parent_idx;
            self.heap_bubble_up(heap_idx);
        }
    }

    /// Swaps the two heap elements at given heap-array indices, also updating
    /// (just) the $swap_idx-es index in self.map
    fn swap_in_heap(&mut self, request_idx: usize, swap_idx: usize) {
        let mut_heap = unsafe { self.lfu_heap.as_mut_ptr().as_mut().unwrap() };
        let swapped_elem = mut_heap[swap_idx].clone();
        if let Record::LFUElem(ref mut heap_idx, _) = self.map.get_mut(&swapped_elem.0).unwrap() {
            *heap_idx = request_idx;
        } else {
            panic!("Unreachable");
        }
        mut_heap[swap_idx] = mem::replace(&mut mut_heap[request_idx], swapped_elem);
    }

    #[cfg(test)]
    fn check_heap_properties(&self, expected_elem_count: usize) {
        assert_eq!(self.lfu_size, expected_elem_count);

        let heap_ref = unsafe { &*self.lfu_heap.as_ptr() };
        if expected_elem_count > 1 {
            self.heap_check_recurse(1, &heap_ref[0].1);
        }
    }

    #[cfg(test)]
    fn heap_check_recurse(&self, heap_idx: usize, freq_bound: &u32) {
        if heap_idx >= self.lfu_size {
            return;
        }
        let current_freq = unsafe { &(*self.lfu_heap.as_ptr())[heap_idx].1 };
        assert!(freq_bound <= current_freq);

        self.heap_check_recurse(2 * heap_idx + 1, current_freq);
        self.heap_check_recurse(2 * heap_idx + 2, current_freq);
    }
}

#[cfg(test)]
mod test {
    use super::QQLFUCache;

    #[test]
    fn simple() {
        let mut cache = QQLFUCache::<_, _, 3>::new(2, 2);
        assert_eq!(cache.get(&1), None);
        for i in 1..5 {
            cache.insert(i, 2 * i);
        }
        // records inside queue 1
        assert_eq!(cache.get(&3), Some(&6));
        assert_eq!(cache.get(&4), Some(&8));
        cache.insert(5, 10);
        cache.insert(6, 12);
        // new insertions got these records evicted from queue 2
        assert_eq!(cache.get(&1), None);
        assert_eq!(cache.get(&2), None);
        // move 3 to LFU
        assert_eq!(cache.get(&3), Some(&6));
        assert_eq!(cache.get(&6), Some(&12));
        cache.insert(7, 14);
        cache.insert(8, 16);
        assert_eq!(cache.get(&4), None);
        // 5 enters LFU
        assert_eq!(cache.get(&5), Some(&10));
        assert_eq!(cache.get(&7), Some(&14));
        cache.insert(9, 18);
        cache.insert(10, 20);
        // modifications in the LFU:
        assert_eq!(cache.get(&7), Some(&14));
        assert_eq!(cache.get(&3), Some(&6));
        assert_eq!(cache.get(&8), Some(&16));

        assert_eq!(cache.get(&5), None);
        let expect = [(7, 0), (3, 1), (8, 0)];
        let mut lfu_iter = unsafe { (*cache.lfu_heap.as_ptr()).iter() };
        for exp in expect.iter() {
            assert_eq!(lfu_iter.next().as_ref().unwrap(), &exp);
        }
        assert_eq!(lfu_iter.next(), None);
    }

    // A simple test that only checks the LFU heap behavior.
    // Both queues will only have a capacity of 1 and will only be used to get
    // records to the LFU.
    #[test]
    fn heap_test() {
        let mut cache = QQLFUCache::<_, _, 100>::new(1, 1);
        cache.insert(100, 100);
        cache.insert(200, 200); // let's use 200 as filler to move values to q2
        cache.get(&100);
        assert_eq!(cache.get(&100), Some(&100));
        cache.check_heap_properties(1);

        for i in 1..100 {
            cache.insert(i, 2 * i);
            cache.insert(200, 200);
            cache.get(&i);
            cache.check_heap_properties(i + 1);
        }
        for i in 1..100 {
            for j in i..100 {
                assert_eq!(cache.get(&j), Some(&(2 * j)));
                cache.check_heap_properties(100);
            }
        }

        // Add several one-time values, removing record for &10
        for i in 101..200 {
            cache.insert(i, i);
            cache.check_heap_properties(100);
        }

        cache.insert(0, 0);
        cache.insert(200, 200);
        cache.get(&0);
        cache.check_heap_properties(100);
        for i in 0..100 {
            assert_eq!(cache.get(&i), Some(&(2 * i)));
        }
    }
}
