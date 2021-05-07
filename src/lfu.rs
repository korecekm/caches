use std::collections::HashMap;
#[cfg(test)]
use std::fmt::Display;
use std::hash::Hash;
use std::mem::{self, MaybeUninit};

// LFU implemented via a hash map and a binary heap.
// This heap is a standard array-based min-heap ordered by a frequency counter.
// Before the cache's CAPACITY is reached, standard heap insertions are used for
// submitting new keys for caching. Once there are a CAPACITY of key-value pairs,
// when inserting new keys, the first (0th) element, ie. the one with lowest
// freq counter is removed, freeing space for the new element (which we know has
// freq 0, initially).
// Once a key is reaccessed, its' freq counter is increased and potentially
// 'bubbles down' towards the leaves of the heap.
// Additionaly, accessed elements (either inserted or reaccessed) move the
// furthest they can 'down' in the heap towards higher freqs, behind records of
// identical freq count, to also roughly approximate LRU policy on elements with
// the same freq counts.

pub struct LFUCache<K: Clone + Eq + Hash, V, const CAPACITY: usize> {
    // For a key, the map stores a tuple (0, 1) containing
    // 0: The index of the corresponding element in the heap (array)
    // 1: The stored value itself
    map: HashMap<K, (usize, V)>,
    // The array values are (key, freq), where 'freq' is the frequency counter
    // by which we order.
    heap: MaybeUninit<[(K, u32); CAPACITY]>,
}

impl<K: Clone + Eq + Hash, V, const CAPACITY: usize> LFUCache<K, V, CAPACITY> {
    pub fn new() -> Self {
        Self {
            map: HashMap::with_capacity(CAPACITY),
            heap: MaybeUninit::uninit(),
        }
    }

    /// Returns value for given key, if it is present in the cache.
    /// Potentially changes the cache's inner structure.
    pub fn get<'a>(&'a mut self, key: &K) -> Option<&'a V> {
        match self.map.get(key) {
            // One of the necessary Rust workarounds :(
            Some((heap_idx, _)) => {
                let mut updated_idx = *heap_idx;
                self.increment_freq(&mut updated_idx);
                if let Some((ref mut heap_idx, ref val)) = self.map.get_mut(key) {
                    *heap_idx = updated_idx;
                    Some(val)
                } else {
                    panic!("Unreachable.");
                }
            }
            None => None,
        }
    }

    /// Submits this key-value pair for caching.
    /// This expects that key isn't already present!
    pub fn insert(&mut self, key: K, value: V) {
        if self.map.len() < CAPACITY {
            // insert new key into the heap
            let heap_idx = self.insert_into_heap((key.clone(), 0));
            // insert record with the correct heap index into the hashmap
            self.map.insert(key, (heap_idx, value));
        } else {
            // remove the l.f.u. element
            let remove_key = unsafe { &(*(self.heap.as_ptr() as *mut (K, u32)).offset(0)).0 };
            self.map.remove(remove_key);

            // replace it with the new one
            unsafe {
                (self.heap.as_ptr() as *mut (K, u32))
                    .offset(0)
                    .write((key.clone(), 0));
            }
            let mut heap_idx = 0;
            self.heap_bubble_down(&mut heap_idx);
            self.map.insert(key, (heap_idx, value));
        }
    }

    /// Increments the frequency counter (second value in the tuple) of the heap element
    /// at array index $heap_idx, potentially increasing this index accordingly
    fn increment_freq(&mut self, heap_idx: &mut usize) {
        unsafe {
            (*self.heap.as_mut_ptr())[*heap_idx].1 += 1;
        }
        self.heap_bubble_down(heap_idx);
    }

    /// Insert a new element into the LFU heap and returns the index it gets
    fn insert_into_heap(&mut self, new_elem: (K, u32)) -> usize {
        // add $new_elem as the last element
        unsafe {
            (self.heap.as_ptr() as *mut (K, u32))
                .offset(self.map.len() as isize)
                .write(new_elem);
        }
        // 'bubble up' to correct position according to the freq counter
        let mut heap_idx = self.map.len() as usize;
        self.heap_bubble_up(&mut heap_idx);
        heap_idx
    }

    /// Makes the heap element at index $heap_idx move 'down' in the heap
    /// according to the freq counter, ie. towards higher counter values
    fn heap_bubble_down(&mut self, heap_idx: &mut usize) {
        if self.map.len() as usize <= 2 * (*heap_idx) + 1 {
            return;
        }

        let heap_ref = unsafe { &*self.heap.as_ptr() };
        let child_idx1 = 2 * (*heap_idx) + 1;
        let child_idx2 = 2 * (*heap_idx) + 2;
        let swap_idx = if self.map.len() as usize == 2 * (*heap_idx) + 2 {
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
        let parent_freq = unsafe { (*self.heap.as_ptr())[parent_idx].1 };
        if parent_freq > 0 {
            self.swap_in_heap(*heap_idx, parent_idx);
            *heap_idx = parent_idx;
            self.heap_bubble_up(heap_idx);
        }
    }

    /// Swaps the two heap elements at given heap-array indices, also updating
    /// (just) the $swap_idx-es index in self.map
    fn swap_in_heap(&mut self, request_idx: usize, swap_idx: usize) {
        let mut_heap = unsafe { self.heap.as_mut_ptr().as_mut().unwrap() };
        let swapped_elem = mut_heap[swap_idx].clone();
        self.map.get_mut(&swapped_elem.0).unwrap().0 = request_idx;
        mut_heap[swap_idx] = mem::replace(&mut mut_heap[request_idx], swapped_elem);
    }

    #[cfg(test)]
    fn check_heap_properties(&self, expected_elem_count: usize)
    where
        K: Display,
    {
        assert_eq!(self.map.len(), expected_elem_count);

        let heap_ref = unsafe { &*self.heap.as_ptr() };
        if expected_elem_count > 1 {
            self.heap_check_recurse(1, &heap_ref[0].1);
            self.heap_check_recurse(2, &heap_ref[0].1);
        }
    }

    #[cfg(test)]
    fn heap_check_recurse(&self, heap_idx: usize, freq_bound: &u32)
    where
        K: Display,
    {
        if heap_idx >= self.map.len() as usize {
            return;
        }
        let current_freq = unsafe { &(*self.heap.as_ptr())[heap_idx].1 };
        assert!(freq_bound <= current_freq);

        self.heap_check_recurse(2 * heap_idx + 1, current_freq);
        self.heap_check_recurse(2 * heap_idx + 2, current_freq);
    }
}

#[cfg(test)]
mod test {
    use super::LFUCache as Cache;

    #[test]
    fn simple() {
        let mut lfu = Cache::<_, _, 5>::new();
        assert_eq!(lfu.get(&4), None);
        assert_eq!(lfu.get(&10), None);
        lfu.insert(10, 10);
        lfu.check_heap_properties(1);
        assert_eq!(lfu.get(&10), Some(&10));
        lfu.check_heap_properties(1);
        for i in 1..5 {
            lfu.insert(i, 2 * i);
            lfu.check_heap_properties(i + 1);
        }
        for i in 1..5 {
            for j in i..5 {
                assert_eq!(lfu.get(&j), Some(&(2 * j)));
                lfu.check_heap_properties(5);
            }
        }

        // Add several one-time values, removing record for &10
        for i in 11..21 {
            lfu.insert(i, i);
            lfu.check_heap_properties(5);
        }

        lfu.insert(0, 0);
        lfu.check_heap_properties(5);
        for i in 0..5 {
            let heap_elem = unsafe { &(*lfu.heap.as_ptr())[i] };
            assert_eq!(heap_elem, &(i, i as u32));
        }
    }
}
