use std::hash::Hash;
use std::hash::Hasher;
use ahash::AHasher;

/// A seeded hash hashing into values 0..vec_size
macro_rules! hash {
    ($v:expr, $seed:expr, $vec_size:expr) => {{
        let mut hasher = AHasher::new_with_keys(1, $seed as u128);
        $v.hash(&mut hasher);
        (hasher.finish() as u64) % ($vec_size as u64)
    }};
}

struct Bloom {
    hasher_count: usize,
    vec: Vec<u64>,
    vec_size: u64,
}

impl Bloom {
    /// The actual set hashed into will be 2^vec_size_exp elements big.
    /// vec_size_exp must be at least 6 (although that's very little)
    fn new(vec_size_exp: usize, hasher_count: usize) -> Self {
        let vec_size = 1 << vec_size_exp;
        Self {
            hasher_count,
            vec: vec![0; vec_size / 64],
            vec_size: vec_size as u64,
        }
    }

    pub(crate) fn set_bit(&mut self, bit: u64) {
        let or = 1 << (bit % 64);
        self.vec[(bit / 64) as usize] |= or;
    }

    pub(crate) fn get_bit(&self, bit: u64) -> bool {
        let and = 1 << (bit % 64);
        self.vec[(bit / 64) as usize] & and > 0
    }

    fn insert<V: Hash>(&mut self, value: &V) {
        for s in 0..self.hasher_count {
            self.set_bit(hash!(value, s, self.vec_size));
        }
    }

    fn may_contain<V: Hash>(&self, value: &V) -> bool {
        for s in 0..self.hasher_count {
            if !self.get_bit(hash!(value, s, self.vec_size)) {
                return false;
            }
        }
        true
    }
}


struct CountingBloom {
    hasher_count: usize,
    vec: Vec<u8>,
}

impl CountingBloom {
    /// Values will be hashed into 0..2^vec_size_exp by hasher_count hashers
    fn new(vec_size_exp: usize, hasher_count: usize) -> Self {
        let vec_size = 1 << vec_size_exp;
        Self {
            hasher_count,
            vec: vec![0; vec_size],
        }
    }

    pub(crate) fn inc(&mut self, idx: usize) {
        self.vec[idx] += 1
    }
    
    pub(crate) fn dec(&mut self, idx: usize) {
        self.vec[idx] -= 1
    }

    pub(crate) fn positive(&self, idx: usize) -> bool {
        self.vec[idx] > 0
    }

    fn insert<V: Hash>(&mut self, value: &V) {
        for s in 0..self.hasher_count {
            self.inc(hash!(value, s, self.vec.len()) as usize);
        }
    }

    fn remove<V: Hash>(&mut self, value: &V) {
        for s in 0..self.hasher_count {
            self.dec(hash!(value, s, self.vec.len()) as usize);
        }
    }

    fn may_contain<V: Hash>(&self, value: &V) -> bool {
        for s in 0..self.hasher_count {
            if !self.positive(hash!(value, s, self.vec.len()) as usize) {
                return false;
            }
        }
        true
    }
}

// Test:

#[cfg(test)]
mod test {
    use super::{Bloom, CountingBloom};
    use rand::{thread_rng, Rng};

    #[test]
    fn random() {
        let mut rng = thread_rng();
        let mut bloom = Bloom::new(10, 4);
        
        let range = 100;
        let mut included = vec![false; range];
        let mut false_pos_count = 0;
        // 1 in 4 iterations will insert
        for _ in 0..2000 {
            let choice = rng.gen_range(0, 4);
            let v = rng.gen_range(0, range);
            if choice == 0 {
                bloom.insert(&v);
                included[v] = true;
            } else {
                match included[v] {
                    false => if bloom.may_contain(&v) {
                        false_pos_count += 1;
                    }
                    true => assert!(bloom.may_contain(&v))
                }
            }
        }

        println!("There were {} false positives.", false_pos_count);
    }

    #[test]
    fn random_counting() {
        let mut rng = thread_rng();
        let mut bloom = CountingBloom::new(8, 3);

        let range = 100;
        let mut included = vec![false; range];
        let mut false_pos_count = 0;
        // 2 in 6 iterations an insert, 1 a remove
        for _ in 0..10000 {
            let choice = rng.gen_range(0, 6);
            let v = rng.gen_range(0, range);
            if choice < 2 {
                if !included[v] {
                    bloom.insert(&v);
                    included[v] = true;
                }
            } else if choice == 2 {
                if included[v] {
                    bloom.remove(&v);
                    included[v] = false;
                }
            } else {
                match included[v] {
                    false => if bloom.may_contain(&v) {
                        false_pos_count += 1;
                    }
                    true => assert!(bloom.may_contain(&v))
                }
            }
        }
    }
}
