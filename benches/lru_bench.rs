extern crate caches;
extern crate criterion;
extern crate rand;

use caches::lru::LRUCache as LRU;
use criterion::*;
use rand::{thread_rng, Rng};
use std::ptr;
use std::sync::Mutex;
use std::thread;
use std::time::Duration;

const CACHE_CAPACITY: usize = 5000;
const INIT_RECORD_COUNT: usize = 3000;
// total number of inserts+gets queried by each spawned thread
const QUERY_COUNT: usize = 3000;
const INSERT_FREQ: usize = 20;
// KEY_OVERFLOW < KEY_MAX. values in the [0, KEY_OVERFLOW) range will be twice as likely to occur
const KEY_OVERFLOW: usize = 2000;
const KEY_MAX: usize = 15000; // the (non-inclusive) maximum for generated keys (minimum is 0)

static mut MISS_COUNT: *const Mutex<u64> = ptr::null();
static mut CACHE: *const Mutex<LRU<usize, ()>> = ptr::null();

pub fn miss_bench(c: &mut Criterion) {
    c.bench_function("lru_misses", prepare_miss_bench);
}

criterion_group!(miss, miss_bench);
criterion_main!(miss);

fn prepare_miss_bench(b: &mut Bencher) {
    let miss_count = Mutex::new(0);
    let cache = Mutex::new(LRU::new(CACHE_CAPACITY));
    unsafe {
        MISS_COUNT = &miss_count;
        CACHE = &cache;
    }
    for k in 0..INIT_RECORD_COUNT {
        (*cache.lock().unwrap()).insert(k, ());
    }

    b.iter_custom(|iters| {
        let mut handles = Vec::new();
        for _ in 0..iters {
            let join_handle = thread::spawn(|| {
                black_box(perform_miss_bench());
            });
            handles.push(join_handle);
        }
        for handle in handles {
            handle.join().unwrap();
        }
        Duration::from_secs(*miss_count.lock().unwrap())
    });
}

fn perform_miss_bench() {
    let mut rng = thread_rng();
    for i in 0..QUERY_COUNT {
        let key = rng.gen_range(0, KEY_MAX + KEY_OVERFLOW) % KEY_MAX;
        if i % INSERT_FREQ == 0 {
            // insert
            unsafe {
                (*(*CACHE).lock().unwrap()).insert(key, ());
            }
        } else {
            // get
            unsafe {
                if (*(*CACHE).lock().unwrap()).get(&key).is_none() {
                    *(*MISS_COUNT).lock().unwrap() += 1;
                }
            }
        }
    }
}
