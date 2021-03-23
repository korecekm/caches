use caches::lru::LRUCache as LRU;
use criterion::*;
use rand::{thread_rng, Rng};
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

pub fn miss_bench(c: &mut Criterion) {
    let miss_count = Mutex::new(0);
    let cache = Mutex::new(LRU::new(CACHE_CAPACITY));
    for k in 0..INIT_RECORD_COUNT {
        (*cache.lock().unwrap()).insert(k, ());
    }

    c.bench_function("lru_misses", move |b| {
        b.iter_custom(|iters| {
            let mut handles = Vec::new();
            for _ in 0..iters {
                let join_handle = thread::spawn(|| {
                    black_box(perform_miss_bench(&cache, &miss_count));
                });
                handles.push(join_handle);
            }
            for handle in handles {
                handle.join();
            }
            Duration::from_secs(*miss_count.lock().unwrap())
        })
    });
}

criterion_group!(miss, miss_bench);
criterion_main!(miss);

fn perform_miss_bench(cache: &Mutex<LRU<usize, ()>>, miss_count: &Mutex<u64>) {
    let mut rng = thread_rng();
    for i in 0..QUERY_COUNT {
        let key = rng.gen_range(0, KEY_MAX + KEY_OVERFLOW) % KEY_MAX;
        if i % INSERT_FREQ == 0 {
            // insert
            (*cache.lock().unwrap()).insert(key, ());
        } else {
            // get
            if (*cache.lock().unwrap()).try_get(&key).is_none() {
                *miss_count.lock().unwrap() += 1;
            }
        }
    }
}
