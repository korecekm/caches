use caches::lru_transactional::LRUCache as LRUTransactional;
use caches::lru_transactional::{LRUWriteTxn, LRUReadTxn};
use caches::lru::LRUCache as LRU;
use rand::{thread_rng, Rng};
use criterion::*;
use std::ptr;
use std::time::{Duration, Instant};

const LOCAL_CACHE_SIZE: usize = 32;
const RECORDS_TOTAL: usize = 832;
// this should be uncommented once the benchmark is well-tuned
//const THREAD_COUNTS: [usize; 4] = [4, 8, 12, 16];
const THREAD_COUNTS: [usize; 1] = [ 8 ];

// how long a thread sleeps after a cache miss
// (to imitate access to HDD)
const MISS_WAIT: Duration = Duration::from_millis(10);
// how many 'streams' of our real-life 57-element data access sample will
// participate for our generated data
const STREAM_COUNT: usize = 800;
const DATA_LENGTH: usize = 196608;
static mut GENERATED_DATA: *const Vec<u64> = ptr::null();

static mut LRUS: *const Vec<LRU<u64, ()>> = ptr::null();
static mut LRU_GLOBAL: *const LRUTransactional<u64, ()> = ptr::null();

macro_rules! sequential_iter {
    ($thread_count:expr, $thread_order:expr, $sleep:expr) => {
        let segment_length = DATA_LENGTH / $thread_count;
        let segment_start = $thread_order * segment_length;
        let segment_end = segment_start + segment_length;

        let lru = unsafe {
            &mut (*(LRUS as *mut Vec<LRU<u64, ()>>))[$thread_order]
        };
        for i in segment_start..segment_end {
            let key = unsafe { (*GENERATED_DATA)[i] };

            if lru.get(&key).is_none() {
                // cache miss
                if $sleep {
                    std::thread::sleep(MISS_WAIT);
                }
                lru.insert(key, ());
            }
        }
    };
}

macro_rules! transactional_iter {
    ($thread_count:expr, $thread_order:expr) => {
        // important 'constants':
        // the length of the segment of GENERATED_DATA that needs to be
        // processed by this thread (or rather all threads at this thread count)
        let segment_length = DATA_LENGTH / $thread_count;
        // for how many GENERATED_DATA element this thread has write privilege
        let write_length = segment_length / $thread_count / 2;
        let segment_start = $thread_order * segment_length;
        let write_start = segment_start + ((segment_length / $thread_count) * $thread_order);
        let write_end = write_start + write_length;

        let mut local_cache = LRU::new(LOCAL_CACHE_SIZE);
        let global_cache = unsafe {
            &mut *(LRU_GLOBAL as *mut LRUTransactional<u64, ()>)
        };
        // first part of the segment without write privilege
        for i in segment_start..write_start {
            let key = unsafe { (*GENERATED_DATA)[i] };

            if global_cache.read().get(&key).is_none()
                && local_cache.get(&key).is_none()
            {
                // cache miss
                std::thread::sleep(MISS_WAIT);
                local_cache.insert(key, ());
            }
        }
        // the part where our thread has write privilege
        let mut write_txn = global_cache.write();
        for i in write_start..write_end {
            let key = unsafe { (*GENERATED_DATA)[i] };

            if write_txn.get(&key).is_none() {
                if local_cache.extract(&key).is_some() {
                    // the key was present in local cache
                    // insert it into the global (transactional) one
                    write_txn.insert(key, ());
                } else {
                    // cache miss
                    std::thread::sleep(MISS_WAIT);
                    local_cache.insert(key, ());
                }
            }
        }
        write_txn.commit();
        // the rest (no write privilege)
        for i in write_end..(segment_start + segment_length) {
            let key = unsafe { (*GENERATED_DATA)[i] };

            if global_cache.read().get(&key).is_none()
                && local_cache.get(&key).is_none()
            {
                // cache miss
                std::thread::sleep(MISS_WAIT);
                local_cache.insert(key, ());
            }
        }
    };
}

// A macro that iterates all GENERATED_DATA without sleeping on cache miss to
// fill the transactional LRU
macro_rules! fill_transactional {
    ($cache_write:expr) => {
        for elem in unsafe { (*GENERATED_DATA).iter() } {
            if $cache_write.get(elem).is_none() {
                $cache_write.insert(*elem, ());
            }
        }
        $cache_write.commit();
    };
}

pub fn local_lrus(c: &mut Criterion) {
    prepare_data();

    let mut group = c.benchmark_group("LRUs-local");
    group.sample_size(10);
    for thread_count in THREAD_COUNTS.iter() {
        group.bench_with_input(
            BenchmarkId::from_parameter(thread_count),
            thread_count,
            |b, &threads| {
                b.iter_custom(|iters| {
                    // Prepare the caches
                    let mut cache_vector = Box::new(Vec::with_capacity(threads));
                    for _ in 0..threads {
                        (*cache_vector).push(LRU::new(RECORDS_TOTAL / threads));
                    }
                    let caches = Box::into_raw(cache_vector);
                    unsafe {
                        LRUS = caches
                    }

                    // Run once to fill the caches
                    for t in 0..threads {
                        sequential_iter!(threads, t, false);
                    }
                    // Now 'iters' times, measuring time
                    let start = Instant::now();
                    for _ in 0..iters {
                        let mut handles = Vec::with_capacity(threads);
                        for t in 0..threads {
                            let join_handle = std::thread::spawn(move || {
                                sequential_iter!(threads, t, true);
                            });
                            handles.push(join_handle);
                        }
                        for handle in handles {
                            handle.join().unwrap();
                        }
                    }

                    let elapsed_duration = start.elapsed();
                    unsafe {
                        Box::from_raw(caches);
                    }
                    elapsed_duration
                })
            }
        );
    }
    group.finish();
}

pub fn transactional_lru(c: &mut Criterion) {
    prepare_data();

    let mut group = c.benchmark_group("LRU-transactional");
    group.sample_size(10);
    for thread_count in THREAD_COUNTS.iter() {
        group.bench_with_input(
            BenchmarkId::from_parameter(thread_count),
            thread_count,
            |b, &threads| {
                b.iter_custom(|iters| {
                    // Create the transactional cache and fill it
                    let cache = Box::new(LRUTransactional::new(RECORDS_TOTAL - (threads * LOCAL_CACHE_SIZE)));
                    fill_transactional!((*cache).write());
                    let cache = Box::into_raw(cache);
                    unsafe {
                        LRU_GLOBAL = cache;
                    }

                    // Now run the benchmark 'iters' times and measure the duration
                    let start = Instant::now();
                    for _ in 0..iters {
                        let mut handles = Vec::with_capacity(threads);
                        for thread_idx in 0..threads {
                            let join_handle = std::thread::spawn(move || {
                                transactional_iter!(threads, thread_idx);
                            });
                            handles.push(join_handle);
                        }
                        for handle in handles {
                            handle.join().unwrap();
                        }
                    }

                    let elapsed_duration = start.elapsed();
                    unsafe {
                        Box::from_raw(cache);
                    }
                    elapsed_duration
                })
            }
        );
    }
    group.finish();
}

criterion_group!(transactional, transactional_lru);
criterion_group!(sequential, local_lrus);
criterion_main!(transactional, sequential);


// This is how the real-usecase sample is expanded: since the sample includes keys from 0 to 18,
// we are able to increment each by 19 and get the same sequence with disjunct keys.
// In this way, we work with 'STREAM_COUNT' identical sequences on different keys.. we 'merge' them
// together randomly to reach a sequence of a total of DATA_LENGTH elements (once any of these
// 'streams' reaches the 57th element it has, it just overflows to the beginning again)

fn prepare_data() {
    if unsafe { !GENERATED_DATA.is_null() } {
        return;
    }

    let unique_uid_count = 19;
    let og_access_count = 57;
    let mut indices = [0; STREAM_COUNT];
    let mut rng = thread_rng();

    let mut generated = Box::new(Vec::with_capacity(DATA_LENGTH));
    for _ in 0..DATA_LENGTH {
        let choice = rng.gen_range(0, STREAM_COUNT);
        let elem = (unique_uid_count * choice) as u64 + ACCESS_UIDS[indices[choice]];
        (*generated).push(elem);
        indices[choice] = (indices[choice] + 1) % og_access_count;
    }
    unsafe {
        GENERATED_DATA = Box::into_raw(generated);
    }
}

const ACCESS_UIDS: [u64; 57] = [
    0, 0, 0, 0, 0, 0, 4, 0, 0, 0, 4, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 0, 11, 6,
    15, 10, 1, 5, 9, 13, 12, 7, 16, 8, 14, 0, 18, 18, 0, 11, 18, 2, 3, 0, 18, 3, 0, 1, 18, 2, 3, 0,
    3,
];
