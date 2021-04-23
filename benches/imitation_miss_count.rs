// This benchmark imitates the very same behavior as the imitation.rs one, but instead of measuring
// time, we count the number of cache misses.
// With the EACH_THREAD benchmarks, this enables us to just run all the 'threads' sequentially,
// without stalling on cache miss, because all 'threads' behave simply sequentially.

use caches::lru::LRUCache as LRU;
use caches::rr::RRCache as RR;
use caches::qq::QCache as QQ;
use rand::{thread_rng, Rng};
use std::ptr;
use std::sync::Mutex;
use std::thread;
use std::time::{Duration, Instant};

const DATA_LENGTH: usize = 800;
static mut GENERATED_DATA: *const Vec<u64> = ptr::null();
// the total number of possible cache records
const MEM_SIZE: usize = 64;
// how long a thread sleeps after a cache miss
// (to imitate access to HDD)
const MISS_WAIT: Duration = Duration::from_millis(10);
const THREAD_COUNTS: [usize; 5] = [1, 2, 4, 8, 16];
// the number of samples taken for the 'lock' benchmarks
const SAMPLE_SIZE: usize = 10;

static mut MISS_COUNT: *const Mutex<u32> = ptr::null();

static mut RR_LOCK: *const Mutex<RR<u64, ()>> = ptr::null();
static mut LRU_LOCK: *const Mutex<LRU<u64, ()>> = ptr::null();
static mut QQ_LOCK: *const Mutex<QQ<u64, ()>> = ptr::null();

// MACROS SUPPLYING GENERAL BENCHMARKED BEHAVIOR:

// iterate generated data with a sequential cache
macro_rules! iterate_data_basic {
    ($cache:expr, $start_idx:expr, $step:expr, $miss_count:expr) => {
        let mut idx = $start_idx;
        while idx < DATA_LENGTH {
            let key = unsafe {
                (*GENERATED_DATA)[idx]
            };

            if $cache.get(&key).is_none() {
                // cache miss
                *$miss_count += 1;

                $cache.insert(key, ());
            }
            idx += $step;
        }
    };
}

// iterate the data with one cache behind a mutex
macro_rules! iterate_data_lock {
    ($cache:expr, $start_idx:expr, $step:expr) => {
        let mut idx = $start_idx;
        while idx < DATA_LENGTH {
            let key = unsafe {
                (*GENERATED_DATA)[idx]
            };

            let mut cache_guard = (*$cache).lock().unwrap();
            if (*cache_guard).get(&key).is_none() {
                // cache miss
                unsafe {
                    *(*MISS_COUNT).lock().unwrap() += 1
                }
                // Sleeping here isn't absolutely necessary, but it is kept so that the behavior is
                // absolutely identical with the one in 'imitation.rs'
                thread::sleep(MISS_WAIT);

                (*cache_guard).insert(key, ());
            }
            idx += $step;
        }
    };
}

macro_rules! perform_each {
    ($thread_count:expr, $caches:expr, $miss_count:expr) => {
        for i in 0..$thread_count {
            iterate_data_basic!(
                $caches[i],
                i,
                $thread_count,
                $miss_count
            );
        }
    };
}

macro_rules! perform_lock {
    ($thread_count:expr, $cache:expr, $as:ty) => {
        let mut handles = Vec::with_capacity($thread_count);
        for i in 0..$thread_count {
            let join_handle = std::thread::spawn(move || {
                iterate_data_lock!(
                    unsafe {
                        ($cache as *mut Mutex<$as>).as_mut().unwrap()
                    },
                    i,
                    $thread_count
                );
            });
            handles.push(join_handle);
        }
        for handle in handles {
            handle.join().unwrap();
        }
    };
}

macro_rules! bench_lock {
    ($bench_name:expr, $cache:expr, $const_cache:expr, $as:ty) => {
        println!("");
        for thread_count in THREAD_COUNTS.iter() {
            // prepare cache and miss count
            let cache = Box::into_raw(Box::new(
                Mutex::new($cache)
            ));
            unsafe {
                $const_cache = cache;
            }
            let mock_count = Box::into_raw(Box::new(Mutex::new(0)));
            let miss_count = Box::into_raw(Box::new(Mutex::new(0)));

            // Run once without counting misses to fill cache
            unsafe {
                MISS_COUNT = mock_count;
            }
            perform_lock!(*thread_count, $const_cache, $as);
            // Now 'SAMPLE_SIZE' times with counting
            unsafe {
                MISS_COUNT = miss_count;
            }
            for _ in 0..SAMPLE_SIZE {
                perform_lock!(*thread_count, $const_cache, $as);
            }
            
            unsafe {
                Box::from_raw(cache);
                Box::from_raw(mock_count);
            }
            let misses = unsafe {
                *(*Box::from_raw(miss_count)).lock().unwrap()
            };
            let mean = misses as f64 / SAMPLE_SIZE as f64;
            println!(
                "{}/{}: Out of {} cache searches, there were a mean of {} misses.",
                $bench_name,
                thread_count,
                DATA_LENGTH,
                mean
            );
        }
    };
}

macro_rules! bench_each {
    ($bench_name:expr, $new_cache:expr) => {
        println!("");
        for thread_count in THREAD_COUNTS.iter() {
            // prepare the caches and miss count
            let mut caches = Vec::with_capacity(*thread_count);
            for _ in 0..*thread_count {
                caches.push($new_cache(thread_count));
            }
            let mut mock_count = 0;
            let mut miss_count = 0;

            // Run once without counting misses to fill the caches
            perform_each!(*thread_count, &mut caches, &mut mock_count);
            // Now with miss counting
            perform_each!(*thread_count, &mut caches, &mut miss_count);

            println!(
                "{}/{}: Out of {} cache searches, there were {} misses.",
                $bench_name,
                thread_count,
                DATA_LENGTH,
                miss_count
            );
        }
    };
}

fn rr_lock() {
    bench_lock!(
        "random_replacement-lock",
        RR::new(MEM_SIZE),
        RR_LOCK,
        RR<u64, ()>
    );
}

fn lru_lock() {
    bench_lock!(
        "LRU-lock",
        LRU::new(MEM_SIZE),
        LRU_LOCK,
        LRU<u64, ()>
    );
}

fn qq_lock() {
    bench_lock!(
        "2Q-lock",
        QQ::new(
            MEM_SIZE / 4,
            MEM_SIZE / 4,
            MEM_SIZE / 2
        ),
        QQ_LOCK,
        QQ<u64, ()>
    );
}

fn rr_each() {
    bench_each!(
        "random_replacement-each_thread",
        |thread_count| {
            RR::new(MEM_SIZE / thread_count)
        }
    );
}

fn lru_each() {
    bench_each!(
        "LRU-each_thread",
        |thread_count| {
            LRU::new(MEM_SIZE / thread_count)
        }
    );
}

fn qq_each() {
    bench_each!(
        "2Q-each_thread",
        |thread_count| {
            QQ::new(
                MEM_SIZE / thread_count / 4,
                MEM_SIZE / thread_count / 4,
                MEM_SIZE / thread_count / 2
            )
        }
    );
}

fn main() {
    prepare_data();

    // benchmarks with a single cache behind a mutex:
    rr_lock();
    lru_lock();
    qq_lock();

    // benchmarks where each thread has its own cache:
    rr_each();
    lru_each();
    qq_each();
     
    println!("");
}

fn prepare_data() {
    let unique_uid_count = 19;
    let og_access_count = 57;
    let mut indices = [0; 13];
    let mut rng = thread_rng();

    let mut generated = Box::new(Vec::with_capacity(DATA_LENGTH));
    for _ in 0..DATA_LENGTH {
        let choice = rng.gen_range(0, 13);
        let elem = (unique_uid_count * choice) as u64 + ACCESS_UIDS[indices[choice]];
        (*generated).push(elem);
        indices[choice] = (indices[choice] + 1) % og_access_count;
    }
    unsafe {
        GENERATED_DATA = Box::into_raw(generated);
    }
}

const ACCESS_UIDS: [u64; 57] = [ 0, 0, 0, 0, 0, 0, 4, 0, 0, 0, 4, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 0,
    11, 6, 15, 10, 1, 5, 9, 13, 12, 7, 16, 8, 14, 0, 18, 18, 0, 11, 18, 2, 3, 0, 18, 3, 0, 1, 18, 2, 3, 0, 3 ];
