// This benchmark builds on 57 real life database queries. Their original type is ignored though
// and all are turned into searches.
// Since the original sample only includes 57 queries of 19 different UIDs, it's expanded for our
// purposes (more on the generation in it's comments towards the end of this file).
// Only one Vec of keys (GENERATED_DATA) is generated for all benchmarks (so all of them work with
// the same data). Then there are two types of benchmarks:
// 1) LOCK: There is simply one cache DS in a mutex that all threads use;
// 2) EACH_THREAD: Each thread has it's own cache and can therefore function without any
//    synchronization needed, the data is split between these threads, so each takes care of the
//    same portion of it.. on the other hand, these caches are also smaller accordingly.
//
// Both types are then run with different numbers of threads (these are the parameters of our
// benchmarks, ie. LRU-each_thread/8 means there are 8 threads splitting the data with 8 separate,
// smaller, caches).
//
// The MEM_SIZE constant states the total maximum number of records in all used caches (ie. the
// LOCK benchmarks use a cache with a maximum of MEM_SIZE records and the EACH_THREADs split this
// number uniformly between all threads)
//
// Both the random replacement and LRU data structures only need to know their capacity to be
// created. The 2Q cache on the other hand needs to know the size of its two logic queues.
// We use this primitive solution to this problem: the MEM_SIZE, divided by any thread count that
// we benchmark, is always divisible by 4, and the first and second 2Q queues take a fourth of this
// number, while the final LRU queue in the 2Q takes the rest (a half)
// (notice that with the last thread count, 16, each thread has only 4 records to work with, so
// there's just one record in the first and second queues in each 2Q, and only 2 records in the
// main queue)

use caches::lru::LRUCache as LRU;
use caches::qq::QCache as QQ;
use caches::rr::RRCache as RR;
use criterion::*;
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

static mut RRS: *const Vec<RR<u64, ()>> = ptr::null();
static mut LRUS: *const Vec<LRU<u64, ()>> = ptr::null();
static mut QQS: *const Vec<QQ<u64, ()>> = ptr::null();

static mut RR_LOCK: *const Mutex<RR<u64, ()>> = ptr::null();
static mut LRU_LOCK: *const Mutex<LRU<u64, ()>> = ptr::null();
static mut QQ_LOCK: *const Mutex<QQ<u64, ()>> = ptr::null();

// MACROS SUPPLYING GENERAL BENCHMARKED BEHAVIOR:

// iterates through the data to be processed without any synchronization
// (ie. what the EACH_THREAD benchmarks do inside every thread)
macro_rules! iterate_data_basic {
    ($cache:expr, $start_idx:expr, $step:expr) => {
        let mut idx = $start_idx;
        while idx < DATA_LENGTH {
            let key = unsafe { (*GENERATED_DATA)[idx] };

            if $cache.get(&key).is_none() {
                // cache miss
                thread::sleep(MISS_WAIT);

                $cache.insert(key, ());
            }
            // only each thread_count-th key is processed, so that every thread
            // has the same workload
            idx += $step;
        }
    };
}

// Iterates through the data, but now the given $cache is a Mutex with a cache
// (ie. what the LOCK benchmarks use)
macro_rules! iterate_data_lock {
    ($cache:expr, $start_idx:expr, $step:expr) => {
        let mut idx = $start_idx;
        while idx < DATA_LENGTH {
            let key = unsafe { (*GENERATED_DATA)[idx] };

            let mut cache_guard = (*$cache).lock().unwrap();
            if (*cache_guard).get(&key).is_none() {
                // cache miss
                thread::sleep(MISS_WAIT);

                (*cache_guard).insert(key, ());
            }
            // only each thread_count-th key is processed, so that every thread
            // has the same workload
            idx += $step;
        }
    };
}

// Spawn the required number of threads for an EACH_THREAD benchmark and join onto those threads so
// that we know when all data has been processed.
macro_rules! perform_each {
    ($thread_count:expr, $caches:expr, $as:ty) => {
        let mut handles = Vec::with_capacity($thread_count);
        for i in 0..$thread_count {
            let join_handle = std::thread::spawn(move || {
                iterate_data_basic!(
                    unsafe { &mut ($caches as *mut Vec<$as>).as_mut().unwrap()[i] },
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

// Spawn the required number of threads for a LOCK benchmark and join onto those threads so that we
// know when all data has been processed.
macro_rules! perform_lock {
    ($thread_count:expr, $cache:expr, $as:ty) => {
        let mut handles = Vec::with_capacity($thread_count);
        for i in 0..$thread_count {
            let join_handle = std::thread::spawn(move || {
                iterate_data_lock!(
                    unsafe { ($cache as *mut $as).as_mut().unwrap() },
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

// The actual benchmark functions can be simplified with a single macro definition for all
// (similarly to what's done in the imitation_miss_count benchmark)
// but that's not done yet for the sake of better code clarity

pub fn rr_each(c: &mut Criterion) {
    if unsafe { GENERATED_DATA.is_null() } {
        prepare_data();
    }

    let mut group = c.benchmark_group("random_replacement-each_thread");
    group.sample_size(10);
    for thread_count in THREAD_COUNTS.iter() {
        group.bench_with_input(
            BenchmarkId::from_parameter(thread_count),
            thread_count,
            |b, &threads| {
                b.iter_custom(|iters| {
                    // prepare the caches
                    let mut cache_vector = Box::new(Vec::with_capacity(threads));
                    for _ in 0..threads {
                        (*cache_vector).push(RR::new(MEM_SIZE / threads));
                    }
                    let caches = Box::into_raw(cache_vector);
                    unsafe {
                        RRS = caches;
                    }

                    // run once without measuring time to fill the caches
                    perform_each!(threads, RRS, RR<u64, ()>);
                    // now 'iters' times and measure the time
                    let start = Instant::now();
                    for _ in 0..iters {
                        perform_each!(threads, RRS, RR<u64, ()>);
                    }

                    let elapsed_duration = start.elapsed();
                    unsafe {
                        Box::from_raw(caches);
                    }
                    elapsed_duration
                })
            },
        );
    }
    group.finish();
}

pub fn lru_each(c: &mut Criterion) {
    if unsafe { GENERATED_DATA.is_null() } {
        prepare_data();
    }

    let mut group = c.benchmark_group("LRU-each_thread");
    group.sample_size(10);
    for thread_count in THREAD_COUNTS.iter() {
        group.bench_with_input(
            BenchmarkId::from_parameter(thread_count),
            thread_count,
            |b, &threads| {
                b.iter_custom(|iters| {
                    // prepare the caches
                    let mut cache_vector = Box::new(Vec::with_capacity(threads));
                    for _ in 0..threads {
                        (*cache_vector).push(LRU::new(MEM_SIZE / threads));
                    }
                    let caches = Box::into_raw(cache_vector);
                    unsafe {
                        LRUS = caches;
                    }

                    // run once without measuring time to fill the caches
                    perform_each!(threads, LRUS, LRU<u64, ()>);
                    // now 'iters' times and measure the time
                    let start = Instant::now();
                    for _ in 0..iters {
                        perform_each!(threads, LRUS, LRU<u64, ()>);
                    }

                    let elapsed_duration = start.elapsed();
                    unsafe {
                        Box::from_raw(caches);
                    }
                    elapsed_duration
                })
            },
        );
    }
    group.finish();
}

pub fn qq_each(c: &mut Criterion) {
    if unsafe { GENERATED_DATA.is_null() } {
        prepare_data();
    }

    let mut group = c.benchmark_group("2Q-each_thread");
    group.sample_size(10);
    for thread_count in THREAD_COUNTS.iter() {
        group.bench_with_input(
            BenchmarkId::from_parameter(thread_count),
            thread_count,
            |b, &threads| {
                b.iter_custom(|iters| {
                    // prepare the caches
                    let mut cache_vector = Box::new(Vec::with_capacity(threads));
                    for _ in 0..threads {
                        (*cache_vector).push(QQ::new(
                            MEM_SIZE / threads / 4,
                            MEM_SIZE / threads / 4,
                            MEM_SIZE / threads / 2,
                        ));
                    }
                    let caches = Box::into_raw(cache_vector);
                    unsafe {
                        QQS = caches;
                    }

                    // run once without measuring time to fill the caches
                    perform_each!(threads, QQS, QQ<u64, ()>);
                    // now 'iters' times and measure the time
                    let start = Instant::now();
                    for _ in 0..iters {
                        perform_each!(threads, QQS, QQ<u64, ()>);
                    }

                    let elapsed_duration = start.elapsed();
                    unsafe {
                        Box::from_raw(caches);
                    }
                    elapsed_duration
                })
            },
        );
    }
    group.finish();
}

pub fn rr_lock(c: &mut Criterion) {
    if unsafe { GENERATED_DATA.is_null() } {
        prepare_data();
    }

    let mut group = c.benchmark_group("random_replacement-lock");
    group.sample_size(10);
    for thread_count in THREAD_COUNTS.iter() {
        group.bench_with_input(
            BenchmarkId::from_parameter(thread_count),
            thread_count,
            |b, &threads| {
                b.iter_custom(|iters| {
                    // prepare the cache
                    let cache = Box::into_raw(Box::new(Mutex::new(RR::new(MEM_SIZE))));
                    unsafe {
                        RR_LOCK = cache;
                    }

                    // run once without measuring time to fill cache
                    perform_lock!(threads, RR_LOCK, Mutex<RR<u64, ()>>);
                    // now 'iters' times and measure the time
                    let start = Instant::now();
                    for _ in 0..iters {
                        perform_lock!(threads, RR_LOCK, Mutex<RR<u64, ()>>);
                    }

                    let elapsed_duration = start.elapsed();
                    unsafe {
                        Box::from_raw(cache);
                    }
                    elapsed_duration
                })
            },
        );
    }
    group.finish();
}

pub fn lru_lock(c: &mut Criterion) {
    if unsafe { GENERATED_DATA.is_null() } {
        prepare_data();
    }

    let mut group = c.benchmark_group("LRU-lock");
    group.sample_size(10);
    for thread_count in THREAD_COUNTS.iter() {
        group.bench_with_input(
            BenchmarkId::from_parameter(thread_count),
            thread_count,
            |b, &threads| {
                b.iter_custom(|iters| {
                    // prepare the cache
                    let cache = Box::into_raw(Box::new(Mutex::new(LRU::new(MEM_SIZE))));
                    unsafe {
                        LRU_LOCK = cache;
                    }

                    // run once without measuring time to fill cache
                    perform_lock!(threads, LRU_LOCK, Mutex<LRU<u64, ()>>);
                    // now 'iters' times and measure the time
                    let start = Instant::now();
                    for _ in 0..iters {
                        perform_lock!(threads, LRU_LOCK, Mutex<LRU<u64, ()>>);
                    }

                    let elapsed_duration = start.elapsed();
                    unsafe {
                        Box::from_raw(cache);
                    }
                    elapsed_duration
                })
            },
        );
    }
    group.finish();
}

pub fn qq_lock(c: &mut Criterion) {
    if unsafe { GENERATED_DATA.is_null() } {
        prepare_data();
    }

    let mut group = c.benchmark_group("2Q-lock");
    group.sample_size(10);
    for thread_count in THREAD_COUNTS.iter() {
        group.bench_with_input(
            BenchmarkId::from_parameter(thread_count),
            thread_count,
            |b, &threads| {
                b.iter_custom(|iters| {
                    //prepare the cache
                    let cache = Box::into_raw(Box::new(Mutex::new(QQ::new(
                        MEM_SIZE / 4,
                        MEM_SIZE / 4,
                        MEM_SIZE / 2,
                    ))));
                    unsafe {
                        QQ_LOCK = cache;
                    }

                    // run once without measuring time to fill cache
                    perform_lock!(threads, QQ_LOCK, Mutex<QQ<u64, ()>>);
                    // now 'iters' times and measure the time
                    let start = Instant::now();
                    for _ in 0..iters {
                        perform_lock!(threads, QQ_LOCK, Mutex<QQ<u64, ()>>);
                    }

                    let elapsed_duration = start.elapsed();
                    unsafe {
                        Box::from_raw(cache);
                    }
                    elapsed_duration
                })
            },
        );
    }
    group.finish();
}

criterion_group!(lock, rr_lock, lru_lock, qq_lock);
criterion_group!(each, rr_each, lru_each, qq_each);
criterion_main!(lock, each);

// This is how the real-usecase sample is expanded: since the sample includes keys from 0 to 18,
// we are able to increment each by 19 and get the same sequence with disjunct keys.
// In this way, we work with 13 identical sequences on different keys.. we 'merge' them together
// randomly to reach a sequence of a total of DATA_LENGTH elements (once any of these 'streams'
// reaches the 57th element it has, it just overflows to the beginning again)

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

const ACCESS_UIDS: [u64; 57] = [
    0, 0, 0, 0, 0, 0, 4, 0, 0, 0, 4, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 0, 11, 6,
    15, 10, 1, 5, 9, 13, 12, 7, 16, 8, 14, 0, 18, 18, 0, 11, 18, 2, 3, 0, 18, 3, 0, 1, 18, 2, 3, 0,
    3,
];
