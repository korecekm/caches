extern crate multiqueue;
use caches::lru::LRUCache as LRU;
use caches::lru_transactional::LRUCache as LRUTransactional;
use std::fs::File;
use std::io::{BufRead, BufReader};
use std::sync::Mutex;
use criterion::*;
use std::ptr;
use std::time::{Duration, Instant};
use ahash::AHasher;
use std::hash::Hash;
use std::hash::Hasher;

// This benchmark tests the concurrent scalability of caching DSes (currently
// only LRU variants). For that, it always works with caches of enough capacity
// to hold the whole dataset, ie. it really only measures the overhead of the
// replacement logic and of the concurrency strategy - there are three
// benchmarked strategies:
// * "DIVIDE": Each thread has its own cache and its own stream of keys to
//   query; a "query scheduler" must be employed to distribute the keys between
//   the threads - it does so by hashing the keys and divides the hashes into
//   uniformly large "buckets". This way, each cache always works with 'its own'
//   key subset (in the case ). This behavior aims to simulate random
//   distribution of keys between threads.
// * "LOCK": There is just one 'large' cache behind a mutex, which each thread
//   has to lock to be able to use the cache. The threads take the queries from
//   a single SPMC queue whenever they are done with their last query.
// * "TRANSACTIONAL": we have a transactional cache and the working threads use
//   a read transaction to access it. They refresh this transaction after a set
//   number of queries, READ_TXN_RENEW_RATE, which is to simulate an imagined
//   behavior with the transactional approach, where just one thread has write
//   privilege and the others need to refresh regularly. As with the LOCK
//   approach, the workload is distributed via an SPMC queue.
// 
// In all three cases, the cache(s) is first filled with all the values that are
// about to be queried, so that we only measure succesfull read behavior.
// 
// Implementation-wise, the datasets are taken from files of our specific
// format, located in the access_logs directory. These logs are transferred
// into RAM (specifically, ACCESSES) via the prepare_data function before we
// start measuring and stay there until all measurements are finished and the
// benchmarking processes heap is freed.

// THIS CODE IS STILL UNDER CONSTRUCTION. It is not very readable at this stage.

const LOG_COUNT: usize = 2;
const ACCESS_FILENAMES: [&str; LOG_COUNT] = ["output", "Carabas"];
static mut ACCESSES: [*const Vec<u16>; LOG_COUNT] = [ptr::null(), ptr::null()];
static mut UNIQUE_KEY_COUNT: [usize; LOG_COUNT] = [0, 0];
const THREAD_COUNTS: [usize; 5] = [4, 8, 16, 24, 32];

static mut LRUS: *const Vec<LRU<u16, ()>> = ptr::null();
static mut LRU_LOCK: *const Mutex<LRU<u16, ()>> = ptr::null();
static mut LRU_TRANSACTIONAL: *const LRUTransactional<u16, ()> = ptr::null();

macro_rules! hash_choice {
    ($key:expr, $cache_count:expr) => {{
        let mut hasher = AHasher::new_with_keys(3, 7);
        $key.hash(&mut hasher);
        let divisor = u64::MAX / $cache_count as u64;
        (hasher.finish() / divisor) as usize
    }}
}

macro_rules! work_divide {
    ($caches:expr, $cache_type:ty, $idx:expr, $query_stream:expr) => {
        for key in $query_stream {
            assert!(unsafe {
                (*($caches as *mut Vec<$cache_type>))[$idx].get(&key).is_some()
            });
        }
    };
}

macro_rules! work_lock {
    ($cache:expr, $query_stream:expr) => {
        for key in $query_stream {
            assert!(unsafe {
                (*$cache).lock().unwrap().get(&key).is_some()
            });
        }
    };
}

const READ_TXN_RENEW_RATE: usize = 40;
macro_rules! work_transactional {
    ($cache:expr, $query_stream:expr) => {
        let mut read_txn = unsafe {
            (*$cache).read()
        };
        let mut idx = 0;
        for key in $query_stream {
            if idx == READ_TXN_RENEW_RATE {
                idx = 0;
                read_txn = unsafe {
                    (*$cache).read()
                }
            }
            assert!(read_txn.get(&key).is_some());
            idx += 1;
        }
    };
}


pub fn lru_divide(c: &mut Criterion) {
    prepare_data();
    let mut group = c.benchmark_group("LRU-divide");
    group.sample_size(10);

    for i in 0..LOG_COUNT {
        for thread_count in THREAD_COUNTS.iter() {
            unsafe {
                LRUS = Box::into_raw(Box::new(Vec::new()));
                for _ in 0..*thread_count {
                    (*(LRUS as *mut Vec<LRU<u16, ()>>)).push(LRU::new(UNIQUE_KEY_COUNT[i]));
                }
                for j in 0..UNIQUE_KEY_COUNT[i] {
                    (*(LRUS as *mut Vec<LRU<u16, ()>>))[hash_choice!(j, *thread_count)].insert(j as u16, ());
                }
            }
            group.bench_with_input(
                BenchmarkId::from_parameter(format!("{}/{}", ACCESS_FILENAMES[i], thread_count)),
                thread_count,
                |b, &threads| {
                    b.iter_custom(|iters| {
                        let mut duration = Duration::from_micros(0);
                        for _ in 0..iters {
                            let mut sends = Vec::new();
                            let mut handles = Vec::new();
                            for t in 0..threads {
                                let (send, recv) = multiqueue::broadcast_queue(unsafe { (*ACCESSES[i]).len() as u64 } );
                                sends.push(send);
                                let consumer_stream = recv.add_stream();
                                let join_handle = std::thread::spawn(move || {
                                    work_divide!(LRUS, LRU<u16, ()>, t, consumer_stream);
                                });
                                handles.push(join_handle);
                                recv.unsubscribe();
                            }

                            let start = Instant::now();
                            for a in unsafe { (*ACCESSES[i]).iter() } {
                                sends[hash_choice!(a, threads)].try_send(*a).unwrap();
                            }
                            for send in sends {
                                drop(send);
                            }

                            for handle in handles {
                                handle.join().unwrap();
                            }
                            duration += start.elapsed()
                        }
                        duration
                    })
                }
            );
            unsafe {
                Box::from_raw(LRUS as *mut Vec<LRU<u16, ()>>);
            }
        }
    }
}

pub fn lru_lock(c: &mut Criterion) {
    prepare_data();
    let mut group = c.benchmark_group("LRU-lock");
    group.sample_size(10);

    for i in 0..LOG_COUNT {
        unsafe {
            LRU_LOCK = Box::into_raw(Box::new(Mutex::new(LRU::new(UNIQUE_KEY_COUNT[i]))));
            for j in 0..UNIQUE_KEY_COUNT[i] {
                (*LRU_LOCK).lock().unwrap().insert(j as u16, ());
            }
        }
        for thread_count in THREAD_COUNTS.iter() {
            group.bench_with_input(
                BenchmarkId::from_parameter(format!("{}/{}", ACCESS_FILENAMES[i], thread_count)),
                &thread_count,
                |b, &threads| {
                    b.iter_custom(|iters| {
                        let mut duration = Duration::from_micros(0);
                        for _ in 0..iters {
                            let (send, recv) = multiqueue::broadcast_queue(unsafe { (*ACCESSES[i]).len() as u64 });
                            let consumer_stream = recv.add_stream();
                            let mut handles = Vec::new();
                            for _ in 0..*threads {
                                let stream = consumer_stream.clone();
                                let join_handle = std::thread::spawn(move || {
                                    work_lock!(LRU_LOCK, stream);
                                });
                                handles.push(join_handle);
                            }
                            recv.unsubscribe();

                            let start = Instant::now();
                            for a in unsafe { (*ACCESSES[i]).iter() } {
                                send.try_send(*a).unwrap();
                            }
                            drop(send);
                            
                            for handle in handles {
                                handle.join().unwrap();
                            }
                            duration += start.elapsed();
                        }
                        duration
                    })
                }
            );
        }
        unsafe {
            Box::from_raw(LRU_LOCK as *mut Mutex<LRU<u16, ()>>);
        }
    }
}

pub fn lru_transactional(c: &mut Criterion) {
    prepare_data();
    let mut group = c.benchmark_group("LRU-transactional");
    group.sample_size(10);

    for i in 0..LOG_COUNT {
        unsafe {
            LRU_TRANSACTIONAL = Box::into_raw(Box::new(LRUTransactional::new(UNIQUE_KEY_COUNT[i])));
            let mut write_txn = (*LRU_TRANSACTIONAL).write();
            for j in 0..UNIQUE_KEY_COUNT[i] {
                write_txn.insert(j as u16, ());
            }
            write_txn.commit();
        }
        for thread_count in THREAD_COUNTS.iter() {
            group.bench_with_input(
                BenchmarkId::from_parameter(format!("{}/{}", ACCESS_FILENAMES[i], thread_count)),
                &thread_count,
                |b, &threads| {
                    b.iter_custom(|iters| {
                        let mut duration = Duration::from_micros(0);
                        for _ in 0..iters {
                            let (send, recv) = multiqueue::broadcast_queue(unsafe { (*ACCESSES[i]).len() as u64 });
                            let consumer_stream = recv.add_stream();
                            let mut handles = Vec::new();
                            for _ in 0..*threads {
                                let stream = consumer_stream.clone();
                                let join_handle = std::thread::spawn(move || {
                                    work_transactional!(LRU_TRANSACTIONAL, stream);
                                });
                                handles.push(join_handle);
                            }
                            recv.unsubscribe();

                            let start = Instant::now();
                            for a in unsafe { (*ACCESSES[i]).iter() } {
                                send.try_send(*a).unwrap();
                            }
                            drop(send);

                            for handle in handles {
                                handle.join().unwrap();
                            }
                            duration += start.elapsed();
                        }
                        duration
                    })
                }
            );
        }
        unsafe {
            Box::from_raw(LRU_TRANSACTIONAL as *mut LRUTransactional<u16, ()>);
        }
    }
}


criterion_group!(divide, lru_divide);
criterion_group!(lock, lru_lock);
criterion_group!(transactional, lru_transactional);
criterion_main!(divide, lock, transactional);


fn prepare_data() {
    unsafe {
        if !ACCESSES[0].is_null() {
            // The access logs have already been transferred into our ACCESSES
            // ARRAY
            return;
        }
        for i in 0..LOG_COUNT {
            ACCESSES[i] = Box::into_raw(Box::new(Vec::new()));
        }
    }
    for i in 0..LOG_COUNT {
        let filepath = format!("benches/access_logs/{}.in", ACCESS_FILENAMES[i]);
        let file = File::open(filepath).unwrap();
        let mut lines = BufReader::new(file).lines().enumerate();
        // The first line contains the number of unique keys in the access
        // sample.
        unsafe {
            UNIQUE_KEY_COUNT[i] = lines.next().unwrap().1.unwrap().parse().unwrap();
        }
        for (_, line) in lines {
            let key = line.unwrap().parse().unwrap();
            unsafe {
                (*(ACCESSES[i] as *mut Vec<u16>)).push(key);
            }
        }
    }
}
