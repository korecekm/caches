use crossbeam::queue::ArrayQueue;
use caches::clock_pro::CLOCKProCache as Cache;
use caches::list::DLList;
use caches::clock_pro_associative::CLOCKProAssociative as CacheAssoc;
use caches::clock_pro_transactional::CLOCKProTransactional as CacheTxnal;
use std::fs::File;
use std::io::{BufRead, BufReader};
use std::ptr;
use criterion::*;
use std::sync::{Arc, Mutex};
use std::time::{Duration, Instant};
use std::sync::mpsc::*;

// CODE UNDER CONSTRUCTION
// 
// # Current behavior:
// 
// We only benchmark based on the one access log we have that actually specifies transaction IDs,
// which is the one provided by Mr. Carabas.
// 
// The file is first pulled into our WORKLOAD vector by the `prepare_data` function. Then the
// benchmarks themselves take place. The Criterion benchmark functions are the ones with the
// '_bench' suffix. Those run multiple threads that perform the transactions in the WORKLOAD.
// The code that's performed is in the macros with the 'perform_' prefix. Those take thair tasks
// from an spmc channel that actually sends indexes in the WORKLOAD Vec, not the Transaction
// structs themselves.

// We will work with the workload described in
// "benches/access_logs/WORKLOAD_FILENAME.txn"
const WORKLOAD_FILENAME: &str = "Carabas";
// This vector will contain the whole workload in memory
static mut WORKLOAD: *const Vec<Transaction<u16>> = ptr::null();
// The max. total number of records cached at one time by the cache(s) that we
// benchmark
const CACHE_SIZE_TOTAL: usize = 3456;
// All concurrent strategies (single_thread_bench is a separate benchmark) will
// be measured one by one with these thread counts.
const THREAD_COUNTS: [usize; 4] = [2, 4, 8, 12];

// Global variables containing the data structures used by the worker threads
static mut CACHE_SINGLE_THREAD: *const Cache<u16, ()> = ptr::null();
static mut CACHE_LOCK: *const Mutex<Cache<u16, ()>> = ptr::null();
static mut CACHE_ASSOCIATIVE: *const CacheAssoc<u16, ()> = ptr::null();
static mut PER_THREAD_MOD_LOCK: *const Mutex<()> = ptr::null();
static mut CACHES_PER_THREAD: [*const Cache<u16, ()>; 32] = [ptr::null(); 32];
static mut CACHE_TRANSACTIONAL: *const CacheTxnal<u16, ()> = ptr::null();

// A macro to occupy any cache having a proper general get and insert function
// with the keys in our workload.
// We use this to initiate the caches, so that the benchmarks run on caches
// that already have a working cached set.
macro_rules! fill_generic {
    ($cache:expr) => {
        for txn in unsafe { (*WORKLOAD).iter() } {
            for key in txn.iter_keys() {
                // We simply hit accessed keys and insert those that are
                // missing.
                if $cache.get(key).is_none() {
                    $cache.insert(*key, ());
                }
            }
        }
    };
}

// This takes care of search-only transactions in strategies where we have
// unique access to all the keys in question (all but PER-THREAD currently)
macro_rules! perform_search_only_generic {
    ($cache:expr, $txn:expr) => {
        // We simulate search-only transactions by performing searches on all
        // the keys and adding those that are missing.
        for uid in $txn.key_vec.iter() {
            if $cache.get(uid).is_none() {
                $cache.insert(*uid, ());
            }
        }
    };
}

// This takes care of modifying transactions in strategies where we have
// unique access to all keys in question and getting a mutable reference to a
// record suffices for its modification (all but PER-THREAD and TXNAL).
macro_rules! perform_mod_generic {
    ($cache:expr, $txn:expr) => {
        // In modifying transactions, we get mutable references to
        // the records that get modified and immutable to the rest
        // (adding the records when missing).
        for i in 0..$txn.key_vec.len() {
            let uid = $txn.key_vec[i];
            if $txn.mod_vec[i] {
                if $cache.get_mut(&uid).is_none() {
                    $cache.insert(uid, ());
                }
            } else {
                if $cache.get(&uid).is_none() {
                    $cache.insert(uid, ());
                }
            }
        }
    };
}

// This macro describes the function of the single thread spawned by our single
// thread benchmark. It does what all the concurrent benchmarks do, but only
// using one sequential cache, so that it can be used to compare our concurrent
// benchmarks with the performance of just one thread.
macro_rules! perform_single_thread {
    // The parameter is a reference (Arc) to the SPMC queue that distributes
    // WORKLOAD indexes to be processed.
    ($query_queue:expr) => {
        // We borrow the cache mutably for convenience
        let cache = unsafe {
            &mut *(CACHE_SINGLE_THREAD as *mut Cache<u16, ()>)
        };
        // Iterate through all the transactions and perform their simulation
        loop {
            if let Some(txn_idx) = $query_queue.pop() {
                if txn_idx == u32::MAX {
                    // u32::MAX is a special value that signifies the end of
                    // the workload
                    break;
                }
                let txn = unsafe { &(*WORKLOAD)[txn_idx as usize] };
                match txn {
                    Transaction::Search(st) => perform_search_only_generic!(cache, st),
                    Transaction::Modify(mt) => perform_mod_generic!(cache, mt),
                }
            }
        }
    };
}

// This macro describes the funtion of a worker thread in the LOCK strategy.
macro_rules! perform_lock {
    // The parameter is a reference (Arc) to the SPMC queue that distributes
    // WORKLOAD indexes to be processed.
    ($query_queue:expr) => {
        // Iterate through all the transactions and perform their simulation
        loop {
            if let Some(txn_idx) = $query_queue.pop() {
                if txn_idx == u32::MAX {
                    // u32::MAX is a special value that signifies the end of
                    // the workload
                    break;
                }
                // Lock the cache to be able to work with it
                let mut cache_guard = unsafe {
                    (*CACHE_LOCK).lock().unwrap()
                };
                let txn = unsafe { &(*WORKLOAD)[txn_idx as usize] };
                match txn {
                    Transaction::Search(st) => perform_search_only_generic!(*cache_guard, st),
                    Transaction::Modify(mt) => perform_mod_generic!(*cache_guard, mt),
                }
            }
        }
    };
}

// This macro describes the funtion of a worker thread in the ASSOCIATIVE
// strategy.
macro_rules! perform_assoc {
    // The parameter is a reference (Arc) to the SPMC queue that distributes
    // WORKLOAD indexes to be processed.
    ($query_queue:expr) => {
        // Iterate through all the transactions and perform their simulation
        loop {
            if let Some(txn_idx) = $query_queue.pop() {
                if txn_idx == u32::MAX {
                    // u32::MAX is a special value that signifies the end of
                    // the workload
                    break;
                }
                let txn = unsafe { &(*WORKLOAD)[txn_idx as usize] };
                // Lock the necessary cache "slots" for this transaction
                let mut cache_guard = unsafe {
                    (*CACHE_ASSOCIATIVE).generate_mut_guard(txn.get_key_vec())
                };
                match txn {
                    Transaction::Search(st) => perform_search_only_generic!(cache_guard, st),
                    Transaction::Modify(mt) => perform_mod_generic!(cache_guard, mt),
                }
            }
        }
    };
}

// A macro that describes the function of our dedicated invalidation thread in
// the per-thread strategy
// (which receives invalidation requests and distributes them to all the
// affected threads)
macro_rules! per_thread_invalidation_thread {
    ($recv:expr, $thread_sends:expr) => {
        while let Ok((write_thread, inval_vec)) = $recv.recv() {
            // Send the invalidation requests to all threads except the one
            // which issued it
            for i in 0..$thread_sends.len() {
                if i != write_thread {
                    // The send may actually fail, legally, since some threads
                    // may have already finished their execution.
                    let _result = $thread_sends[i].send(inval_vec.clone());
                }
            }
        }
    };
}

/// Takes care of invalidating all the necessary records of a thread's cache
/// (when using the per-thread strategy)
fn per_thread_invalidate(cache: &mut Cache<u16, ()>, invalidate_recv: &Receiver<Vec<u16>>) -> bool {
    let mut invalidated = false;
    while let Ok(key_vec) = invalidate_recv.try_recv() {
        invalidated = true;
        for key in key_vec.iter() {
            cache.evict(key);
        }
    }
    invalidated
}

/// Takes care of a read-only transaction in the per-thread strategy
fn per_thread_read(cache: &mut Cache<u16, ()>, txn: &SearchTxn<u16>, invalidate_recv: &Receiver<Vec<u16>>) {
    // We need to work with a valid state of the cache, so if some keys in
    // our transaction are missing, forcing us to insert them, while we
    // also get an invalidation request, we rerun the whole transaction
    // (some of the used keys may have been invalidated)
    // This requires all accessed keys to fit into the cache! Although we
    // may quite safely assume they will, this is exploitable.
    for uid in txn.key_vec.iter() {
        if cache.get(uid).is_none() {
            let invalidated = per_thread_invalidate(cache, invalidate_recv);
            cache.insert(*uid, ());
            if invalidated {
                // Rerun the transaction
                per_thread_read(cache, txn, invalidate_recv);
                break;
            }
        }
    }
}

/// Takes care of a transaction that modifies records in the per-thread strategy
fn per_thread_mod(thread_idx: usize, cache: &mut Cache<u16, ()>, txn: &ModifyTxn<u16>, invalidate_send: &SyncSender<(usize, Vec<u16>)>) {
    let mod_guard = unsafe { (*PER_THREAD_MOD_LOCK).lock().unwrap() };
    // We will store all the keys we modify into a Vec to be able to send
    // an invalidation request. We simply iterate it for potential
    // duplicates, quadratic time is no issue here as the Vec is expected
    // to be short.
    let mut inval_vec = Vec::new();
    for i in 0..txn.key_vec.len() {
        let uid = txn.key_vec[i];
        if txn.mod_vec[i] {
            // We perform a modification on the record
            if cache.get_mut(&uid).is_none() {
                cache.insert(uid, ());
            }
            // Add the key (UID) to the inval_vec, if it isn't already
            // present
            let mut present = false;
            for invalid_uid in inval_vec.iter() {
                if *invalid_uid == uid {
                    present = true;
                    break;
                }
            }
            if !present {
                inval_vec.push(uid);
            }
        } else {
            // Non-modifying record access
            if cache.get(&uid).is_none() {
                cache.insert(uid, ());
            }
        }
    }
    invalidate_send.send((thread_idx, inval_vec)).unwrap();
    // Just to be clear about only now dropping the guard
    drop(mod_guard);
}

// This macro describes the funtion of a worker thread in the PER-THREAD
// strategy.
macro_rules! perform_per_thread {
    // This macro needs to know the index (order doing spawning) of its thread,
    // a reference (Arc) to the scheduler SPMC queue as all other strategies
    // and also the infrastructure of our invalidation mechanism, that is, the
    // send stream to our invalidation thread and also the recv end of the
    // invalidation stream leading from that thread.
    ($thread_idx:expr, $query_queue:expr, $invalidate_send:expr, $invalidate_recv:expr) => {
        let cache = unsafe {
            &mut *(CACHES_PER_THREAD[$thread_idx] as *mut Cache<u16, ()>)
        };
        loop {
            if let Some(txn_idx) = $query_queue.pop() {
                if txn_idx == u32::MAX {
                    // u32::MAX is a special value that signifies the end of
                    // the workload
                    break;
                }
                // Perform potential invalidations to stay up to date
                per_thread_invalidate(cache, &$invalidate_recv);
                let txn = unsafe { &(*WORKLOAD)[txn_idx as usize] };
                match txn {
                    Transaction::Search(st) => per_thread_read(cache, st, &$invalidate_recv),
                    Transaction::Modify(mt) => per_thread_mod($thread_idx, cache, mt, &$invalidate_send),
                }
            }
        }
    };
}

// Macro that takes care of a transaction at `txn_idx` of our WORKLOAD, using a
// write transaction.
macro_rules! txnal_write {
    ($txn_idx:expr, $hit_list:expr) => {
        let mut write = unsafe {
            (*CACHE_TRANSACTIONAL).write()
        };
        // Hit all records that couldn't have been hit with only the read txn
        while let Some(key) = $hit_list.pop_back() {
            write.get(&key);
        }
        // Perform given transaction
        match unsafe { &(*WORKLOAD)[$txn_idx as usize] } {
            // We simulate search-only transactions by performing
            // searches on all the keys and adding those that are
            // missing.
            Transaction::Search(st) => perform_search_only_generic!(write, st),
            Transaction::Modify(mt) => {
                // The transactional approach requires modifications to be
                // performed using the `reinsert` method.
                // So here, we only ger references for search queries (adding
                // the missing ones) and simulate modifications to records by
                // 'reinserting' them.
                for i in 0..mt.key_vec.len() {
                    let uid = mt.key_vec[i];
                    if write.get(&uid).is_none() {
                        write.insert(uid, ());
                    } else if mt.mod_vec[i] {
                        write.reinsert(uid, ());
                    }
                }
            }
        }
        write.commit();
    };
}

macro_rules! perform_txnal {
    // The parameter is a reference (Arc) to the SPMC queue that distributes
    // WORKLOAD indexes to be processed.
    ($query_queue:expr) => {
        // When only using a read txn, 
        let mut hit_list = DLList::new();
        'iter_txns: loop {
            if let Some(txn_idx) = $query_queue.pop() {
                if txn_idx == u32::MAX {
                    // u32::MAX is a special value that signifies the end of
                    // the workload
                    break;
                }
                // Too many cache hits went unmarked globally, we take a write
                // transaction now to perform the cache hits.
                if hit_list.size > 400 {
                    txnal_write!(txn_idx, &mut hit_list);
                    continue;
                }
                let txn = unsafe { &(*WORKLOAD)[txn_idx as usize] };
                if txn.does_modify() {
                    txnal_write!(txn_idx, &mut hit_list);
                } else {
                    // Transaction that only performs reads
                    let read = unsafe {
                        (*CACHE_TRANSACTIONAL).read()
                    };
                    for uid in txn.iter_keys() {
                        if read.get(uid).is_none() {
                            // Key not present in the cache's read snapshot. We
                            // need a cache write transaction for this.
                            txnal_write!(txn_idx, &mut hit_list);
                            continue 'iter_txns;
                        }
                    }
                    // The transaction was successful, so we record all the cache
                    // hits (to mark them globally once we get the write privilege)
                    for uid in txn.iter_keys() {
                        hit_list.push_front(*uid);
                    }
                }
            }
        }
    };
}

/// A benchmark function that aims to compare the performance of the concurrent
/// strategies with the performance of one thread with a simple sequential
/// cache.
pub fn single_thread_bench(c: &mut Criterion) {
    // Prepare the workload into our WORKLOAD Vec
    prepare_data();
    // Prepare the benchmark group
    let mut group = c.benchmark_group("SINGLE_THREAD");
    group.sample_size(10);

    // Prepare the cache
    let mut cache = Cache::new(CACHE_SIZE_TOTAL);
    fill_generic!(cache);
    unsafe {
        CACHE_SINGLE_THREAD = Box::into_raw(Box::new(cache));
    }
    // Perform the benchmark itself:
    group.bench_function(format!("single_thread/{}", WORKLOAD_FILENAME), move |b| {
        b.iter_custom(|iters| {
            let mut duration = Duration::from_micros(0);
            for _ in 0..iters {
                // First, prepare the queue to send the workload through
                let workload_size = unsafe { (*WORKLOAD).len() };
                let query_queue = Arc::new(ArrayQueue::new(workload_size + 1));
                // Spawn the worker thread
                let queue_ref = query_queue.clone();
                let join_handle = std::thread::spawn(move || {
                    perform_single_thread!(queue_ref);
                });

                // We only start measuring the time once we send requests
                let start = Instant::now();
                for txn_idx in 0..workload_size {
                    query_queue.push(txn_idx as u32).unwrap();
                }
                // Finish the broadcast:
                query_queue.push(u32::MAX).unwrap();

                join_handle.join().unwrap();
                duration += start.elapsed();
            }
            duration
        })
    });
    // Free the cache
    unsafe {
        Box::from_raw(CACHE_SINGLE_THREAD as *mut Cache<u16, ()>);
    }
}

/// The LOCK benchmark function.
pub fn lock_bench(c: &mut Criterion) {
    // Prepare the workload into our WORKLOAD Vec
    prepare_data();
    // Prepare the benchmark group
    let mut group = c.benchmark_group("LOCK");
    group.sample_size(10);

    // Prepare the cache for the threads to access.
    let mut cache = Cache::new(CACHE_SIZE_TOTAL);
    fill_generic!(cache);
    unsafe {
        CACHE_LOCK = Box::into_raw(Box::new(Mutex::new(cache)));
    }
    // Perform the benchmark one by one for all chosen thread counts.
    for thread_count in THREAD_COUNTS.iter() {
        group.bench_with_input(
            BenchmarkId::from_parameter(format!("{}/{}", WORKLOAD_FILENAME, thread_count)),
            thread_count,
            |b, thread_count| {
                b.iter_custom(|iters| {
                    let mut duration = Duration::from_micros(0);
                    for _ in 0..iters {
                        // First, prepare the queue to send the workload through
                        let workload_size = unsafe { (*WORKLOAD).len() };
                        let query_queue = Arc::new(ArrayQueue::new(workload_size + *thread_count));
                        let mut handles = Vec::new();
                        // Spawn the worker threads
                        for _ in 0..*thread_count {
                            let queue_ref = query_queue.clone();
                            let join_handle = std::thread::spawn(move || {
                                perform_lock!(queue_ref);
                            });
                            handles.push(join_handle);
                        }

                        // We only start measuring the time once we send requests
                        let start = Instant::now();
                        for txn_idx in 0..workload_size {
                            query_queue.push(txn_idx as u32).unwrap();
                        }
                        // Stop the broadcast.
                        // (by sending the u32::MAX value, signifying workload
                        // end, once for each spawned threads)
                        for _ in 0..*thread_count {
                            query_queue.push(u32::MAX).unwrap();
                        }

                        for handle in handles {
                            handle.join().unwrap();
                        }
                        // The duration from this iteration gets added to the
                        // sum for this `iters` count
                        duration += start.elapsed();
                    }
                    duration
                })
            }
        );
    }
    // Free the cache
    unsafe {
        Box::from_raw(CACHE_LOCK as *mut Mutex<Cache<u16, ()>>);
    }
}

pub fn associative_bench(c: &mut Criterion) {
    // Prepare the workload into our WORKLOAD Vec
    prepare_data();
    // Prepare the benchmark group
    let mut group = c.benchmark_group("ASSOCIATIVE");
    group.sample_size(10);

    // Perform the benchmark one by one for all chosen thread counts.
    for thread_count in THREAD_COUNTS.iter() {
        // Prepare the cache
        let cache = CacheAssoc::new(CACHE_SIZE_TOTAL, thread_count * 3);
        let mut unique_guard = cache.generate_unique_access_guard();
        fill_generic!(unique_guard);
        drop(unique_guard);
        unsafe {
            CACHE_ASSOCIATIVE = Box::into_raw(Box::new(cache));
        }
        // The bench function itself:
        group.bench_with_input(
            BenchmarkId::from_parameter(format!("{}/{}", WORKLOAD_FILENAME, thread_count)),
            thread_count,
            |b, thread_count| {
                b.iter_custom(|iters| {
                    let mut duration = Duration::from_micros(0);
                    for _ in 0..iters {
                        // First, prepare the queue to send the workload through
                        let workload_size = unsafe { (*WORKLOAD).len() };
                        let query_queue = Arc::new(ArrayQueue::new(workload_size + *thread_count));
                        let mut handles = Vec::new();
                        for _ in 0..*thread_count {
                            let queue_ref = query_queue.clone();
                            let join_handle = std::thread::spawn(move || {
                                perform_assoc!(queue_ref);
                            });
                            handles.push(join_handle);
                        }

                        // We only start measuring the time once we send requests
                        let start = Instant::now();
                        for txn_idx in 0..workload_size {
                            query_queue.push(txn_idx as u32).unwrap();
                        }
                        // Stop the broadcast.
                        // (by sending the u32::MAX value, signifying workload
                        // end, once for each spawned threads)
                        for _ in 0..*thread_count {
                            query_queue.push(u32::MAX).unwrap();
                        }

                        for handle in handles {
                            handle.join().unwrap();
                        }
                        // The duration from this iteration gets added to the
                        // sum for this `iters` count
                        duration += start.elapsed();
                    }
                    duration
                })
            }
        );
        // Free the cache
        unsafe {
            Box::from_raw(CACHE_ASSOCIATIVE as *mut CacheAssoc<u16, ()>);
        }
    }
}

pub fn per_thread_bench(c: &mut Criterion) {
    // Prepare the workload into our WORKLOAD Vec
    prepare_data();
    // Prepare the benchmark group
    let mut group = c.benchmark_group("PER-THREAD");
    group.sample_size(10);

    // Perform the benchmark one by one for all chosen thread counts.
    for thread_count in THREAD_COUNTS.iter() {
        // Prepare the caches
        for i in 0..*thread_count {
            let mut cache = Cache::new(CACHE_SIZE_TOTAL / *thread_count);
            fill_generic!(cache);
            unsafe {
                CACHES_PER_THREAD[i] = Box::into_raw(Box::new(cache));
            }
        }
        unsafe {
            // Also prepare the write lock
            PER_THREAD_MOD_LOCK = Box::into_raw(Box::new(Mutex::new(())));
        }
        // The bench function itself:
        group.bench_with_input(
            BenchmarkId::from_parameter(format!("{}/{}", WORKLOAD_FILENAME, thread_count)),
            thread_count,
            |b, thread_count| {
                b.iter_custom(|iters| {
                    let mut duration = Duration::from_micros(0);
                    for _ in 0..iters {
                        // First, prepare the queue to send the workload through
                        let workload_size = unsafe { (*WORKLOAD).len() };
                        let query_queue = Arc::new(ArrayQueue::new(workload_size + *thread_count));
                        // Also prepare the invalidation mechanism:
                        // A "rendezvous" channel for record invalidation requests
                        let (inval_send, inval_recv) = sync_channel(0);
                        // Vector containing "send"s to specific threads
                        let mut thread_sends = Vec::new();
                        // Spawn all the worker threads
                        let mut handles = Vec::new();
                        for thread_idx in 0..*thread_count {
                            let queue_ref = query_queue.clone();
                            let inval_send = inval_send.clone();
                            let (thread_inval_send, thread_inval_recv) = channel();
                            thread_sends.push(thread_inval_send);
                            let join_handle = std::thread::spawn(move || {
                                perform_per_thread!(thread_idx, queue_ref, inval_send, thread_inval_recv);
                            });
                            handles.push(join_handle);
                        }
                        drop(inval_send);

                        // Spawn the dedicated invalidation broadcast thread.
                        let invalidation_thread_handle = std::thread::spawn(move || {
                            per_thread_invalidation_thread!(inval_recv, thread_sends);
                        });

                        // We only start measuring the time once we send requests
                        let start = Instant::now();
                        for txn_idx in 0..workload_size {
                            query_queue.push(txn_idx as u32).unwrap();
                        }
                        // Stop the broadcast
                        // (by sending the u32::MAX value, signifying workload
                        // end, once for each spawned threads)
                        for _ in 0..*thread_count {
                            query_queue.push(u32::MAX).unwrap();
                        }

                        for handle in handles {
                            handle.join().unwrap();
                        }
                        // The duration from this iteration gets added to the
                        // sum for this `iters` count
                        duration += start.elapsed();
                        invalidation_thread_handle.join().unwrap();
                    }
                    duration
                })
            }
        );
        // Free the caches and the write lock
        unsafe {
            for i in 0..*thread_count {
                Box::from_raw(CACHES_PER_THREAD[i] as *mut Cache<u16, ()>);
            }
            Box::from_raw(PER_THREAD_MOD_LOCK as *mut Mutex<()>);
        }
    }
}

pub fn transactional_bench(c: &mut Criterion) {
    // Prepare the workload into our WORKLOAD Vec
    prepare_data();
    // Prepare the benchmark group
    let mut group = c.benchmark_group("TRANSACTIONAL");
    group.sample_size(10);

    // Prepare the cache for the threads to access.
    let cache = CacheTxnal::new(CACHE_SIZE_TOTAL);
    let mut write_txn = cache.write();
    fill_generic!(write_txn);
    write_txn.commit();
    unsafe {
        CACHE_TRANSACTIONAL = Box::into_raw(Box::new(cache));
    }
    // Perform the benchmark one by one for all chosen thread counts.
    for thread_count in THREAD_COUNTS.iter() {
        group.bench_with_input(
            BenchmarkId::from_parameter(format!("{}/{}", WORKLOAD_FILENAME, thread_count)),
            thread_count,
            |b, thread_count| {
                b.iter_custom(|iters| {
                    let mut duration = Duration::from_micros(0);
                    for _ in 0..iters {
                        // First, prepare the queue to send the workload
                        // through
                        let workload_size = unsafe { (*WORKLOAD).len() };
                        let query_queue = Arc::new(ArrayQueue::new(workload_size + *thread_count));
                        let mut handles = Vec::new();
                        for _ in 0..*thread_count {
                            let queue_ref = query_queue.clone();
                            let join_handle = std::thread::spawn(move || {
                                perform_txnal!(queue_ref);
                            });
                            handles.push(join_handle);
                        }

                        // We only start measuring the time once we send requests
                        let start = Instant::now();
                        for txn_idx in 0..workload_size {
                            query_queue.push(txn_idx as u32).unwrap();
                        }
                        // Stop the broadcast
                        // (by sending the u32::MAX value, signifying workload
                        // end, once for each spawned threads)
                        for _ in 0..*thread_count {
                            query_queue.push(u32::MAX).unwrap();
                        }

                        for handle in handles {
                            handle.join().unwrap();
                        }
                        // The duration from this iteration gets added to the
                        // sum for this `iters` count
                        duration += start.elapsed();
                    }
                    duration
                })
            }
        );
    }
    // Free the cache
    unsafe {
        Box::from_raw(CACHE_TRANSACTIONAL as *mut CacheTxnal<u16, ()>);
    }
}

criterion_group!(single_thread, single_thread_bench);
criterion_group!(concurrent, lock_bench, associative_bench, per_thread_bench, transactional_bench);
criterion_main!(single_thread, concurrent);

/// In our abstraction, a search-only transaction is fully described by the
/// sequence of accessed records (keys).
struct SearchTxn<K> {
    key_vec: Vec<K>,
}

/// A transaction that modifies records contains the accessed keys, and also
/// information on which records are modified.
struct ModifyTxn<K> {
    key_vec: Vec<K>,
    // `mod_vec` has the same length as `key_vec`, for each key, this says if
    // the record is modified (then the corresponding element is `true`)
    mod_vec: Vec<bool>,
}

/// General transaction enum. Can be of two types
/// * Search: a search-only transaction
/// * Modify: a transaction that modifies some records
enum Transaction<K> {
    Search(SearchTxn<K>),
    Modify(ModifyTxn<K>),
}

impl<K> Transaction<K> {
    /// Does this transaction modify some records?
    fn does_modify(&self) -> bool {
        match self {
            Self::Search(_) => false,
            Self::Modify(_) => true,
        }
    }

    /// Iterates over references to all the keys accessed by this transaction.
    fn iter_keys(&self) -> std::slice::Iter<'_, K> {
        self.get_key_vec().iter()
    }

    /// Returns a reference to the key vector of this transaction, no matter
    /// the type.
    fn get_key_vec(&self) -> &Vec<K> {
        match self {
            Self::Search(st) => &st.key_vec,
            Self::Modify(mt) => &mt.key_vec,
        }
    }
}

/// This function is responsible for obtaining our workload from our custom txn
/// file located in "benches/access_logs/[WORKLOAD_FILENAME].txn" and storing
/// it inside `WORKLOAD`. If the workload is already in memory, it doesn't go
/// through this process again, so we can call this function at the beginning
/// of each benchmark without wasting resources.
fn prepare_data() {
    // If not yet prepared, initiate the WORKLOAD vector and get a mutable
    // reference to it, for convenience.
    unsafe {
        if !WORKLOAD.is_null() {
            return;
        }
        WORKLOAD = Box::into_raw(Box::new(Vec::new()));
    }
    let workload = unsafe {
        &mut *(WORKLOAD as *mut Vec<Transaction<u16>>)
    };
    // Read from the file
    let filepath = format!("benches/access_logs/{}.txn", WORKLOAD_FILENAME);
    let file = File::open(filepath).unwrap();
    let mut lines = BufReader::new(file).lines().enumerate();

    // We parse the file line by line, each 'T' begins a new transaction.
    let first_line = lines.next().unwrap().1.unwrap();
    assert_eq!(first_line.as_bytes()[0], 'T' as u8);
    let mut txn_mod = if first_line.as_bytes()[2] == 'M' as u8 {
        true
    } else {
        false
    };
    // vectors that will tell us what keys are accessed and if they are
    // modified by the access or not
    let mut txn_query_types = Vec::new();
    let mut txn_keys = Vec::new();
    for (_, line) in lines {
        let line = line.unwrap();
        let identifier = line.as_bytes()[0] as char;
        if identifier == 'T' {
            // This line starts a new transaction.
            // Process the current transaction
            workload.push(prepare_txn_struct(txn_mod, txn_keys, txn_query_types));
            // Init a new transaction
            txn_mod = if line.as_bytes()[2] == 'M' as u8 {
                true
            } else {
                false
            };
            txn_query_types = Vec::new();
            txn_keys = Vec::new();
        } else {
            // This line specifies a query inside the current transaction.
            // Is this a modification query?
            let query_type = if line.as_bytes()[0] == 'M' as u8 {
                true
            } else {
                false
            };
            let query_id = line[2..line.len()].parse().unwrap();
            txn_query_types.push(query_type);
            txn_keys.push(query_id);
        }
    }
    // Finish the processing of the last transaction
    workload.push(prepare_txn_struct(txn_mod, txn_keys, txn_query_types));
}

// Simply takes all components of a transaction and turns them into an actual
// Transaction struct
fn prepare_txn_struct<K>(modifies: bool, key_vec: Vec<K>, mod_vec: Vec<bool>) -> Transaction<K> {
    match modifies {
        true => Transaction::Modify(ModifyTxn {
            key_vec,
            mod_vec,
        }),
        false => Transaction::Search(SearchTxn {
            key_vec
        }),
    }
}
