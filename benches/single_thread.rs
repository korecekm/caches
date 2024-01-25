// SPDX-FileCopyrightText: 2024 2023 Martin Koreček
//
// SPDX-License-Identifier: GPL-3.0-or-later

// This benchmark examines the in-memory performance of our implementations of cache replacement
// policy data structures. That is, how long they take to perform several transactions.
// 
// To make the overhead of the benchmark itself similar to the one in the `concurrent` benchmark,
// we perform the cache operations in a separate spawned thread, meaasure the time in the very same
// way as the concurrent benchmark, and also use "Log 2" as the workload.
// 
// We additionally perform a "NULL" benchmark, which doesn't perform any cache operations, and only
// measures how long the iteration through the workload in the separate thread takes without them,
// i.e. what the overhead of the benchmark alone is.

use caches::rr::RRCache as RR;
use caches::lru::LRUCache as LRU;
use caches::lfu::LFUCache as LFU;
use caches::clock::CLOCKCache as CLOCK;
use caches::clock_pro::CLOCKProCache as CLOCKPro;
use caches::lirs::LIRSCache as LIRS;
use caches::qq::QCache as QQ;
use caches::qq_lfu::QQLFUCache as QQLFU;
use caches::arc::ARCache as ARC;
use std::fs::File;
use std::io::{BufRead, BufReader};
use std::ptr;
use std::marker::PhantomData;
use criterion::*;
use crossbeam::queue::ArrayQueue;
use std::time::{Duration, Instant};
use std::sync::Arc;

// We are working with the `/benches/access_logs/Carabas.txn` access log, i.e.
// Log 2
const WORKLOAD_FILENAME: &str = "Carabas";
// The whole access logs will be imported here by `prepare_data` in the form of
// `Transaction` structs.
static mut WORKLOAD: *const Vec<Transaction<u16>> = ptr::null();
// To be able to avoid code repetition via our `generic_bench` macro, while
// also having the currently measured replacement data structure in a global
// variable to use it in a separate thread, we use this unsafe technique of
// storing the data structure in a `()` pointer. When the CACHE is used, the
// type is given ad hoc.
// (so this variable will actually hold a pointer to any caching data structure
// that we currently benchmark)
static mut CACHE: *const () = ptr::null();

// Before running the first iteration of the benchmark, the cache data
// structure is filled by iterating the log's transactions, to not start with
// an empty one and have non-uniform results.
macro_rules! fill_generic {
    ($cache_type:ty) => {
        // Get a mutable reference to our cache
        let cache = unsafe {
            &mut *(CACHE as *mut $cache_type)
        };
        // Iterate the workload and simulate the use of our cache.
        for txn in unsafe { (*WORKLOAD).iter() } {
            for key in txn.iter_keys() {
                // Hit accessed keys; insert the missing ones.
                if cache.get(key).is_none() {
                    cache.insert(*key, ());
                }
            }
        }
    };
}

// Performs the measurement for the current caching data structure in the very
// same way we do it in the main, `concurrent` bench file. We receive indexes
// to the WORKLOAD vector via a concurrent queue. The thread needs to actively
// wait for these indexes and when it receives one, it simulates performing the
// transaction at the given index.
// The end of the workload is represented by sending u32::MAX through the
// queue. That is how the thread knows when to stop the execution
macro_rules! perform_generic {
    ($cache_type:ty, $query_queue:expr) => {
        // Get a mutable reference to our cache
        let cache = unsafe {
            &mut *(CACHE as *mut $cache_type)
        };
        // Loop that actively waits for instructions given through a concurrent
        // queue
        loop {
            if let Some(txn_idx) = $query_queue.pop() {
                if txn_idx == u32::MAX {
                    // The end of the workload
                    break;
                }
                // "Perform" the execution of the transaction at received index
                let txn = unsafe { &(*WORKLOAD)[txn_idx as usize] };
                for key in txn.iter_keys() {
                    if cache.get(key).is_none() {
                        cache.insert(*key, ());
                    }
                }
            }
        }
    };
}

// This makes it possible for `generic_bench` to initiate any type of caching
// data structure, even the ones 'parameterized' with const generics.
// Each type of caching data structure has its own expansion with its
// appropriate keyword identifier. Besides the identifier, the macro only takes
// the size of the cache, and makes an instance of the respective DS.
macro_rules! creation {
    (rr $cache_size:expr) => {
        RR::<u16, ()>::new($cache_size)
    };
    (lru $cache_size:expr) => {
        LRU::<u16, ()>::new($cache_size)
    };
    (lfu $cache_size:expr) => {
        LFU::<u16, (), $cache_size>::new()
    };
    (clock $cache_size:expr) => {
        CLOCK::<u16, (), $cache_size>::new()
    };
    (clock_pro $cache_size:expr) => {
        CLOCKPro::<u16, ()>::new($cache_size)
    };
    (lirs $cache_size:expr) => {
        LIRS::<u16, ()>::new({ $cache_size - 30 }, 30)
    };
    (qq $cache_size:expr) => {
        QQ::<u16, ()>::new(10, { $cache_size / 6 }, { $cache_size - ($cache_size / 6) - 10 })
    };
    (qq_lfu $cache_size:expr) => {
        QQLFU::<u16, (), { $cache_size - ($cache_size / 5 * 2) }>::new($cache_size / 5, $cache_size / 5)
    };
    (arc $cache_size:expr) => {
        ARC::<u16, ()>::new($cache_size)
    };
    // An instance of the "NULL" cache, that only serves to see how much
    // overhead there is with no actual cache operations.
    (null $cache_size:expr) => {
        NullCache::<u16, ()> {
            _phantom_k: PhantomData,
            _phantom_v: PhantomData,
        }
    }
}

// A macro that expands into a full benchmark for a caching data structure. It
// receives a criterion benchmark group and the sizes of caches to benchmark.
// Using our `creation` macro with the appropriate identifier given in
// $cache_id, we are able to instantiate the CACHE, and also free it later. We
// also need to receive the current cache's type.
macro_rules! generic_bench {
    ($bench_group:expr, $cache_id:ident, $cache_type:ty, $($cache_size:expr),*) => {
        // For each given cache_size:
        $(
            // Use the cache size as the input parameter for our benchmark
            $bench_group.bench_with_input(
                BenchmarkId::from_parameter(format!("{}/{}", WORKLOAD_FILENAME, $cache_size)),
                &$cache_size,
                |b, _| {
                    // Create an instance of our cache using the `creation`
                    // macro with the given identifier and cache size
                    unsafe {
                        CACHE = Box::into_raw(Box::new(creation!($cache_id $cache_size))) as *const ();
                    }
                    // Run the workload on the cache to fill the data structure first
                    fill_generic!($cache_type);

                    // The measurement itself: criterion gives us the number of
                    // iterations (iters) that we shall run the measurement.
                    // The combined duration they take is summed up and
                    // returned.
                    b.iter_custom(|iters| {
                        let mut duration = Duration::from_micros(0);
                        // Perform the measurement `iters` times
                        for _ in 0..iters {
                            // Prepare the concurrent queue through which we
                            // send the indexes in WORKLOAD of transactions
                            // that shall be performed.
                            let workload_size = unsafe { (*WORKLOAD).len() };
                            let query_queue = Arc::new(ArrayQueue::new(workload_size + 1));

                            // Create the reference to the queue for the thread
                            // we spawn
                            let queue_ref = query_queue.clone();
                            // Spawn the thread that will perform the measured
                            // behavior.
                            let join_handle = std::thread::spawn(move || {
                                perform_generic!($cache_type, queue_ref);
                            });

                            // We only start measuring time once we actually
                            // send instructions to the worker thread
                            let start = Instant::now();
                            // Make the worker thread perform all the
                            // transactions
                            for txn_idx in 0..workload_size {
                                query_queue.push(txn_idx as u32).unwrap();
                            }
                            // End the instruction "stream"
                            query_queue.push(u32::MAX).unwrap();

                            join_handle.join().unwrap();
                            // Once the worker thread has finished, we
                            // increment the time it took to our total duration
                            duration += start.elapsed();
                        }
                        // Returned the total duration we measured
                        duration
                    });

                    // Free the cache data structure in our static variable
                    unsafe {
                        Box::from_raw(CACHE as *mut $cache_type);
                    }
                }
            );
        )*
    };
}

// Benchmark function for 'Random replacement'
fn rr_bench(c: &mut Criterion) {
    prepare_data();
    let mut bench_group = c.benchmark_group("Random replacement");
    bench_group.sample_size(10);

    // Cache sizes can be given in a variadic way, as we don't need const
    // generics here
    generic_bench!(bench_group, rr, RR<u16, ()>, 200, 1000, 2000, 3456);

    bench_group.finish();
}

// Benchmark function for 'LRU'
fn lru_bench(c: &mut Criterion) {
    prepare_data();
    let mut bench_group = c.benchmark_group("LRU");
    bench_group.sample_size(10);

    // Cache sizes can be given in a variadic way, as we don't need const
    // generics here
    generic_bench!(bench_group, lru, LRU<u16, ()>, 200, 1000, 2000, 3456);

    bench_group.finish();
}

// Benchmark function for 'LFU'
fn lfu_bench(c: &mut Criterion) {
    prepare_data();
    let mut bench_group = c.benchmark_group("LFU");
    bench_group.sample_size(10);
    
    // The LFU uses const generics for its 'parameterization', which forces us
    // to expand `generic_bench` multiple times, with the appropriate types
    // given.
    generic_bench!(bench_group, lfu, LFU<u16, (), 200>, 200);
    generic_bench!(bench_group, lfu, LFU<u16, (), 1000>, 1000);
    generic_bench!(bench_group, lfu, LFU<u16, (), 2000>, 2000);
    generic_bench!(bench_group, lfu, LFU<u16, (), 3456>, 3456);

    bench_group.finish();
}

// Benchmark function for 'CLOCK'
fn clock_bench(c: &mut Criterion) {
    prepare_data();
    let mut bench_group = c.benchmark_group("CLOCK");
    bench_group.sample_size(10);

    // The CLOCK uses const generics for its 'parameterization', which forces
    // us to expand `generic_bench` multiple times, with the appropriate types
    // given.
    generic_bench!(bench_group, clock, CLOCK<u16, (), 200>, 200);
    generic_bench!(bench_group, clock, CLOCK<u16, (), 1000>, 1000);
    generic_bench!(bench_group, clock, CLOCK<u16, (), 2000>, 2000);
    generic_bench!(bench_group, clock, CLOCK<u16, (), 3456>, 3456);
    
    bench_group.finish();
}

// Benchmark function for 'CLOCK-Pro'
fn clock_pro_bench(c: &mut Criterion) {
    prepare_data();
    let mut bench_group = c.benchmark_group("CLOCK-Pro");
    bench_group.sample_size(10);

    // Cache sizes can be given in a variadic way, as we don't need const
    // generics here
    generic_bench!(bench_group, clock_pro, CLOCKPro<u16, ()>, 200, 1000, 2000, 3456);
    
    bench_group.finish();
}

// Benchmark function for 'LIRS'
fn lirs_bench(c: &mut Criterion) {
    prepare_data();
    let mut bench_group = c.benchmark_group("LIRS");
    bench_group.sample_size(10);

    // Cache sizes can be given in a variadic way, as we don't need const
    // generics here
    generic_bench!(bench_group, lirs, LIRS<u16, ()>, 200, 1000, 2000, 3456);
    
    bench_group.finish();
}

// Benchmark function for '2Q'
fn qq_bench(c: &mut Criterion) {
    prepare_data();
    let mut bench_group = c.benchmark_group("2Q");
    bench_group.sample_size(10);

    // Cache sizes can be given in a variadic way, as we don't need const
    // generics here
    generic_bench!(bench_group, qq, QQ<u16, ()>, 200, 1000, 2000, 3456);
    
    bench_group.finish();
}

// Benchmark function for '2Q-LFU'
fn qq_lfu_bench(c: &mut Criterion) {
    prepare_data();
    let mut bench_group = c.benchmark_group("2Q-LFU");
    bench_group.sample_size(10);

    // The 2Q-LFU uses const generics to define the size of its main (priority)
    // queue, which forces us to expand `generic_bench` multiple times, with
    // the appropriate types given.
    generic_bench!(bench_group, qq_lfu, QQLFU<u16, (), { 200 - (200 / 5 * 2) }>, 200);
    generic_bench!(bench_group, qq_lfu, QQLFU<u16, (), { 1000 - (1000 / 5 * 2) }>, 1000);
    generic_bench!(bench_group, qq_lfu, QQLFU<u16, (), { 2000 - (2000 / 5 * 2) }>, 2000);
    generic_bench!(bench_group, qq_lfu, QQLFU<u16, (), { 3456 - (3456 / 5 * 2) }>, 3456);
    
    bench_group.finish();
}

// Benchmark function for 'ARC'
fn arc_bench(c: &mut Criterion) {
    prepare_data();
    let mut bench_group = c.benchmark_group("ARC");
    bench_group.sample_size(10);

    // Cache sizes can be given in a variadic way, as we don't need const
    // generics here
    generic_bench!(bench_group, arc, ARC<u16, ()>, 200, 1000, 2000, 3456);
    
    bench_group.finish();
}


/// A mock cache-like data structure that does nothing in its operations.
/// Serves us to find out what overhead the benchmark alone brings.
struct NullCache<K, V> {
    _phantom_k: PhantomData<K>,
    _phantom_v: PhantomData<V>,
}

impl<K, V> NullCache<K, V> {
    fn get<'a>(&'a mut self, _key: &K) -> Option<&'a V> {
        None
    }

    fn insert(&mut self, _key: K, _value: V) {
        // empty
    }
}

fn null_bench(c: &mut Criterion) {
    prepare_data();
    let mut bench_group = c.benchmark_group("NULL");
    bench_group.sample_size(10);

    generic_bench!(bench_group, null, NullCache<u16, ()>, 0);
}


criterion_group!(policies, rr_bench, lru_bench, lfu_bench, clock_bench, clock_pro_bench, lirs_bench, qq_bench, qq_lfu_bench, arc_bench);
criterion_group!(null, null_bench);
criterion_main!(policies, null);


// From this point, the file is almost identical to the end of the `concurrent`
// benchmark. We use the same function to import the workload into a static
// variable, and use the same Transaction struct to represent it.
// (of course, that is inconvenient code repetition, but the alternatives are
// either moving the Transaction struct into `src`, or two separate Rust
// projects, one for implementation and one for benchmarking).

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
    #[allow(dead_code)]
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
