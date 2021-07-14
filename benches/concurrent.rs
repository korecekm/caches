use std::fs::File;
use std::io::{BufRead, BufReader};
use std::ptr;
use criterion::*;

// We will work with the workload described in
// "benches/access_logs/[WORKLOAD_FILENAME].txn"
// (more about this format can be found in the access_logs directory's README)
const WORKLOAD_FILENAME: &str = "Carabas";
// The whole access logs will be imported here by `prepare_data` in the form of
// `Transaction` structs.
static mut WORKLOAD: *const Vec<Transaction<u16>> = ptr::null();
// The max. total number of records cached at one time by the cache(s) that we
// benchmark
const CACHE_SIZE_TOTAL: usize = 3456;
// All concurrent strategies (single_thread_bench is a separate benchmark) will
// be measured one by one with these thread counts.
const THREAD_COUNTS: [usize; 4] = [2, 4, 8, 12];

// Before running the first iteration of a benchmark, the cache data structure
// is filled by iterating the log's transactions, to not start with an empty
// one and have non-uniform results.
macro_rules! fill_generic {
    ($cache:expr) => {
        // Iterate the workload and simulate the use of our cache.
        for txn in unsafe { (*WORKLOAD).iter() } {
            for key in txn.iter_keys() {
                // Hit accessed keys; insert the missing ones.
                if $cache.get(key).is_none() {
                    $cache.insert(*key, ());
                }
            }
        }
    };
}

// This takes care of search-only transactions in strategies where we have
// unique access to all the keys in question (all but PER-THREAD currently).
// Actually, this macro is also used for mutable transactions in the LOCK and
// ASSOCIATIVE measurements, as those strategies don't require special behavior
// towards record modifications.
macro_rules! perform_search_only_generic {
    ($cache:expr, $txn:expr) => {
        // We simulate search-only transactions by performing searches on all
        // the keys and adding those that are missing.
        for uid in $txn.iter_keys() {
            if $cache.get(uid).is_none() {
                $cache.insert(*uid, ());
            }
        }
    };
}

macro_rules! send_workload {
    ($query_queue:expr, $join_handles:expr) => {{
        let workload_size = unsafe {
            (*WORKLOAD).len()
        };
        let start = Instant::now();
        // Send all indexes to transactions in `WORKLOAD`
        for txn_idx in 0..workload_size {
            $query_queue.push(txn_idx as u32).unwrap();
        }
        // Stop the broadcast by sending u32::MAX for each worker thread.
        for _ in 0..$join_handles.len() {
            $query_queue.push(u32::MAX).unwrap();
        }

        // Join all threads
        for handle in $join_handles {
            handle.join().unwrap();
        }
        start.elapsed()
    }}
}

macro_rules! prepare_cache_struct {
    (lock $thread_count:expr, $struct_variable:expr) => {
        let cache = Mutex::new(Cache::new(CACHE_SIZE_TOTAL));
        fill_generic!(*cache.lock().unwrap());
        unsafe {
            $struct_variable = Box::into_raw(Box::new(cache));
        }
    };
    (assoc $thread_count:expr, $struct_variable:expr) => {
        let cache = CacheAssoc::new(CACHE_SIZE_TOTAL, $thread_count * 3);
        let mut unique_guard = cache.generate_unique_access_guard();
        fill_generic!(unique_guard);
        drop(unique_guard);
        unsafe {
            $struct_variable = Box::into_raw(Box::new(cache));
        }
    };
    (perthread $thread_count:expr, $struct_variable:expr) => {
        let mut caches_per_thread = Vec::with_capacity($thread_count);
        for _ in 0..$thread_count {
            let mut cache = Cache::new(CACHE_SIZE_TOTAL / $thread_count);
            fill_generic!(cache);
            caches_per_thread.push(cache);
        }
        unsafe {
            $struct_variable = Box::into_raw(Box::new(caches_per_thread));
        }
    };
    (txnal $thread_count:expr, $struct_variable:expr) => {
        let cache_txnal = CacheTxnal::new(CACHE_SIZE_TOTAL);
        let mut write_txn = cache_txnal.write();
        fill_generic!(write_txn);
        write_txn.commit();
        unsafe {
            $struct_variable = Box::into_raw(Box::new(cache_txnal));
        }
    }
}

macro_rules! generic_bench {
    ($criterion:expr, $bench_name:expr, $strategy_id:ident, $struct_variable:expr, $struct_type:ty, $iteration_function:expr) => {
        prepare_data();
        let mut group = $criterion.benchmark_group($bench_name);
        group.sample_size(10);

        for thread_count in THREAD_COUNTS.iter() {
            prepare_cache_struct!($strategy_id *thread_count, $struct_variable);

            group.bench_with_input(
                BenchmarkId::from_parameter(format!("{}/{}", WORKLOAD_FILENAME, thread_count)),
                thread_count,
                |b, thread_count| {
                    b.iter_custom(|iters| {
                        let mut duration = Duration::from_micros(0);
                        for _ in 0..iters {
                            duration += ($iteration_function)(*thread_count);
                        }
                        duration
                    })
                }
            );

            // Free the structure that holds our cache(s)
            unsafe {
                Box::from_raw($struct_variable as *mut $struct_type);
            }
        }
    };
}

// The LOCK strategy
mod lock {
    use super::{WORKLOAD, prepare_data, THREAD_COUNTS, WORKLOAD_FILENAME, CACHE_SIZE_TOTAL};
    use crossbeam::queue::ArrayQueue;
    use criterion::*;
    use std::sync::{Arc, Mutex};
    use std::time::{Duration, Instant};
    use std::ptr;
    use caches::lru::LRUCache as Cache;

    // All threads will be accessing this one cache.
    static mut CACHE_LOCK: *const Mutex<Cache<u16, ()>> = ptr::null();

    // This expands into what a worker thread does, using this strategy
    macro_rules! perform_lock {
        // The parameter is a reference (Arc) to the SPMC queue that distributes
        // WORKLOAD indexes to be processed.
        ($query_queue:expr) => {
            loop {
                if let Some(txn_idx) = $query_queue.pop() {
                    if txn_idx == u32::MAX {
                        // u32::MAX is a special value that signifies the end
                        // of the workload
                        break;
                    }
                    // Current transaction to process:
                    let txn = unsafe {
                        &(*WORKLOAD)[txn_idx as usize]
                    };
                    // Lock the cache to be able to work with it
                    let mut cache_guard = unsafe {
                        (*CACHE_LOCK).lock().unwrap()
                    };
                    perform_search_only_generic!(*cache_guard, txn);
                }
            }
        };
    }

    fn perform_measurement_iteration(thread_count: usize) -> Duration {
        // First, prepare the queue to send the workload through
        let workload_size = unsafe { (*WORKLOAD).len() };
        let query_queue = Arc::new(ArrayQueue::new(workload_size + thread_count));
        // Spawn the worker threads
        let mut join_handles = Vec::with_capacity(thread_count);
        for _ in 0..thread_count {
            let queue_ref = query_queue.clone();
            let join_handle = std::thread::spawn(move || {
                perform_lock!(queue_ref);
            });
            join_handles.push(join_handle);
        }

        send_workload!(query_queue, join_handles)
    }

    pub fn lock_bench(c: &mut Criterion) {
        generic_bench!(
            c,
            "LOCK",
            lock,
            CACHE_LOCK,
            Mutex<Cache<u16, ()>>,
            perform_measurement_iteration
        );
    }
}

// The ASSOCIATIVE strategy
mod assoc {
    use super::{WORKLOAD, prepare_data, THREAD_COUNTS, WORKLOAD_FILENAME, CACHE_SIZE_TOTAL};
    use std::time::{Duration, Instant};
    use criterion::*;
    use std::ptr;
    use std::sync::Arc;
    use crossbeam::queue::ArrayQueue;
    use caches::lru_associative::LRUAssociative as CacheAssoc;

    // All threads will be accessing this associative cache
    static mut CACHE_ASSOCIATIVE: *const CacheAssoc<u16, ()> = ptr::null();

    // This expands into what a worker thread does, using this strategy
    macro_rules! perform_assoc {
        // The parameter is a reference (Arc) to the SPMC queue that
        // distributes WORKLOAD indexes to be processed.
        ($query_queue:expr) => {
            loop {
                if let Some(txn_idx) = $query_queue.pop() {
                    if txn_idx == u32::MAX {
                        // u32::MAX is a special value that signifies the end
                        // of the workload
                        break;
                    }
                    // Current transaction to process
                    let txn = unsafe {
                        &(*WORKLOAD)[txn_idx as usize]
                    };
                    // Lock the cache "slots" necessary for this transaction
                    let mut cache_guard = unsafe {
                        (*CACHE_ASSOCIATIVE).generate_mut_guard(txn.get_key_vec())
                    };
                    perform_search_only_generic!(cache_guard, txn);
                }
            }
        };
    }

    fn perform_measurement_iteration(thread_count: usize) -> Duration {
        // First, prepare the queue to send the workload through
        let workload_size = unsafe { (*WORKLOAD).len() };
        let query_queue = Arc::new(ArrayQueue::new(workload_size + thread_count));
        // Spawn the worker threads
        let mut join_handles = Vec::with_capacity(thread_count);
        for _ in 0..thread_count {
            let queue_ref = query_queue.clone();
            let join_handle = std::thread::spawn(move || {
                perform_assoc!(queue_ref);
            });
            join_handles.push(join_handle);
        }

        send_workload!(query_queue, join_handles)
    }

    pub fn assoc_bench(c: &mut Criterion) {
        generic_bench!(
            c,
            "ASSOCIATIVE",
            assoc,
            CACHE_ASSOCIATIVE,
            CacheAssoc<u16, ()>,
            perform_measurement_iteration
        );
    }
}

// The PER-THREAD strategy
mod per_thread {
    use super::{WORKLOAD, prepare_data, THREAD_COUNTS, WORKLOAD_FILENAME, CACHE_SIZE_TOTAL, Transaction, SearchTxn, ModifyTxn};
    use std::time::{Duration, Instant};
    use crossbeam::queue::ArrayQueue;
    use criterion::*;
    use std::sync::{Arc, Mutex};
    use std::ptr;
    use caches::lru::LRUCache as Cache;
    use std::sync::mpsc::*;

    // To modify any records in memory, a thread needs to lock this mutex.
    static mut MODIFICATION_LOCK: *const Mutex<()> = ptr::null();
    // Each thread will be accessing its own cache in this vector
    static mut CACHES_PER_THREAD: *const Vec<Cache<u16, ()>> = ptr::null();

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

    /// Takes care of invalidating all the necessary records of a thread's
    /// cache.
    /// 'Returns' information about whether any records got invalidated.
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
        let mod_guard = unsafe { (*MODIFICATION_LOCK).lock().unwrap() };
        // We will store all the keys we modify into a Vec to be able to send
        // an invalidation request. We simply iterate it for potential
        // duplicates, quadratic time is no issue here as the Vec is expected
        // to be short.
        let mut inval_vec = Vec::new();
        for i in 0..txn.key_vec.len() {
            let uid = txn.key_vec[i];
            // Access the UID, potentially inserting it anew
            if cache.get(&uid).is_none() {
                cache.insert(uid, ());
            }
            if txn.mod_vec[i] {
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
            }
        }
        // Invoke the invalidation broadcast
        invalidate_send.send((thread_idx, inval_vec)).unwrap();
        // Just to be clear about only now dropping the modification guard
        drop(mod_guard);
    }

    // This expands into what a worker thread does, using this strategy
    macro_rules! perform_per_thread {
        // This macro needs to know the index (order during spawning) of its
        // thread, a reference (Arc) to the scheduler SPMC queue as all other
        // strategies and also the infrastructure of our invalidation
        // mechanism, that is, the send stream to our invalidation thread and
        // also the recv end of the invalidation stream leading from that
        // thread.
        ($thread_idx:expr, $query_queue:expr, $inval_send:expr, $inval_recv:expr) => {
            // Get access to the cache of this thread
            let cache = unsafe {
                &mut (*(CACHES_PER_THREAD as *mut Vec<Cache<u16, ()>>))[$thread_idx]
            };
            loop {
                if let Some(txn_idx) = $query_queue.pop() {
                    if txn_idx == u32::MAX {
                        // u32::MAX is a special value that signifies the end of
                        // the workload
                        break;
                    }
                    // Perform potential invalidations to stay up to date
                    per_thread_invalidate(cache, &$inval_recv);
                    // Current transaction to process
                    let txn = unsafe {
                        &(*WORKLOAD)[txn_idx as usize]
                    };
                    match txn {
                        Transaction::Search(st) => per_thread_read(cache, st, &$inval_recv),
                        Transaction::Modify(mt) => per_thread_mod($thread_idx, cache, mt, &$inval_send),
                    }
                }
            }
        };
    }

    fn perform_measurement_iteration(thread_count: usize) -> Duration {
        // First, prepare the queue to send the workload through
        let workload_size = unsafe { (*WORKLOAD).len() };
        let query_queue = Arc::new(ArrayQueue::new(workload_size + thread_count));
        // Also prepare the invalidation mechanism:
        // A "rendezvous" channel for record invalidation requests
        let (inval_send, inval_recv) = sync_channel(0);
        // Vector containing "send"s to specific threads
        let mut thread_sends = Vec::with_capacity(thread_count);

        // Spawn all the worker threads
        let mut join_handles = Vec::with_capacity(thread_count);
        for thread_idx in 0..thread_count {
            let queue_ref = query_queue.clone();
            let inval_send = inval_send.clone();
            let (thread_inval_send, thread_inval_recv) = channel();
            thread_sends.push(thread_inval_send);
            let join_handle = std::thread::spawn(move || {
                perform_per_thread!(thread_idx, queue_ref, inval_send, thread_inval_recv);
            });
            join_handles.push(join_handle);
        }
        drop(inval_send);

        // Spawn the dedicated invalidation broadcast thread.
        let invalidation_thread_handle = std::thread::spawn(move || {
            per_thread_invalidation_thread!(inval_recv, thread_sends);
        });
        let duration = send_workload!(query_queue, join_handles);
        // Now also join the dedicated broadcast thread.
        invalidation_thread_handle.join().unwrap();

        duration
    }

    pub fn per_thread_bench(c: &mut Criterion) {
        // Initiate the modification lock that will be used in all the
        // per-thread measurements
        unsafe {
            MODIFICATION_LOCK = Box::into_raw(Box::new(Mutex::new(())));
        }

        generic_bench!(
            c,
            "PER-THREAD",
            perthread,
            CACHES_PER_THREAD,
            Vec<Cache<u16, ()>>,
            perform_measurement_iteration
        );

        // Free the modification lock
        unsafe {
            Box::from_raw(MODIFICATION_LOCK as *mut Mutex<()>);
        }
    }
}

// The TRANSACTIONAL strategy
mod txnal {
    use super::{WORKLOAD, prepare_data, THREAD_COUNTS, WORKLOAD_FILENAME, CACHE_SIZE_TOTAL, Transaction};
    use std::time::{Duration, Instant};
    use criterion::*;
    use std::ptr;
    use caches::list::DLList;
    use std::sync::Arc;
    use crossbeam::queue::ArrayQueue;
    use caches::lru_transactional::LRUTransactional as CacheTxnal;

    // The threads will be working with snapshots to this transactional cache.
    static mut CACHE_TRANSACTIONAL: *const CacheTxnal<u16, ()> = ptr::null();

    // Macro that takes care of a transaction at `txn_idx` of our WORKLOAD,
    // using a write transaction.
    macro_rules! txnal_write {
        ($txn_idx:expr, $hit_list:expr) => {
            // Acquire write privilege to the cache
            let mut write = unsafe {
                (*CACHE_TRANSACTIONAL).write()
            };
            // Hit all records that couldn't have been hit with only the read
            // txn
            while let Some(key) = $hit_list.pop_back() {
                write.get(&key);
            }
            // Perform given transaction
            let txn = unsafe {
                &(*WORKLOAD)[$txn_idx as usize]
            };
            match txn {
                // We simulate search-only transactions by performing
                // searches on all the keys and adding those that are
                // missing.
                Transaction::Search(_) => perform_search_only_generic!(write, txn),
                Transaction::Modify(mt) => {
                    // The transactional approach requires modifications to be
                    // performed using the `reinsert` method.
                    // So here, we only ger references for search queries
                    // (adding
                    // the missing ones) and simulate modifications to records
                    // by 'reinserting' them.
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

    // This expands into what a worker thread does, using this strategy
    macro_rules! perform_txnal {
        ($query_queue:expr) => {
            // Read-only snapshots of the cache don't allow us to update the
            // cache's internal state, so we keep a record of hit keys, that we
            // access once we get the write privilege
            let mut hit_list = DLList::new();
            'iter_txns: loop {
                if let Some(txn_idx) = $query_queue.pop() {
                    if txn_idx == u32::MAX {
                        // u32::MAX is a special value that signifies the end 
                        // of the workload
                        break;
                    }
                    // Too many cache hits went unmarked globally, we take a
                    // write transaction now to perform the cache hits.
                    if hit_list.size > 400 {
                        txnal_write!(txn_idx, &mut hit_list);
                        continue;
                    }
                    // Current transaction to process
                    let txn = unsafe {
                        &(*WORKLOAD)[txn_idx as usize]
                    };
                    if txn.does_modify() {
                        txnal_write!(txn_idx, &mut hit_list);
                    } else {
                        // Transaction only performs reads.
                        // Get a read-only snapshot of the cache
                        let read = unsafe {
                            (*CACHE_TRANSACTIONAL).read()
                        };
                        for key in txn.iter_keys() {
                            if read.get(key).is_none() {
                                // Key not present in the cache's read
                                // snapshot. We need write privilege to the
                                // cache.
                                txnal_write!(txn_idx, &mut hit_list);
                                continue 'iter_txns;
                            }
                        }
                        // The transaction was successful, so we record all the
                        // cache hits (to mark them globally once we get the
                        // write privilege)
                        for key in txn.iter_keys() {
                            hit_list.push_front(*key);
                        }
                    }
                }
            }
        };
    }

    fn perform_measurement_iteration(thread_count: usize) -> Duration {
        // First, prepare the queue to send the workload through
        let workload_size = unsafe { (*WORKLOAD).len() };
        let query_queue = Arc::new(ArrayQueue::new(workload_size + thread_count));
        // Spawn the worker threads
        let mut join_handles = Vec::with_capacity(thread_count);
        for _ in 0..thread_count {
            let queue_ref = query_queue.clone();
            let join_handle = std::thread::spawn(move || {
                perform_txnal!(queue_ref);
            });
            join_handles.push(join_handle);
        }

        send_workload!(query_queue, join_handles)
    }

    pub fn txnal_bench(c: &mut Criterion) {
        generic_bench!(
            c,
            "TRANSACTIONAL",
            txnal,
            CACHE_TRANSACTIONAL,
            CacheTxnal<u16, ()>,
            perform_measurement_iteration
        );
    }
}


criterion_group!(
    concurrent,
    lock::lock_bench,
    assoc::assoc_bench,
    per_thread::per_thread_bench,
    txnal::txnal_bench
);
criterion_main!(concurrent);


// From this point, the file is almost identical to the end of the
// `single_thread` benchmark. We use the same function to import the workload
// into a static variable, and use the same Transaction struct to represent it.
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
