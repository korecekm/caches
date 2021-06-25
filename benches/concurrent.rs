extern crate multiqueue;
use caches::clock_pro::CLOCKProCache as Cache;
use caches::list::DLList;
use caches::clock_pro_associative::CLOCKProAssociative as CacheAssoc;
use caches::clock_pro_transactional::CLOCKProTransactional as CacheTxnal;
use std::fs::File;
use std::io::{BufRead, BufReader};
use std::ptr;
use criterion::*;
use std::sync::Mutex;
use std::time::{Duration, Instant};

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

const WORKLOAD_FILENAME: &str = "Carabas";
static mut WORKLOAD: *const Vec<Transaction<u16>> = ptr::null();
const CACHE_SIZE_TOTAL: usize = 4224;
const THREAD_COUNTS: [usize; 1] = [2];

static mut CACHE_LOCK: *const Mutex<Cache<u16, ()>> = ptr::null();
static mut CACHE_ASSOCIATIVE: *const CacheAssoc<u16, ()> = ptr::null();
static mut CACHE_TRANSACTIONAL: *const CacheTxnal<u16, ()> = ptr::null();

// A macro to occupy any cache with a proper general get and insert function
// with the keys in our workload.
// We use this to initiate the caches, so that the benchmarks run on caches
// that already have a working cached set.
macro_rules! fill_generic {
    ($cache:expr) => {
        for txn in unsafe { (*WORKLOAD).iter() } {
            let key_vec = match txn {
                Transaction::Search(st) => &st.key_vec,
                Transaction::Modify(mt) => &mt.key_vec,
            };
            for key in key_vec.iter() {
                if $cache.get(key).is_none() {
                    $cache.insert(*key, ());
                }
            }
        }
    };
}

macro_rules! perform_lock {
    ($query_stream:expr) => {
        for txn_idx in $query_stream {
            let mut cache_guard = unsafe {
                (*CACHE_LOCK).lock().unwrap()
            };
            // Performance-wise, the CLOCK-Pro acts the same for both `get` and
            // `get_mut`. So we may just use get at all times (the whole cache
            for uid in unsafe { (*WORKLOAD)[txn_idx as usize].iter_keys() } {
                if (*cache_guard).get(uid).is_none() {
                    (*cache_guard).insert(*uid, ());
                }
            }
        }
    };
}

macro_rules! perform_assoc {
    ($query_stream:expr) => {
        for txn_idx in $query_stream {
            // Performance-wise, the CLOCK-Pro acts the same for both `get` and
            // `get_mut`. So we may just use get at all times (the necessary
            // cache slots are locked, so a simple `get` is a valid mutation
            // simulation.
            let key_vec = match unsafe { &(*WORKLOAD)[txn_idx as usize] } {
                Transaction::Search(st) => &st.key_vec,
                Transaction::Modify(mt) => &mt.key_vec,
            };
            let mut cache_guard = unsafe {
                (*CACHE_ASSOCIATIVE).generate_mut_guard(key_vec)
            };
            for uid in key_vec.iter() {
                if cache_guard.get(uid).is_none() {
                    cache_guard.insert(*uid, ());
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
            Transaction::Search(st) => {
                for uid in st.key_vec.iter() {
                    if write.get(uid).is_none() {
                        write.insert(*uid, ());
                    }
                }
            }
            Transaction::Modify(mt) => {
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
    ($query_stream:expr) => {
        // When only using a read txn, 
        let mut hit_list = DLList::new();
        for txn_idx in $query_stream {
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
                        break;
                    }
                }
                // The transaction was successful, so we record all the cache
                // hits (to mark them globally once we get the write privilege)
                for uid in txn.iter_keys() {
                    hit_list.push_front(*uid);
                }
            }
        }
    };
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
            BenchmarkId::from_parameter(thread_count),
            thread_count,
            |b, thread_count| {
                b.iter_custom(|iters| {
                    let mut duration = Duration::from_micros(0);
                    for _ in 0..iters {
                        // First, prepare the broadcast queue to send the
                        // workload through
                        let workload_size = unsafe { (*WORKLOAD).len() };
                        let (send, recv) = multiqueue::broadcast_queue(workload_size as u64);
                        let consumer_stream = recv.add_stream();
                        let mut handles = Vec::new();
                        for _ in 0..*thread_count {
                            let stream = consumer_stream.clone();
                            let join_handle = std::thread::spawn(move || {
                                perform_lock!(stream);
                            });
                            handles.push(join_handle);
                        }
                        recv.unsubscribe();

                        // We only start measuring the time once we send requests
                        let start = Instant::now();
                        for txn_idx in 0..workload_size {
                            send.try_send(txn_idx as u16).unwrap();
                        }
                        // Stop the broadcast
                        drop(send);

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
        let cache = CacheAssoc::new(CACHE_SIZE_TOTAL, thread_count * 4);
        let mut unique_guard = cache.generate_unique_access_guard();
        fill_generic!(unique_guard);
        drop(unique_guard);
        unsafe {
            CACHE_ASSOCIATIVE = Box::into_raw(Box::new(cache));
        }
        // The bench function itself:
        group.bench_with_input(
            BenchmarkId::from_parameter(thread_count),
            thread_count,
            |b, thread_count| {
                b.iter_custom(|iters| {
                    let mut duration = Duration::from_micros(0);
                    for _ in 0..iters {
                        // First, prepare the broadcast queue to send the workload through
                        let workload_size = unsafe { (*WORKLOAD).len() };
                        let (send, recv) = multiqueue::broadcast_queue(workload_size as u64);
                        let consumer_stream = recv.add_stream();
                        let mut handles = Vec::new();
                        for _ in 0..*thread_count {
                            let stream = consumer_stream.clone();
                            let join_handle = std::thread::spawn(move || {
                                perform_assoc!(stream);
                            });
                            handles.push(join_handle);
                        }
                        recv.unsubscribe();

                        // We only start measuring the time once we send requests
                        let start = Instant::now();
                        for txn_idx in 0..workload_size {
                            send.try_send(txn_idx as u16).unwrap();
                        }
                        // Stop the broadcast
                        drop(send);

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

pub fn transactional_bench(c: &mut Criterion) {
    // Prepare the workload into our WORKLOAD Vec
    prepare_data();
    // Prepare the benchmark group
    let mut group = c.benchmark_group("TRANSACTIONAL");
    group.sample_size(10);

    // Prepare the cache or the threads to access.
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
            BenchmarkId::from_parameter(thread_count),
            thread_count,
            |b, thread_count| {
                b.iter_custom(|iters| {
                    let mut duration = Duration::from_micros(0);
                    for _ in 0..iters {
                        // First, prepare the broadcast queue to send the
                        // workload through
                        let workload_size = unsafe { (*WORKLOAD).len() };
                        let (send, recv) = multiqueue::broadcast_queue(workload_size as u64);
                        let consumer_stream = recv.add_stream();
                        let mut handles = Vec::new();
                        for _ in 0..*thread_count {
                            let stream = consumer_stream.clone();
                            let join_handle = std::thread::spawn(move || {
                                perform_txnal!(stream);
                            });
                            handles.push(join_handle);
                        }
                        recv.unsubscribe();

                        // We only start measuring the time once we send requests
                        let start = Instant::now();
                        for txn_idx in 0..workload_size {
                            send.try_send(txn_idx as u16).unwrap();
                        }
                        // Stop the broadcast
                        drop(send);

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


criterion_group!(concurrent, lock_bench, associative_bench);
criterion_main!(concurrent);


struct SearchTxn<K> {
    key_vec: Vec<K>,
}

struct ModifyTxn<K> {
    key_vec: Vec<K>,
    mod_vec: Vec<bool>,
}

enum Transaction<K> {
    Search(SearchTxn<K>),
    Modify(ModifyTxn<K>),
}

impl<K> Transaction<K> {
    fn does_modify(&self) -> bool {
        match self {
            Self::Search(_) => false,
            Self::Modify(_) => true,
        }
    }

    fn iter_keys(&self) -> std::slice::Iter<'_, K> {
        match self {
            Self::Search(st) => st.key_vec.iter(),
            Self::Modify(mt) => mt.key_vec.iter(),
        }
    }
}

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
