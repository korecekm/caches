// This bench function iterates through keys in our access logs and counts how many cache misses
// occur with the different cache replacement policies of different cache capacities.
// 
// The access logs are imported from our custom `.in` files inside the benches/access_logs dir.,
// more about the file format is in the directory's README.
// 
// The results of these measurements are written into corresponding `hit_rate-[ACCESS_LOG].result`
// files into the benches/results directory. The directory, again, contains a README with a
// description of this custom format (only the "2D multi" type of file concerns us here).
// 
// Additionally to counting the misses for the cache replacement policies, we also count the
// "Belady" optima for each kind of measurement.
// 
// The unique number of keys accessed in the measured access log is always decremented from the
// miss count, as the first access to a key causes a cache miss inevitably.
// 
// The parameters to the parameterized cache replacement policies (2Q, 2Q-LFU and LIRS) for this
// measurement are chosen based on measurement by the `cache_parameter_comparison` bench file.
// 
// Because some of the caches use const generics, to only determine the cache capacities that we
// want to measure for at one place in the code (in the main function), we need to use macros (and
// variadic parameters).

use caches::arc::ARCache as ARC;
use caches::clock::CLOCKCache as CLOCK;
use caches::clock_pro::CLOCKProCache as CLOCKPro;
use caches::lfu::LFUCache as LFU;
use caches::lirs::LIRSCache as LIRS;
use caches::lru::LRUCache as LRU;
use caches::qq::QCache as QQ;
use caches::qq_lfu::QQLFUCache as QQLFU;
use caches::rr::RRCache as RR;
use std::collections::HashMap;
use std::fs::File;
use std::io::Write;
use std::io::{BufRead, BufReader};
use std::ptr;

// static vector that holds the list of accessed keys (UIDs) with which we
// currently measure
static mut ACCESSES: *const Vec<u16> = ptr::null();
// The total number of unique keys accessed within the current access log.
static mut UNIQUE_KEY_COUNT: usize = 0;

// Expands into the measurement itself, i.e. receives a cache data structure
// and iterates through the access log. On a cache miss, it increments a
// recorded miss count and inserts the record into the cache anew
macro_rules! iterate_accesses {
    ($cache:expr) => {{
        let mut miss_count = 0;
        for key in unsafe { (*ACCESSES).iter() } {
            if $cache.get(&key).is_none() {
                // cache miss
                miss_count += 1;
                $cache.insert(*key, ());
            }
        }
        // Whenever a key is accessed for the very first time, it's necessarily
        // a miss. Since our goal is to see, how well the caches adapt to the
        // access pattern, we subtract the number of unique keys.
        unsafe { miss_count - UNIQUE_KEY_COUNT }
    }};
}

// As all our cache data structures share their interface, this can be used to
// expand into any of the measurements for unparameterized caches.
// It counts the misses for a cache type and writes the results into the
// current `.result` file
macro_rules! perform_generic {
    // Params:
    // * `writefile` is the file handle to the current .result file
    // * cache_type: the type of the measured cache (which must be
    //   unparameterized, i.e. only needs the capacity for its instantiation)
    // * capacities: a variadic set of parameters that determine the cache
    //   capacities for which we measure
    ($writefile:expr, $cache_type:ty, $($capacity:expr),*) => {
        $(
            // Create the cache.
            let mut cache = <$cache_type>::new($capacity);
            // Write the measured number of misses into the .result file
            write!($writefile, " {}", iterate_accesses!(cache)).unwrap();
        )*
        // End the record with a newline
        writeln!($writefile, "").unwrap();
    };
}

// The parameterized 2Q needs a separate macro. The structure of the execution,
// however, is the same as `perform_generic`
macro_rules! perform_2Q {
    ($writefile:expr, $($capacity:expr),*) => {
        $(
            // The capacities of Q1, Q2 and the main queue are set to 10, the
            // sixth of the capacity, and the rest, respectively.
            let mut cache = QQ::<u16, ()>::new(10, { $capacity / 6 }, { $capacity - ($capacity / 6) - 10 });
            write!($writefile, " {}", iterate_accesses!(cache)).unwrap();
        )*
        // End the record with a newline
        writeln!($writefile, "").unwrap();
    };
}

// The parameterized 2Q-LFU needs a separate macro. The structure of the
// execution, however, is the same as `perform_generic`
macro_rules! perform_2Q_LFU {
    ($writefile:expr, $($capacity:expr),*) => {
        $(
            // The capacities of both Q1 and Q2 are set to the fifth of the
            // total capacity
            let mut cache = QQLFU::<u16, (), { $capacity - ($capacity / 5 * 2)}>::new($capacity / 5, $capacity / 5);
            write!($writefile, " {}", iterate_accesses!(cache)).unwrap();
        )*
        // End the record with a newline
        writeln!($writefile, "").unwrap();
    };
}

// The LFU needs a separate macro, because it uses const generics for its
// capacity. The structure of the execution, however, is the same as
// `perform_generic`
macro_rules! perform_lfu {
    ($writefile:expr, $($capacity:expr),*) => {
        $(
            let mut cache = LFU::<u16, (), $capacity>::new();
            write!($writefile, " {}", iterate_accesses!(cache)).unwrap();
        )*
        // End the record with a newline
        writeln!($writefile, "").unwrap();
    };
}

// The CLOCK needs a separate macro, because it uses const generics for its
// capacity. The structure of the execution, however, is the same as
// `perform_generic`
macro_rules! perform_clock {
    ($writefile:expr, $($capacity:expr),*) => {
        $(
            let mut cache = CLOCK::<u16, (), $capacity>::new();
            write!($writefile, " {}", iterate_accesses!(cache)).unwrap();
        )*
        // End the record with a newline
        writeln!($writefile, "").unwrap();
    };
}

// The parameterized LIRS needs a separate macro. The structure of the
// execution, however, is the same as `perform_generic`
macro_rules! perform_lirs {
    ($writefile:expr, $($capacity:expr),*) => {
        $(
            // The HIR capacity is set to 30 for all measurements
            let mut cache = LIRS::<u16, ()>::new({ $capacity - 30 }, 30);
            write!($writefile, " {}", iterate_accesses!(cache)).unwrap();
        )*
        // End the record with a newline
        writeln!($writefile, "").unwrap();
    };
}

// This macro performs the measurements themselves. It receives the filename
// from which to take the workload, the index of the log (we name our logs
// "Log 1" and "Log 2") and all the cache capacities for which we wish to
// measure.
// It exports the results into the `benches/results` directory in out custom
// .result format, which is descriped in the directory's README.
macro_rules! perform_measurement {
    ($filename:expr, $log_idx:expr, $($capacity:expr),*) => {
        // Import the access log into our static ACCESSES variable, and also
        // prepare the File handle for the `.result` file we write into.
        let readpath = format!("benches/access_logs/{}.in", $filename);
        let writepath = format!("benches/results/hit_rate-{}.result", $filename);
        prepare_data(&readpath);
        let mut writefile = File::create(writepath).unwrap();

        // Write the first several, generic, lines of the result file
        writeln!(&mut writefile, "2D multi").unwrap();
        writeln!(&mut writefile, "Hit rates for Log {}", $log_idx).unwrap();
        writeln!(&mut writefile, "{}", unsafe { UNIQUE_KEY_COUNT }).unwrap();
        writeln!(&mut writefile, "{}", unsafe { (*ACCESSES).len() - UNIQUE_KEY_COUNT }).unwrap();
        $(
            write!(&mut writefile, " {}", $capacity).unwrap();
        )*
        writeln!(&mut writefile, "").unwrap();

        // Now, write the results for each of the cache replacement policies.
        // Parameterized policies, or those that use const generics need to be
        // measured using their ad hoc macros, but others may be done using
        // `perform_geneirc`
        writeln!(&mut writefile, "LRU").unwrap();
        perform_generic!(&mut writefile, LRU<u16, ()>, $($capacity),*);
        writeln!(&mut writefile, "2Q").unwrap();
        perform_2Q!(&mut writefile, $($capacity),*);
        writeln!(&mut writefile, "2Q-LFU").unwrap();
        perform_2Q_LFU!(&mut writefile, $($capacity),*);
        writeln!(&mut writefile, "ARC").unwrap();
        perform_generic!(&mut writefile, ARC<u16, ()>, $($capacity),*);
        writeln!(&mut writefile, "LFU").unwrap();
        perform_lfu!(&mut writefile, $($capacity),*);
        writeln!(&mut writefile, "LIRS").unwrap();
        perform_lirs!(&mut writefile, $($capacity),*);
        writeln!(&mut writefile, "CLOCK").unwrap();
        perform_clock!(&mut writefile, $($capacity),*);
        writeln!(&mut writefile, "CLOCK-Pro").unwrap();
        perform_generic!(&mut writefile, CLOCKPro<u16, ()>, $($capacity),*);
        writeln!(&mut writefile, "Random replacement").unwrap();
        perform_generic!(&mut writefile, RR<u16, ()>, $($capacity),*);

        // Also generate the optimal values
        unsafe {
            prepare_opt_metadata();
        }
        writeln!(&mut writefile, "OPT").unwrap();
        $(
            write!(&mut writefile, " {}", count_opt_misses($capacity)).unwrap();
        )*
        writeln!(&mut writefile, "").unwrap();

        // deallocate the data for the current input file, that's now in memory
        unsafe {
            Box::from_raw(ACCESSES as *mut Vec<u16>);
            Box::from_raw(OPT_METADATA as *mut Vec<Vec<u16>>);
        }
    };
}

fn main() {
    // Perform the measurement for "Log 1" with the selected cache capacities
    perform_measurement!("output", 1, 80, 150, 250, 400, 600, 800, 1006);
    // Perform the measurement for "Log 2" with the selected cache capacities
    perform_measurement!(
        "Carabas", 2, 80, 141, 232, 353, 494, 650, 850, 1107, 1768, 3537, 5660, 7075
    );
}

/// This function is responsible for importing the `.in` access log file at the
/// received path into our `ACCESSES` local variable.
fn prepare_data(filepath: &str) {
    // Init the global variable as an empty vector (of u16)
    unsafe {
        ACCESSES = Box::into_raw(Box::new(Vec::new()));
    }
    // Read the lines of the `.in` file
    let file = File::open(filepath).unwrap();
    let mut lines = BufReader::new(file).lines().enumerate();

    // The first line contains the number of unique keys in the access sample.
    unsafe {
        UNIQUE_KEY_COUNT = lines.next().unwrap().1.unwrap().parse().unwrap();
    }
    // The rest just the keys (IDs) of records that get accessed
    for (_, line) in lines {
        let key = line.unwrap().parse().unwrap();
        unsafe {
            (*(ACCESSES as *mut Vec<u16>)).push(key);
        }
    }
}

// Counting the optima:
// As proven by Laszlo Belady, the theoretical optimal way of evicting records
// (once necessary) is by each time evicting the one that will be next accessed
// the furthest in the future.
// To be able to count such optima for the different cache capacities we
// measure, we first prepare our `OPT_METADATA` 2D vector. The first dimension
// will be all the unique keys. For each key, we will hold a vector of the size
// of the access log, that will say how many other unique keys will be accessed
// before this one.
// Once that is prepared, we can just simulate the optimal cache by simulating
// it as a Vec of keys, and each time an eviction is needed, replacing the key
// that won't be used the longest with the newly inserted one.
// (the keys in our access logs are always numbers between 0 and
// UNIQUE_KEY_COUNT-1, which makes this process easier)

static mut OPT_METADATA: *const Vec<Vec<u16>> = ptr::null();

// Prepare the OPT_METADATA 2D vector, as described above.
unsafe fn prepare_opt_metadata() {
    // First, initiate the first dimension, which are the unique keys in our
    // access log
    OPT_METADATA = Box::into_raw(Box::new(Vec::with_capacity(UNIQUE_KEY_COUNT)));
    let opt_metadata = &mut *(OPT_METADATA as *mut Vec<Vec<u16>>);
    let data_length = (*ACCESSES).len();
    // Prepare the vector in the second dimension
    for i in 0..UNIQUE_KEY_COUNT {
        opt_metadata.push(Vec::with_capacity(data_length));
        opt_metadata[i].resize(data_length, data_length as u16 + 1);
    }

    // Prepare the vector for one exact index in the access logs
    for i in 0..data_length {
        prepare_opt_single(opt_metadata, i);
    }
}

/// Prepare OPT_METADATA for one index in the access log, meaning that we see
/// what key is accessed at this idx and record the count of other unique keys
/// accessed until this point, from the previous access of this element
fn prepare_opt_single(opt_metadata: &mut Vec<Vec<u16>>, idx: usize) {
    // Prepare a map of keys that will let us see which other keys we have
    // already encountered
    let mut map = HashMap::with_capacity(unsafe { UNIQUE_KEY_COUNT });
    // The key at idx
    let original_elem = unsafe { (*ACCESSES)[idx] };
    // The length of our access log
    let data_length = unsafe { (*ACCESSES).len() };

    // The number of distinct keys met since the original idx
    let mut key_count = 0;
    // We will iterate backwards from the original index and mark the data for
    // the original key (`original_elem`)
    let mut i = idx;
    loop {
        // decrement idx, potentially overflowing to the end of the list again
        i = (data_length + i - 1) % data_length;
        // update the metadata based on the current met key count
        opt_metadata[original_elem as usize][i] = key_count;
        // See if we have already encountered the key at current index
        let elem = unsafe { (*ACCESSES)[i] };
        if elem == original_elem {
            return;
        } else if map.get(&elem).is_none() {
            // We haven't encountered it yet, the number of unique keys met
            // increases
            key_count += 1;
            map.insert(elem, ());
        }
    }
}

/// Based on OPT_METADATA, count the Belady optimum for given cache capacity
fn count_opt_misses(cache_capacity: usize) -> usize {
    // currently cached keys:
    let mut cached_vec = Vec::with_capacity(cache_capacity);
    // their hash map, to conveniently see which are present in the cache
    let mut cached_map = HashMap::with_capacity(cache_capacity);
    let mut miss_count = 0;

    // Iterate through the access log:
    let mut i = 0;
    for elem in unsafe { (*ACCESSES).iter() } {
        if cached_map.contains_key(elem) {
            // cache hit
            i += 1;
            continue;
        }
        // cache miss:
        miss_count += 1;
        // If capacity isn't reached yet, just insert the new element,
        // otherwise replace the right key.
        if cached_vec.len() < cache_capacity {
            cached_vec.push(*elem);
        } else {
            let evict_idx = opt_evict(&cached_vec, i);
            cached_map.remove(&cached_vec[evict_idx]);
            cached_vec[evict_idx] = *elem;
        }
        cached_map.insert(*elem, ());
        i += 1;
    }

    // The number of unique keys gets subtracted, since the first occurence of
    // a key is necessarily a miss.
    miss_count - unsafe { UNIQUE_KEY_COUNT }
}

/// Receives a reference to a vector of currently cached keys and the index of
/// the current query, and returns the index, in the vector, that contains the
/// key to evict, optimally
fn opt_evict(cached_vec: &Vec<u16>, query_idx: usize) -> usize {
    let opt_metadata = unsafe { &*OPT_METADATA };
    // Iterate through cached keys and see which key will only be used next
    // after the "maximal gap"
    let mut max_gap = 0;
    let mut max_idx = 0;
    for i in 0..cached_vec.len() {
        let key = cached_vec[i];
        let gap = opt_metadata[key as usize][query_idx];
        if gap > max_gap {
            // This "gap" is the maximal yet seen
            max_gap = gap;
            max_idx = i;
        }
    }
    max_idx
}
