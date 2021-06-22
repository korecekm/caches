use rand::{thread_rng, Rng};
use std::collections::HashMap;
use std::ptr;
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
use std::io::Write;

static mut ACCESSES: *const Vec<u16> = ptr::null();
static mut UNIQUE_KEY_COUNT: usize = 0;

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
        unsafe {
            miss_count - UNIQUE_KEY_COUNT
        }
    }}
}

macro_rules! perform_generic {
    ($writefile:expr, $cache_type:ty, $($capacity:expr),*) => {
        $(
            let mut cache = <$cache_type>::new($capacity);
            write!($writefile, " {}", iterate_accesses!(cache)).unwrap();
        )*
        writeln!($writefile, "").unwrap();
    };
}

macro_rules! perform_2Q {
    ($writefile:expr, $($capacity:expr),*) => {
        $(
            let mut cache = QQ::<u16, ()>::new(10, { $capacity / 6 }, { $capacity - ($capacity / 6) - 10 });
            write!($writefile, " {}", iterate_accesses!(cache)).unwrap();
        )*
        writeln!($writefile, "").unwrap();
    };
}

macro_rules! perform_2Q_LFU {
    ($writefile:expr, $($capacity:expr),*) => {
        $(
            let mut cache = QQLFU::<u16, (), { $capacity - ($capacity / 5 * 2)}>::new($capacity / 5, $capacity / 5);
            write!($writefile, " {}", iterate_accesses!(cache)).unwrap();
        )*
        writeln!($writefile, "").unwrap();
    };
}

macro_rules! perform_lfu {
    ($writefile:expr, $($capacity:expr),*) => {
        $(
            let mut cache = LFU::<u16, (), $capacity>::new();
            write!($writefile, " {}", iterate_accesses!(cache)).unwrap();
        )*
        writeln!($writefile, "").unwrap();
    };
}

macro_rules! perform_clock {
    ($writefile:expr, $($capacity:expr),*) => {
        $(
            let mut cache = CLOCK::<u16, (), $capacity>::new();
            write!($writefile, " {}", iterate_accesses!(cache)).unwrap();
        )*
        writeln!($writefile, "").unwrap();
    };
}

macro_rules! perform_lirs {
    ($writefile:expr, $($capacity:expr),*) => {
        $(
            let mut cache = LIRS::<u16, ()>::new({ $capacity - 30 }, 30);
            write!($writefile, " {}", iterate_accesses!(cache)).unwrap();
        )*
        writeln!($writefile, "").unwrap();
    };
}

macro_rules! perform_measurement {
    ($filename:expr, $($capacity:expr),*) => {
        let readpath = format!("benches/access_logs/{}.in", $filename);
        let writepath = format!("benches/results/hit_rate-{}.result", $filename);
        prepare_data(&readpath);
        let mut writefile = File::create(writepath).unwrap();
        writeln!(&mut writefile, "2D multi").unwrap();
        writeln!(&mut writefile, "Hit rates for Log 1").unwrap();

        writeln!(&mut writefile, "{}", unsafe { UNIQUE_KEY_COUNT }).unwrap();
        writeln!(&mut writefile, "{}", unsafe { (*ACCESSES).len() - UNIQUE_KEY_COUNT }).unwrap();
        $(
            write!(&mut writefile, " {}", $capacity).unwrap();
        )*
        writeln!(&mut writefile, "").unwrap();

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
    perform_measurement!("output", 80, 150, 250, 400, 600, 800, 1006);
    perform_measurement!("Carabas", 80, 141, 232, 353, 494, 650, 850, 1107, 1768, 3537, 5660, 7075);
}

fn prepare_data(filepath: &str) {
    unsafe {
        ACCESSES = Box::into_raw(Box::new(Vec::new()));
    }
    let file = File::open(filepath).unwrap();
    let mut lines = BufReader::new(file).lines().enumerate();
    // The first line contains the number of unique keys in the access sample.
    unsafe {
        UNIQUE_KEY_COUNT = lines.next().unwrap().1.unwrap().parse().unwrap();
    }
    for (_, line) in lines {
        let key = line.unwrap().parse().unwrap();
        unsafe {
            (*(ACCESSES as *mut Vec<u16>)).push(key);
        }
    }
}

// Counting the optimum:
static mut OPT_METADATA: *const Vec<Vec<u16>> = ptr::null();

unsafe fn prepare_opt_metadata() {
    OPT_METADATA = Box::into_raw(Box::new(Vec::with_capacity(UNIQUE_KEY_COUNT)));
    let opt_metadata = &mut *(OPT_METADATA as *mut Vec<Vec<u16>>);
    let data_length = (*ACCESSES).len();
    for i in 0..UNIQUE_KEY_COUNT {
        opt_metadata.push(Vec::with_capacity(data_length));
        opt_metadata[i].resize(data_length, data_length as u16 + 1);
    }
        
    for i in 0..data_length {
        prepare_opt_single(opt_metadata, i);
    }
}

fn prepare_opt_single(opt_metadata: &mut Vec<Vec<u16>>, idx: usize) {
    let mut map = HashMap::with_capacity(unsafe {
        UNIQUE_KEY_COUNT
    });
    let original_elem = unsafe {
        (*ACCESSES)[idx]
    };
    let data_length = unsafe {
        (*ACCESSES).len()
    };

    // The number of distinct keys met since the original idx
    let mut key_count = 0;
    let mut i = idx;
    loop {
        // decrement idx, potentially overflowing to the end of the list again
        i = (data_length + i - 1) % data_length;
        opt_metadata[original_elem as usize][i] = key_count;
        let elem = unsafe {
            (*ACCESSES)[i]
        };
        if elem == original_elem {
            return;
        } else if map.get(&elem).is_none() {
            key_count += 1;
            map.insert(elem, ());
        }
    }
}

fn count_opt_misses(cache_capacity: usize) -> usize {
    // currently cached keys:
    let mut cached_vec = Vec::with_capacity(cache_capacity);
    let mut cached_map = HashMap::with_capacity(cache_capacity);
    let mut miss_count = 0;

    let mut i = 0;
    for elem in unsafe { (*ACCESSES).iter() } {
        if cached_map.contains_key(elem) {
            i += 1;
            continue;
        }
        // cache miss:
        miss_count += 1;
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

fn opt_evict(cached_vec: &Vec<u16>, query_idx: usize) -> usize {
    let opt_metadata = unsafe {
        &*OPT_METADATA
    };
    let mut max_gap = 0;
    let mut max_idx = 0;
    for i in 0..cached_vec.len() {
        let key = cached_vec[i];
        let gap = opt_metadata[key as usize][query_idx];
        if gap > max_gap {
            max_gap = gap;
            max_idx = i;
        }
    }
    max_idx
}
