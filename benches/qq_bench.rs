// This is a sequential benchmark aimed to see which parameters are best for
// the 2Q cache, or rather the classical 2Q and the one with an LFU instead of
// an LRU as the last 'queue'

use caches::qq::QCache as QQ;
use caches::qq_lfu::QQLFUCache as QQLFU;
use criterion::*;
use rand::{thread_rng, Rng};
use std::ptr;
use std::thread;
use std::time::{Duration, Instant};

// How large will the generated data Vec be in total
const DATA_LENGTH: usize = 2000;
// How big a segment we iterate through on each benchmark iteration
const SEGMENT_SIZE: usize = 400;
// how many 'streams' of our real-life 57-element data access sample will
// participate for our generated data
const STREAM_COUNT: usize = 12;
// The total number of elements a cache may contain in total
const MEM_SIZE: usize = 52;
// How long a thread sleeps on cache miss
const MISS_WAIT: Duration = Duration::from_millis(10);
// The benchmarked parameters.
// The tuples mean a pair of (queue 1 capacity, queue 2 capacity)
//const PARAMS: [(usize, usize); 6] = [(2, 4), (5, 5), (2, 8), (7, 3), (7, 19), (13, 13)];
const PARAMS: [(usize, usize); 3] = [(2, 4), (5, 5), (7, 19)];

// The generated keys that we iterate through.
static mut GENERATED_DATA: *const Vec<u64> = ptr::null();

macro_rules! perform_cache_iteration {
    ($cache:expr, $start_idx:expr) => {
        for i in 0..SEGMENT_SIZE {
            let key = unsafe { (*GENERATED_DATA)[$start_idx + i] };

            if $cache.get(&key).is_none() {
                // cache miss:
                // simulate main storage access
                thread::sleep(MISS_WAIT);

                // missing record 'is retrieved from storage', insert it into the cache
                $cache.insert(key, ());
            }
        }
    };
}

macro_rules! bench_cache {
    ($cache:expr, $group:expr, $id:expr) => {
        $group.bench_with_input(
            BenchmarkId::from_parameter($id),
            &0,
            |b, _| {
                b.iter_custom(|iters| {
                    let mut data_start_idx = 0;
                    // Run once to fill the cache
                    perform_cache_iteration!($cache, data_start_idx);

                    // Now 'iters' times, measuring the time
                    let start = Instant::now();
                    for _ in 0..iters {
                        data_start_idx = (data_start_idx + SEGMENT_SIZE) % DATA_LENGTH;
                        perform_cache_iteration!($cache, data_start_idx);
                    }
                    start.elapsed()
                })
            }
        );
    };
}

pub fn qq_standard(c: &mut Criterion) {
    prepare_data();

    let mut group = c.benchmark_group("standard_2Q");
    group.sample_size(16);
    for params in PARAMS.iter() {
        let mut cache = QQ::new(params.0, params.1, MEM_SIZE - params.0 - params.1);
        let id = format!("({}, {}, {})", params.0, params.1, MEM_SIZE - params.0 - params.1);
        bench_cache!(&mut cache, &mut group, id);
    }
    group.finish();
}

pub fn qq_lfu(c: &mut Criterion) {
    prepare_data();

    let mut group = c.benchmark_group("2Q-LFU");
    group.sample_size(16);

    // const generics can't (yet?) be used inside loops
    let mut cache = QQLFU::<_, _, {MEM_SIZE - PARAMS[0].0 - PARAMS[0].1}>::new(PARAMS[0].0, PARAMS[0].1);
    let id = format!("({}, {}, {})", PARAMS[0].0, PARAMS[0].1, MEM_SIZE - PARAMS[0].0 - PARAMS[0].1);
    bench_cache!(&mut cache, &mut group, id);

    let mut cache = QQLFU::<_, _, {MEM_SIZE - PARAMS[1].0 - PARAMS[1].1}>::new(PARAMS[1].0, PARAMS[1].1);
    let id = format!("({}, {}, {})", PARAMS[1].0, PARAMS[1].1, MEM_SIZE - PARAMS[1].0 - PARAMS[1].1);
    bench_cache!(&mut cache, &mut group, id);
    
    let mut cache = QQLFU::<_, _, {MEM_SIZE - PARAMS[2].0 - PARAMS[2].1}>::new(PARAMS[2].0, PARAMS[2].1);
    let id = format!("({}, {}, {})", PARAMS[2].0, PARAMS[2].1, MEM_SIZE - PARAMS[2].0 - PARAMS[2].1);
    bench_cache!(&mut cache, &mut group, id);

    group.finish();
}


criterion_group!(qqs, qq_standard, qq_lfu);
criterion_main!(qqs);


// This is how the real-usecase sample is expanded: since the sample includes keys from 0 to 18,
// we are able to increment each by 19 and get the same sequence with disjunct keys.
// In this way, we work with STREAM_COUNT identical sequences on different keys.. we 'merge' them
// together randomly to reach a sequence of a total of DATA_LENGTH elements (once any of these
// 'streams' reaches the 57th element it has, it just overflows to the beginning again)

fn prepare_data() {
    if unsafe { !GENERATED_DATA.is_null() } {
        return;
    }

    // property of the sample
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
