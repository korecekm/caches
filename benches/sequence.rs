use caches::lru::LRUCache as LRU;
use caches::rr::RRCache as RR;
use caches::qq::QCache as QQ;
use criterion::*;
use criterion::measurement::{Measurement, ValueFormatter};
use rand::{thread_rng, Rng};
use std::ptr;
use std::sync::Mutex;
use std::thread;

//
//
//

const SEQUENCE_LENGTH: u64 = 0x10000;
// total number of records
const MEM_SIZE: usize = 0x400;
// how many times the size of a step the generated range will be
const RANGE: u64 = 10;
// all keys will be in the range [0, MOD)
const MOD: u64 = 0x10000000;
//const THREAD_COUNTS: [usize; 5] = [2, 4, 8, 12, 16];
const THREAD_COUNTS: [usize; 2] = [2, 16];

static mut MISS_COUNT: *const Mutex<u32> = ptr::null();
static mut SEQUENCE: *const Vec<u64> = ptr::null();

static mut LRU_LOCK: *const Mutex<LRU<u64, ()>> = ptr::null();
static mut RR_LOCK: *const Mutex<RR<u64, ()>> = ptr::null();
static mut QQ_LOCK: *const Mutex<QQ<u64, ()>> = ptr::null();

// macros supplying general benchmarked behavior:

// iterate SEQUENCE with a sequential cache
macro_rules! iterate_sequence_basic {
    ($cache:expr, $miss_count:expr) => {
        for i in 0..(SEQUENCE_LENGTH as usize) {
            let elem = unsafe {
                (*SEQUENCE)[i].clone()
            };

            if $cache.get(&elem).is_none() {
                // cache miss
                *$miss_count += 1;

                $cache.insert(elem, ());
            }
        }
    };
}

// iterate SEQUENCE with a cache inside a mutex
macro_rules! iterate_sequence_lock {
    ($cache:expr, $start_idx:expr) => {
        let mut idx = $start_idx;
        for _ in 0..SEQUENCE_LENGTH {
            let elem = unsafe {
                (*SEQUENCE)[idx].clone()
            };

            let mut cache_guard = (*$cache).lock().unwrap();
            if (*cache_guard).get(&elem).is_none() {
                // cache miss
                unsafe {
                    *(*MISS_COUNT).lock().unwrap() += 1;
                }

                (*cache_guard).insert(elem, ());
            }
            idx = (idx + 1) % (SEQUENCE_LENGTH as usize);
        }
    };
}

// the benchmarked behavior itself for caches behind a mutex
macro_rules! perform_lock {
    ($thread_count:expr, $cache:expr, $as:ty) => {
        let mut handles = Vec::with_capacity($thread_count);
        for i in 0..$thread_count {
            let join_handle = thread::spawn(move || {
                iterate_sequence_lock!(
                    unsafe {
                        ($cache as *mut $as).as_mut().unwrap()
                    },
                    i * (SEQUENCE_LENGTH as usize / $thread_count)
                );
            });
            handles.push(join_handle);
        }
        for handle in handles {
            handle.join().unwrap();
        }
    };
}


pub fn lru_each(c: &mut Criterion<Misses>) {
    if unsafe { SEQUENCE.is_null() } {
        prepare_sequence();
    }

    let mut group = c.benchmark_group("lru_each_thread");
    for thread_count in THREAD_COUNTS.iter() {
        group.bench_with_input(
            BenchmarkId::from_parameter(thread_count),
            thread_count,
            |b, &count| {
                b.iter_custom(|iters| {
                    // prepare cache and miss count
                    let mut cache = LRU::new(MEM_SIZE / count);
                    let mut mock_count = 0;
                    let mut miss_count = 0;

                    // Run once without counting misses to fill cache
                    iterate_sequence_basic!(&mut cache, &mut mock_count);
                    // Now count the misses
                    iterate_sequence_basic!(&mut cache, &mut miss_count);

                    // the count won't be different for other iterations since this benchmark is sequential
                    iters as u32 * miss_count
                })
            }
        );
    }
    group.finish();
}

pub fn lru_lock(c: &mut Criterion<Misses>) {
    if unsafe { SEQUENCE.is_null() } {
        prepare_sequence();
    }

    let mut group = c.benchmark_group("lru_lock");
    for thread_count in THREAD_COUNTS.iter() {
        group.bench_with_input(
            BenchmarkId::from_parameter(thread_count),
            thread_count,
            |b, &threads| {
                b.iter_custom(|iters| {
                    // prepare cache and miss count
                    let cache = Box::into_raw(Box::new(Mutex::new(LRU::new(MEM_SIZE))));
                    unsafe {
                        LRU_LOCK = cache;
                    }
                    let mock_count = Box::into_raw(Box::new(Mutex::new(0)));
                    let miss_count = Box::into_raw(Box::new(Mutex::new(0)));

                    // Run once without counting misses to fill cache
                    unsafe {
                        MISS_COUNT = mock_count;
                    }
                    perform_lock!(threads, LRU_LOCK, Mutex<LRU<u64, ()>>);
                    // Now 'iters' times with counting
                    unsafe {
                        MISS_COUNT = miss_count;
                    }
                    for _ in 0..iters {
                        perform_lock!(threads, LRU_LOCK, Mutex<LRU<u64, ()>>);
                    }

                    unsafe {
                        Box::from_raw(cache);
                        Box::from_raw(mock_count);
                    }
                    let misses = unsafe {
                        *(*Box::from_raw(miss_count)).lock().unwrap()
                    };
                    misses
                })
            }
        );
    }
    group.finish();
}

fn miss_counting() -> Criterion<Misses> {
    Criterion::default().with_measurement(Misses)
}

criterion_group! {
    name = each;
    config = miss_counting();
    targets = lru_each
}
criterion_group! {
    name = lock;
    config = miss_counting();
    targets = lru_lock
}
criterion_main!(each);

fn prepare_sequence() {
    let mut rng = thread_rng();
    let mut seq = Box::new(Vec::with_capacity(SEQUENCE_LENGTH as usize));
    let step = MOD / SEQUENCE_LENGTH;
    let range = RANGE * step;
    let mut offset = 0;
    for i in 0..SEQUENCE_LENGTH {
        let plus = rng.gen_range(0, range);
        (*seq).push((offset + plus) % MOD);
        offset += step;
    }
    unsafe {
        SEQUENCE = Box::into_raw(seq);
    }
}


pub struct Misses;
impl Measurement for Misses {
    type Intermediate = *mut Mutex<u32>;
    type Value = u32;
    fn start(&self) -> Self::Intermediate {
        Box::into_raw(Box::new(
            Mutex::new(0)
        ))
    }
    fn end(&self, i: Self::Intermediate) -> Self::Value {
        let mutex = unsafe {
            Box::from_raw(i)
        };
        let v = *mutex.lock().unwrap();
        v
    }
    fn add(&self, v1: &Self::Value, v2: &Self::Value) -> Self::Value {
        *v1 + *v2
    }
    fn zero(&self) -> Self::Value {
        0
    }
    fn to_f64(&self, val: &Self::Value) -> f64 {
        *val as f64
    }
    fn formatter(&self) -> &dyn ValueFormatter {
        &MissesFormatter
    }
}

struct MissesFormatter;
impl ValueFormatter for MissesFormatter {
    fn format_value(&self, value: f64) -> String {
        format!("{} misses", value)
    }
    fn format_throughput(&self, throughput: &Throughput, value: f64) -> String {
        match *throughput {
            Throughput::Bytes(bytes) => format!(
                "{} bytes/miss",
                bytes as f64 / value
            ),
            Throughput::Elements(elems) => format!(
                "{} elems/miss",
                elems as f64 / value
            ),
        }
    }
    fn scale_values(&self, ns: f64, values: &mut [f64]) -> &'static str {
        "misses"
    }
    fn scale_throughputs(
        &self,
        _typical: f64,
        throughput: &Throughput,
        values: &mut [f64],
    ) -> &'static str {
        match *throughput {
            Throughput::Bytes(bytes) => {
                for val in values {
                    *val = (bytes as f64) / *val
                }
                "{} bytes/miss"
            }
            Throughput::Elements(elems) => {
                for val in values {
                    *val = (elems as f64) / *val;
                }
                "{} elems/miss"
            }
        }
    }
    fn scale_for_machines(&self, values: &mut [f64]) -> &'static str {
        "misses"
    }
}
