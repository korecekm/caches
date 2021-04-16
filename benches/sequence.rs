use caches::lru::LRUCache as LRU;
use caches::rr::RRCache as RR;
use criterion::*;
use criterion::measurement::{Measurement, ValueFormatter};
use rand::{thread_rng, Rng};
use std::ptr;
use std::sync::Mutex;
use std::thread;

// 
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

// how long a thread sleeps after a cache miss (to simulate HDD lookup)
// const MISS_PENALTY: Duration = Duration::from_millis(10);

const THREAD_COUNTS: [usize; 5] = [2, 4, 8, 12, 16];
static mut MISS_COUNT: *const Mutex<u32> = ptr::null();

static mut SEQUENCE: *const Vec<u64> = ptr::null();
static mut LRUS: *const Vec<LRU<u64, ()>> = ptr::null();
static mut RRS: *const Vec<RR<u64, ()>> = ptr::null();


pub fn lru_each(c: &mut Criterion<Misses>) {
    if unsafe { SEQUENCE.is_null() } {
        prepare_sequence();
    }

    let mut group = c.benchmark_group("lru_each_thread");
    for thread_count in THREAD_COUNTS.iter() {
        group.bench_with_input(
            BenchmarkId::from_parameter(thread_count),
            thread_count,
            |b, &size| {
                b.iter_custom(|iters| {
                    // prepare the LRUs:
                    let mut caches = Vec::with_capacity(size);
                    for _ in 0..size {
                        caches.push(LRU::new(MEM_SIZE / size));
                    }
                    unsafe {
                        LRUS = &caches;
                    }

                    // Run sequence once without counting misses to then work with a full cache
                    let mock_count = Mutex::new(0u32);
                    unsafe {
                        MISS_COUNT = &mock_count;
                    }
                    perform_lru_each(size);

                    let miss_count = Mutex::new(0u32);
                    unsafe {
                        MISS_COUNT = &miss_count;
                    }
                    for _ in 0..iters {
                        perform_lru_each(size);
                    }
                    let count = *miss_count.lock().unwrap();
                    //count
                    iters as u32 * 4
                })
            }
        );
    }
    group.finish();
}

fn miss_counting() -> Criterion<Misses> {
    Criterion::default().with_measurement(Misses)
}

/*
pub fn rr_each(c: &mut Criterion) {}
pub fn lru_lock(c: &mut Criterion) {}
pub fn rr_lock(c: &mut Criterion) {}

criterion_group!(each_thread, lru_each, rr_each);
criterion_group!(lock, lru_lock, rr_lock);
criterion_main!(each_thread, lock);*/
criterion_group! {
    name = lru;
    config = miss_counting();
    targets = lru_each
}
criterion_main!(lru);

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


macro_rules! iterate_sequence {
    ($cache:expr, $start_idx:expr) => {
        let mut idx = $start_idx;
        for _ in 0..SEQUENCE_LENGTH {
            let elem = unsafe {
                (*SEQUENCE)[idx].clone()
            };

            if $cache.get(&elem).is_none() {
                // cache miss
                unsafe {
                    *(*MISS_COUNT).lock().unwrap() += 1;
                }

                $cache.insert(elem, ());
            }
            idx = (idx + 1) % (SEQUENCE_LENGTH as usize);
        }
    };
}

fn perform_lru_each(thread_count: usize) {
    let mut handles = Vec::with_capacity(thread_count);
    for i in 0..thread_count {
        let join_handle = thread::spawn(move || {
            black_box(move || {
                iterate_sequence!(
                    unsafe {
                        &mut (LRUS as *mut Vec<LRU<u64, ()>>).as_mut().unwrap()[i]
                    },
                    i * (SEQUENCE_LENGTH as usize / thread_count)
                );
            })
        });
        handles.push(join_handle);
    }
    for handle in handles {
        handle.join().unwrap();
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
        let v = (*mutex.lock().unwrap());
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