// This benchmark aims to see how our transactional hash map implementations fair against each
// other.. here, we only compare sequential behavior of write transactions (with no additional read
// transactions or concurrency whatsoever). The transactions get committed occasionally.
// In addition, we perform the same operations on the std::collections::HashMap (other than commit)
// just to see the comparison to the non-concurrent non-tree (and presumably well implemented)
// version.
// 
// We make two types of measurements, ones where we perform randomized queries, and ones where we
// only do updates to the hash maps (with the same generated records though).

use caches::bptree_hash_map::HashMap as BPTHM;
use caches::trie_hashmap::*;
use criterion::*;
use rand::{thread_rng, Rng};
use std::ptr;

// We will make three measurements for each type and each hash map implementation. They will
// perform on workloads generated with records of the specified query counts and key ranges
// (numbers of unique records that may be queried by our workloads)
const QUERY_COUNTS: [usize; 3] = [2000, 35000, 20000000];
const KEY_RANGES: [u32; 3] = [100, 3000, 100000];
// This is how queries are generated:
// 1) A random $choice variable is chosen from the [0, SEARCH_FREQ + INSERT_REMOVE_RANGE] range
// 2) If it's 0, commit will be performed
// 3) If it's in the [1, SEARCH_FREQ] range, search is queried
// 4) Otherwise, insert or remove is queried, with the probability of remove starting at zero and growing linearly
const SEARCH_FREQ: usize = 30;
const INSERT_REMOVE_RANGE: usize = 150;

// randomized queries
static mut QUERIES_STANDARD: [*const Vec<HashmapAction>; 3] = [ptr::null(); 3];
// only the keys are randomized, all queries are updates
static mut QUERIES_UPDATES: [*const Vec<HashmapAction>; 3] = [ptr::null(); 3];

/// Enum that describes an action of a hash map. We generate these actions at
/// random as workloads for our hash maps.
enum HashmapAction {
    Commit,
    Search(u32),
    Update(u32),
    Remove(u32),
}

// This macro performs all the queries of our workload on any hash maps we tell
// it to. So this is a way of producing measurements generically.
macro_rules! bench_hashmap {
    // We need to provide: a name for our benchmark (measurement), a mutable
    // reference to the global Criterion struct, what type of queries we want
    // to measure with (only updates vs. all kinds), and finally the function
    // that will perform the queries themselves - this actually determines what
    // hash map implementation we are measuring.
    ($bench_name:expr, $criterion:expr, $query_type:expr, $func:expr) => {
        // Generate the workload, if not yet generated
        prepare_benches();
        let mut group = $criterion.benchmark_group($bench_name);
        for bench_idx in 0..3 {
            // Perform for all the key ranges and query counts we want:
            group.bench_with_input(
                BenchmarkId::from_parameter(format!(
                    "({}, {})",
                    KEY_RANGES[bench_idx], QUERY_COUNTS[bench_idx]
                )),
                &bench_idx,
                |b, &idx| {
                    b.iter_batched(
                        || unsafe { &(*$query_type[idx]) },
                        // Call the given function that performs the queries themselves.
                        |queries| black_box($func(queries)),
                        BatchSize::SmallInput,
                    )
                },
            );
        }
        group.finish();
    };
}

// FUNCTIONS THAT INVOKE THE MEASUREMENTS (by expanding `bench_hashmap` in the correct ways):

pub fn std_standard(c: &mut Criterion) {
    bench_hashmap!(
        "STD_hashmap-standard",
        c,
        QUERIES_STANDARD,
        perform_stdhashmap_bench
    );
}

pub fn trie_standard(c: &mut Criterion) {
    bench_hashmap!(
        "trie-standard",
        c,
        QUERIES_STANDARD,
        perform_triehashmap_bench
    );
}

pub fn bptree_standard(c: &mut Criterion) {
    bench_hashmap!("B+Tree-standard", c, QUERIES_STANDARD, perform_bptree_bench);
}

pub fn std_updates(c: &mut Criterion) {
    bench_hashmap!(
        "STD_hashmap-just_updates",
        c,
        QUERIES_UPDATES,
        perform_stdhashmap_bench
    );
}

pub fn trie_updates(c: &mut Criterion) {
    bench_hashmap!(
        "trie-just_updates",
        c,
        QUERIES_UPDATES,
        perform_triehashmap_bench
    );
}

pub fn bptree_updates(c: &mut Criterion) {
    bench_hashmap!(
        "B+Tree-just_updates",
        c,
        QUERIES_UPDATES,
        perform_bptree_bench
    );
}

/// A special bench function that iterates the queries like the other
/// measurement, but doesn't actually perform any hash map actions, so that we
/// can see how much time overhead the benchmark has alone.
pub fn null_bench(c: &mut Criterion) {
    prepare_benches();
    let mut group = c.benchmark_group("null-benchmark");
    for bench_idx in 0..3 {
        let query_count = QUERY_COUNTS[bench_idx];
        group.bench_with_input(
            BenchmarkId::from_parameter(query_count),
            &bench_idx,
            |b, &idx| {
                b.iter_batched(
                    || unsafe { &*QUERIES_STANDARD[idx] },
                    |queries| black_box(perform_null_bench(queries)),
                    BatchSize::SmallInput,
                )
            }
        );
    }
    group.finish();
}

criterion_group!(
    standard,
    std_standard,
    trie_standard,
    bptree_standard
);
criterion_group!(
    updates,
    std_updates,
    trie_updates,
    bptree_updates
);
criterion_group!(null, null_bench);
criterion_main!(standard, updates, null);

// HASHMAP ACTIONS GENERATION:

fn prepare_benches() {
    if unsafe { QUERIES_STANDARD[0].is_null() } {
        for idx in 0..3 {
            let mut standard = Box::new(Vec::with_capacity(QUERY_COUNTS[idx]));
            let mut updates = Box::new(Vec::with_capacity(QUERY_COUNTS[idx]));
            prepare(idx, &mut *standard, &mut *updates);
            unsafe {
                QUERIES_STANDARD[idx] = Box::into_raw(standard);
                QUERIES_UPDATES[idx] = Box::into_raw(updates);
            }
        }
    }
}

// All hashmaps shall work with the same queries (although std-hashmap doesn't perform commits).
// Therefore a vector of queries is generated only once and kept via a static pointer.
// (it's never dropped, but that's no issue in a benchmark process)
fn prepare(idx: usize, standard: &mut Vec<HashmapAction>, updates: &mut Vec<HashmapAction>) {
    let mut rng = thread_rng();
    let query_count = QUERY_COUNTS[idx];
    let key_range = KEY_RANGES[idx];
    for i in 0..query_count {
        let key = rng.gen_range(0, key_range);
        updates.push(HashmapAction::Update(key));
        let mut choice = rng.gen_range(0, 1 + SEARCH_FREQ + INSERT_REMOVE_RANGE);
        if choice == 0 {
            standard.push(HashmapAction::Commit);
        } else if choice <= SEARCH_FREQ {
            standard.push(HashmapAction::Search(key));
        } else {
            // insert / remove
            choice -= SEARCH_FREQ + 1;
            let margin = i / (query_count / INSERT_REMOVE_RANGE);
            if choice < margin {
                standard.push(HashmapAction::Remove(key));
            } else {
                standard.push(HashmapAction::Update(key));
            }
        }
    }
}

// UTILITY FUNCTIONS THAT PERFORM THE ACTUAL ITERATION:

/// The actions of our transactional trie hash map
fn perform_triehashmap_bench(queries: &Vec<HashmapAction>) {
    let map = TrieMap::new();
    let mut write_txn = map.write();
    for q in queries.iter() {
        match q {
            HashmapAction::Commit => {
                write_txn.commit();
                write_txn = map.write();
            }
            HashmapAction::Search(k) => {
                write_txn.search(&k);
            }
            HashmapAction::Update(k) => {
                write_txn.update(k, ());
            }
            HashmapAction::Remove(k) => {
                write_txn.remove(&k);
            }
        }
    }
}

/// The actions of our transactional B+-tree-based hash map
fn perform_bptree_bench(queries: &Vec<HashmapAction>) {
    let map = BPTHM::new();
    let mut write_txn = map.write();
    for q in queries.iter() {
        match q {
            HashmapAction::Commit => {
                write_txn.commit();
                write_txn = map.write();
            }
            HashmapAction::Search(k) => {
                write_txn.search(&k);
            }
            HashmapAction::Update(k) => {
                write_txn.update(k, ());
            }
            HashmapAction::Remove(k) => {
                write_txn.remove(&k);
            }
        }
    }
}

/// The actions of the standard library's sequential hash maps (we ommit
/// commits)
fn perform_stdhashmap_bench(queries: &Vec<HashmapAction>) {
    let mut map = std::collections::hash_map::HashMap::new();
    for q in queries.iter() {
        match q {
            HashmapAction::Commit => {}
            HashmapAction::Search(k) => {
                map.get(&k);
            }
            HashmapAction::Update(k) => {
                map.insert(k, ());
            }
            HashmapAction::Remove(k) => {
                map.remove(&k);
            }
        }
    }
}

/// Mock actions for the "NULL" measurement (it works with an empty trie map,
/// so no actual hash map actions are ever done)
fn perform_null_bench(queries: &Vec<HashmapAction>) {
    let map = TrieMap::<u32, ()>::new();
    let write_txn = map.write();
    for q in queries.iter() {
        // hopefully this doesn't get optimized inside the black_box
        match q {
            HashmapAction::Commit => {}
            HashmapAction::Search(k) => {
                write_txn.search(&k);
            }
            HashmapAction::Update(k) => {
                write_txn.search(&k);
            }
            HashmapAction::Remove(k) => {
                write_txn.search(&k);
            }
        }
    }
}
