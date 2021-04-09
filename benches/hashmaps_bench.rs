// This benchmark aims to see how several transactional hash map implementations fair against each
// other.. here, we only compare sequential behavior of write transactions (with no additional read
// transactions or concurrency whatsoever). The transactions get committed occasionally.
// In addition, we perform the same operations on the std::collections::HashMap (other than commit)
// just to see the comparison to the non-concurrent non-tree (and presumably well implemented) version.

extern crate criterion;
extern crate rand;
extern crate caches;
extern crate concread;

use caches::trie_hashmap::*;
use caches::hash_map::HashMap as BPTHM;
use criterion::{criterion_group, criterion_main, BatchSize, Criterion, black_box};
use concache::manual::Map as ConcacheMap;
use rand::{thread_rng, Rng};
use std::ptr;

const QUERY_COUNT: usize = 35000;
const KEY_RANGE: u32 = 3000;
// This is how queries are generated:
// 1) A random $choice variable is chosen from the [0, SEARCH_FREQ + INSERT_REMOVE_RANGE] range
// 2) If it's 0, commit will be performed
// 3) If it's in the [1, SEARCH_FREQ] range, search is queried
// 4) Otherwise, insert or remove is queried, with the probability of remove starting at zero and growing linearly
const SEARCH_FREQ: usize = 30;
const INSERT_REMOVE_RANGE: usize = 150;

static mut QUERIES: *const Vec<HashmapAction> = ptr::null();

enum HashmapAction {
    Commit,
    Search(u32),
    Update(u32),
    Remove(u32),
}

pub fn triehashmap_bench(c: &mut Criterion) {
    c.bench_function("triehashmap_bench", |b| {
        b.iter_batched(
            || prepare_benches(),
            |queries| black_box(perform_triehashmap_bench(queries)),
            BatchSize::SmallInput,
        )
    });
}

pub fn concread_hashmap_bench(c: &mut Criterion) {
    c.bench_function("concread_hashmap_bench", |b| {
        b.iter_batched(
            || prepare_benches(),
            |queries| black_box(perform_concread_bench(queries)),
            BatchSize::SmallInput,
        )
    });
}

pub fn bptree_hashmap_bench(c: &mut Criterion) {
    c.bench_function("bptree_hashmap_bench", |b| {
        b.iter_batched(
            || prepare_benches(),
            |queries| black_box(perform_bptree_bench(queries)),
            BatchSize::SmallInput,
        )
    });
}

pub fn concache_hashmap_bench(c: &mut Criterion) {
    c.bench_function("concache_hashmap_bench", |b| {
        b.iter_batched(
            || prepare_benches(),
            |queries| black_box(perform_concache_bench(queries)),
            BatchSize::SmallInput,
        )
    });
}

pub fn stdhashmap_bench(c: &mut Criterion) {
    c.bench_function("std_hashmap_bench", |b| {
        b.iter_batched(
            || prepare_benches(),
            |queries| black_box(perform_stdhashmap_bench(queries)),
            BatchSize::SmallInput,
        )
    });
}

criterion_group!(
    hashmaps,
    triehashmap_bench,
    concread_hashmap_bench,
    bptree_hashmap_bench,
    concache_hashmap_bench,
    stdhashmap_bench
);
criterion_main!(hashmaps);

// All hashmaps shall work with the same queries (although std-hashmap doesn't perform commits).
// Therefore a vector of queries is generated only once and kept via a static pointer.
// (it's never dropped, but that's no issue in a benchmark process)
fn prepare_benches() -> &'static Vec<HashmapAction> {
    if unsafe { QUERIES.is_null() } {
        let mut rng = thread_rng();
        let mut queries = Box::new(Vec::with_capacity(QUERY_COUNT));
        for i in 0..QUERY_COUNT {
            let key = rng.gen_range(0, KEY_RANGE);
            let mut choice = rng.gen_range(0, 1 + SEARCH_FREQ + INSERT_REMOVE_RANGE);
            if choice == 0 {
                queries.push(HashmapAction::Commit);
            } else if choice <= SEARCH_FREQ {
                queries.push(HashmapAction::Search(key));
            } else {
                // insert / remove:
                choice -= SEARCH_FREQ + 1;
                let margin = i / (QUERY_COUNT / INSERT_REMOVE_RANGE);
                if choice < margin {
                    queries.push(HashmapAction::Remove(key));
                } else {
                    queries.push(HashmapAction::Update(key));
                }
            }
        }
        unsafe {
            QUERIES = Box::into_raw(queries);
        }
    }
    unsafe {
        &*QUERIES
    }
}

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

fn perform_concread_bench(queries: &'static Vec<HashmapAction>) {
    let map = concread::hashmap::HashMap::new();
    let mut write_txn = map.write();
    for q in queries.iter() {
        match q {
            HashmapAction::Commit => {
                write_txn.commit();
                write_txn = map.write();
            }
            HashmapAction::Search(k) => {
                write_txn.get(&k);
            }
            HashmapAction::Update(k) => {
                write_txn.insert(k, ());
            }
            HashmapAction::Remove(k) => {
                write_txn.remove(&k);
            }
        }
    }
}

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

fn perform_concache_bench(queries: &Vec<HashmapAction>) {
    // so that the capacity is the same as that of the current trie_hashmap
    let mut map_handle = ConcacheMap::with_capacity(32768);
    for q in queries.iter() {
        match q {
            HashmapAction::Commit => {},
            HashmapAction::Search(k) => {
                map_handle.get(&k);
            }
            HashmapAction::Update(k) => {
                map_handle.insert(k, ());
            }
            HashmapAction::Remove(k) => {
                map_handle.remove(&k);
            }
        }
    }
}

fn perform_stdhashmap_bench(queries: &Vec<HashmapAction>) {
    let mut map = std::collections::hash_map::HashMap::new();
    for q in queries.iter() {
        match q {
            HashmapAction::Commit => {},
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
