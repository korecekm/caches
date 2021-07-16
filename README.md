# Caches

This directory contains source files written in the Rust programming language as a part of the bachelor thesis "*A Comparison of Strategies for Database Caching*" by Martin Koreček. They provide implementations of cache replacement policies, concurrent adaptations of cache data structures, and benchmarks that attempt to evaluate them. The following sections provide essential information about the presented files. Each source file includes comments that attempt to explain its source code in particular.

The code is intended to answer the research questions of the thesis.

## Sequential cache data structures

The `lru.rs`, `qq.rs`, `arc.rs`, `lfu.rs`, `qq_lfu.rs`, `lirs.rs`, `clock.rs`, `clock_pro.rs` and `rr.rs` files in the `src` directory provide implementations of sequential cache data structures with the *LRU*, *2Q*, *ARC*, *LFU*, *2Q-LFU*, *LIRS*, *CLOCK*, *CLOCK-Pro* and *Random replacement* replacement logic, respectively.

All of these caches are designed to store up to a given number (capacity) of **key-value** pairs. Each provides two fundamental cache methods:

* `get`: Receives a reference to a **key** and returns a reference to its **value**, if stored. Usually also updates the data structure's state, depending on the implemented replacement policy.
* `insert`: Receives a **key-value**, where the **key** is not in the cache yet, and submits it for caching (inserts it into the data structure), potentially evicting another **key-value** pair based on the replacement policy.

Several of the data structures utilize a doubly linked list implemented in the `src/list.rs` file.

## Concurrent adaptations of caches

Next, we have two special data structures, providing an "*associative*" and a "*transactional*" version of the *LRU* cache, implemented in `src/lru_associative.rs` and `src/lru_transactional.rs`. More information about them is, firstly, in sections **3.2**, **3.4** and **4.2**, **4.4** of the thesis, and secondly in their source files. The transactional cache uses one of our transactional hash maps.

## Transactional hash maps

We provide two implementations of transactional **key-value** hash maps. They are discussed in section **6.5** of the thesis. One, located in `src/bptree_hashmap.rs` stores its records in the transactional B+ Tree from `src/bpt_transactional.rs`, ordered by the hashes of keys. The other, inside `src/trie_hashmap.rs` approaches the hashes like a trie, storing values at a constant depth. Our transactional LRU cache uses this implementation.

## Benchmarks

The `benches` directory contains the following types of benchmarks:

### Measurements that count the cache misses encountered with different cache replacement policies

The measurements in `cache_parameter_comparison.rs` and `hit_rate.rs` serve to provide the results for **Chapter 2.** and sections **6.1** and **6.2** of the thesis. To find out more about how they do it, please read their documentations at the beginning of the two files.

### Measurements that evaluate the in memory performance of the data structures

Benchmarks in `single_thread.rs` and `concurrent.rs` use the **Criterion** micro-benchmarking library measure the execution times of our sequential cache structures, and the (simulations of) concurrent approaches discussed in chapters **3** and **4**. They provide the results for chapter **5**.

Another benchmark uses **Criterion** to measure execution times, namely the one in `hashmaps_bench.rs`, which attempts to compare the performance of our two transactional hash map implementations. The trie-based approach turned out to be perceptibly faster, which is why the transactional LRU uses it.

---

*Note that the code samples in the Rust docs (comments) in the source files aren't intended as standalone code, and therefore won't build. By default, Cargo tests the validity of the code in the docs, which is not desirable for us. If you wish to run the tests for this library, run with `cargo test --lib`.*

*The benchmarks in this directory are intended to be run separately (which can be done using `cargo bench [benchmark_filename]`). Some write into our custom `.result` files, some use the `criterion` library for the evaluation of execution times.*
