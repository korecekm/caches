// This bench file is intended to reveal how different parameters given to the parameterized
// replecament policies (2Q, 2Q-LFU and LIRS) affect their performance, and which choices of the
// parameters work well.
// 
// The LIRS data structure only requires setting its parameter (the HIR capacity) in runtime, when
// making its instance with the `new` function, but the 2Q-LFU is implemented with a const generic
// size of its main (priority) queue. Const generics need to be know at compile-time, so we need to
// be a little crafty with macros to be able to specify all the evaluated parameters at just one
// place in this source file.
// 
// If you want to get to understand the code here, I would recommend looking first at the `main`
// function and its associated comments, and move on to the function and macros it 'calls'.
// 
// The measurements work by simulating the workload from access logs in our custom `.in` files
// located in the benches/access_logs directory (more about this file format can be found in the
// directory's README).
// 
// The measured results get written into their appropriate `.result` files into the benches/result
// directory (each total cache capacity for each of the policies into a separate file). More about
// our custom `.result` format is to be found in the directory's README (the "2D multi" type
// doesn't concern us here, only "2D single" for LIRS and "3D" for 2Q and 2Q-LFU; the "3D" type
// format is actually adapted a little to suite the possibilities of macros to iterate through the
// cartesian product of its parameters... more in the comments above the `perform_qqs` macro).

use caches::qq::QCache as QQ;
use caches::qq_lfu::QQLFUCache as QQLFU;
use caches::lirs::LIRSCache as Lirs;
use std::fs::File;
use std::io::{BufRead, BufReader};
use std::ptr;
use std::io::Write;

// We perform measurements for 2 access logs
const MEASUREMENT_COUNT: usize = 2;
// These are the names of the files containing the access logs
const ACCESS_FILENAMES: [&str; MEASUREMENT_COUNT] = ["output", "Carabas"];
// And this is what we call them in the generated `.result` files
const LOG_NAMES: [&str; MEASUREMENT_COUNT] = ["Log 1", "Log 2"];

// The accesses to record keys in our access logs get imported to this vector.
// The measurement functions than iterate through it and simulate cache
// behavior.
static mut ACCESSES: *const Vec<u16> = ptr::null();
// The total number of unique keys that are accessed in the currently processed
// log file.
static mut UNIQUE_KEY_COUNT: usize = 0;
// The `.result` file into which we generate the results for the QQ policy
static mut QQ_RESULT_FILE: *const File = ptr::null();
// The `.result` file into which we generate the results for the QQ-LFU policy
static mut QQ_LFU_RESULT_FILE: *const File = ptr::null();

// This macro counts all the misses
macro_rules! count_cache {
    ($cache:expr) => {{
        let mut miss_count = 0;
        // Iterate through the keys in the access log, if a record isn't
        // already present in the cache, it's a cache miss and we insert it.
        for key in unsafe { (*ACCESSES).iter() } {
            if $cache.get(&key).is_none() {
                // cache miss
                miss_count += 1;
                $cache.insert(*key, ());
            }
        }
        // As with any of our miss counting measurements, we subtract the
        // number of unique keys in the access log, because the first access
        // to each of them is an inevitable miss and we choose to not count
        // these misses.
        unsafe {
            miss_count - UNIQUE_KEY_COUNT
        }
    }}
}

// Receives the capacities of all three queues of the 2Q (q3 being the main
// one), initiates the cache and writes the miss count for this combination of
// parameters into the result file.
macro_rules! count_qq {
    ($q1_capacity:expr, $q2_capacity:expr, $q3_capacity:expr) => {
        // Get access to the File handle
        let writefile = unsafe {
            &mut *(QQ_RESULT_FILE as *mut File)
        };
        // Init the cache.
        let mut cache = QQ::<u16, ()>::new($q1_capacity, $q2_capacity, $q3_capacity);
        // Write the result into the file. That is, write the Q1 size, Q2 size
        // and the miss count (the total capacity is already written in the
        // file).
        writeln!(writefile, "{} {} {}", $q1_capacity, $q2_capacity, count_cache!(&mut cache)).unwrap();
    };
}

// Receives the capacities of all three queues of the 2Q-LFU (q3 being the main
// priority queue), initiates the cache and writes the miss count for this
// combination of parameters into the result file.
macro_rules! count_qq_lfu {
    ($q1_capacity:expr, $q2_capacity:expr, $q3_capacity:expr) => {
        // Get access to the File handle
        let writefile = unsafe {
            &mut *(QQ_LFU_RESULT_FILE as *mut File)
        };
        // Init the cache (the heap size being a const generic)
        let mut cache = QQLFU::<u16, (), $q3_capacity>::new($q1_capacity, $q2_capacity);
        // Write the result into the file. That is, write the Q1 size, Q2 size
        // and the miss count (the total capacity is already written in the
        // file).
        writeln!(writefile, "{} {} {}", $q1_capacity, $q2_capacity, count_cache!(&mut cache)).unwrap();
    };
}

// This macro takes care of both the 2Q and 2Q-LFU measurements. The `main`
// function expands this macro with parameters of the last type, the $log_idx
// is there to know which access log we are working with, then the total
// capacity of the caches is given, and then the sizes of Q1 and Q2 to try out.
// Actually, the cartesian product of the $($all) parameters is tried for the
// queue sizes.
// But since 2Q-LFU uses const generics for the size of its main (priority)
// queue, we need to expand this cartesian product with a macro. This is not
// such an easy task. For that, we use three additional keywords for our
// params:
// * `single`: expansions starting with the `single` keyword are responsible
//   for the "diagonal" of the cartesian product - the "second powers"
// * `pairs` are the rest, ie. the distinct pairs of Q1 and Q2 sizes
// * `unroll` is a utility expansion to expand `pairs` for all the distinct
//   pairs of parameters (just once each)
macro_rules! perform_qqs {
    // Expansion responsible for performing the measurement with a pair of
    // different queue sizes (i.e. both permutations of the sizes)
    (pairs $capacity_total:expr, $first:expr, $second:expr) => {
        // Perform for the 2Q
        count_qq!($first, $second, { $capacity_total - $first - $second });
        count_qq!($second, $first, { $capacity_total - $first - $second });
        // Perform for the 2Q-LFU
        count_qq_lfu!($first, $second, { $capacity_total - $first - $second });
        count_qq_lfu!($second, $first, { $capacity_total - $first - $second });
    };
    // Expansion responsible for trying one parameter for both Q1 and Q2 size
    (single $capacity_total:expr, $first:expr) => {
        count_qq!($first, $first, { $capacity_total - 2 * $first });
        count_qq_lfu!($first, $first, { $capacity_total - 2 * $first });
    };
    // Expansion responsible for trying one parameter for both Q1 and Q2 size
    // and expanding this further to the rest of the params
    (single $capacity_total:expr, $first:expr, $($rest:expr),*) => {
        count_qq!($first, $first, { $capacity_total - 2 * $first });
        count_qq_lfu!($first, $first, { $capacity_total - 2 * $first });
        perform_qqs!(single $capacity_total, $($rest),*)
    };
    // The final expansion with the `unroll` keyword
    (unroll $capacity_total:expr, $first:expr, $second:expr) => {
        perform_qqs!(pairs $capacity_total, $first, $second);
    };
    // Makes the `pairs` expansion of this macro be called for all pairs with
    // one param being $first, and the other being one of the $($rest)
    (unroll $capacity_total:expr, $first:expr, $second:expr, $($rest:expr),*) => {
        perform_qqs!(pairs $capacity_total, $first, $second);
        perform_qqs!(unroll $capacity_total, $first, $($rest),*);
    };
    // Takes care of expanding into all measurements for distinct pairs of the
    // {$first, $second, $($rest)} set
    (pairs $capacity_total:expr, $first:expr, $second:expr, $($rest:expr),*) => {
        perform_qqs!(unroll $capacity_total, $first, $second, $($rest),*);
        perform_qqs!(pairs $capacity_total, $second, $($rest),*);
    };
    // The main expansion. Initiates the result files and expands all necessary
    // versions of this macro to produce the cartesian product of $($all)
    ($log_idx:expr, $capacity_total:expr, $($all:expr),*) => {
        // INITIATE THE RESULT FILES:
        // More about these files in the README in benches/results.
        // What we do here is write the first parts of the two (2Q and 2Q-LFU)
        // result files.
        let qq_writepath = format!("benches/results/2q_params-{}-capacity-{}.result", ACCESS_FILENAMES[$log_idx], $capacity_total);
        let qq_lfu_writepath = format!("benches/results/2q_lfu_params-{}-capacity-{}.result", ACCESS_FILENAMES[$log_idx], $capacity_total);

        // 2Q
        let mut qq_writefile = File::create(qq_writepath).unwrap();
        // Plot type
        writeln!(&mut qq_writefile, "3D").unwrap();
        // Plot title
        writeln!(&mut qq_writefile, "{}: 2Q parameters (total capacity {})", LOG_NAMES[$log_idx], $capacity_total).unwrap();
        // Unique key count
        writeln!(&mut qq_writefile, "{}", unsafe { UNIQUE_KEY_COUNT }).unwrap();
        // ("Significant") query count
        writeln!(&mut qq_writefile, "{}", unsafe { (*ACCESSES).len() - UNIQUE_KEY_COUNT }).unwrap();

        // 2Q LFU
        let mut qq_lfu_writefile = File::create(qq_lfu_writepath).unwrap();
        // Plot type
        writeln!(&mut qq_lfu_writefile, "3D").unwrap();
        // Plot title
        writeln!(&mut qq_lfu_writefile, "{}: 2Q-LFU parameters (total capacity {})", LOG_NAMES[$log_idx], $capacity_total).unwrap();
        // Unique key count
        writeln!(&mut qq_lfu_writefile, "{}", unsafe { UNIQUE_KEY_COUNT }).unwrap();
        // ("Significant") query count
        writeln!(&mut qq_lfu_writefile, "{}", unsafe { (*ACCESSES).len() - UNIQUE_KEY_COUNT }).unwrap();

        // Parameter array for both
        $(
            write!(&mut qq_writefile, " {}", $all).unwrap();
            write!(&mut qq_lfu_writefile, " {}", $all).unwrap();
        )*
        writeln!(&mut qq_writefile, "").unwrap();
        writeln!(&mut qq_lfu_writefile, "").unwrap();

        // And finally the labels for the parameter axes
        writeln!(&mut qq_writefile, "1st queue size").unwrap();
        writeln!(&mut qq_writefile, "2nd queue size").unwrap();
        writeln!(&mut qq_lfu_writefile, "1st queue size").unwrap();
        writeln!(&mut qq_lfu_writefile, "2nd queue size").unwrap();

        // Put the File handles into static variables to make things easier
        unsafe {
            QQ_RESULT_FILE = Box::into_raw(Box::new(qq_writefile));
            QQ_LFU_RESULT_FILE = Box::into_raw(Box::new(qq_lfu_writefile));
        }

        // Count misses for all combinations of the cache's parameters:
        // First, the (x, x) type of parameter pairs
        perform_qqs!(single $capacity_total, $($all),*);
        // Second, the (x, y) type
        perform_qqs!(pairs $capacity_total, $($all),*);

        // Close the files
        unsafe {
            Box::from_raw(QQ_RESULT_FILE as *mut File);
            Box::from_raw(QQ_LFU_RESULT_FILE as *mut File);
        }
    };
}

/// Receives the total capacity of our cache, an array of HIR capacities to
/// try, and performs the whole measurement for the LIRS of this total
/// capacity, writing the results in the appropriate result file.
fn perform_lirs<const N: usize>(log_idx: usize, capacity_total: usize, hir_capacities: [usize; N]) {
    // INITIATE THE RESULT FILE (of the "2D single" type):
    let lirs_writepath = format!("benches/results/lirs_params-{}-capacity-{}.result", ACCESS_FILENAMES[log_idx], capacity_total);
    let mut lirs_writefile = File::create(lirs_writepath).unwrap();
    // Plot type
    writeln!(&mut lirs_writefile, "2D single").unwrap();
    // Plot title
    writeln!(&mut lirs_writefile, "{}: LIRS parameters (total capacity {})", LOG_NAMES[log_idx], capacity_total).unwrap();
    // Unique key count
    writeln!(&mut lirs_writefile, "{}", unsafe { UNIQUE_KEY_COUNT }).unwrap();
    // ("Significant") query count
    writeln!(&mut lirs_writefile, "{}", unsafe { (*ACCESSES).len() - UNIQUE_KEY_COUNT }).unwrap();
    // Parameter array
    for h in hir_capacities.iter() {
        write!(&mut lirs_writefile, " {}", h).unwrap();
    }
    writeln!(&mut lirs_writefile, "").unwrap();
    // Horizontal axis label
    writeln!(&mut lirs_writefile, "HIR capacity").unwrap();
    
    // The comparison itself: iterate through the log file with the different
    // cache parameters.
    for h in hir_capacities.iter() {
        // Initiate the cache with this HIR capacity
        let mut cache = Lirs::<u16, ()>::new(capacity_total - *h, *h);
        // Write the miss count for it  into the result file.
        write!(&mut lirs_writefile, " {}", count_cache!(&mut cache)).unwrap();
    }
    writeln!(&mut lirs_writefile, "").unwrap();
}

/// The main function iterates through our (two) access logs and uses
/// appropriate macros to measure the effect of the parameters on the miss
/// counts, and write them into the right `.result` files.
fn main() {
    for idx in 0..MEASUREMENT_COUNT {
        // Informative print to stdout
        println!("Processing file {}...", ACCESS_FILENAMES[idx]);
        // Extract the access log from an `.in` file into the ACCESSES global
        // vector.
        let filepath = format!("benches/access_logs/{}.in", ACCESS_FILENAMES[idx]);
        prepare_data(&filepath);

        // 2Q and 2Q-LFU measurements
        perform_qqs!(idx, 300, 5, 10, 30, 100);
        perform_qqs!(idx, 600, 5, 10, 30, 70, 120, 230);
        perform_qqs!(idx, 1000, 10, 55, 100, 250, 400);

        // LIRS measurements
        perform_lirs(idx, 200, [1, 2, 5, 10, 30, 50, 100]);
        perform_lirs(idx, 700, [2, 7, 20, 30, 50, 60, 120]);

        // Free the log from memory.
        unsafe {
            Box::from_raw(ACCESSES as *mut Vec<u16>);
        }
    }
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
