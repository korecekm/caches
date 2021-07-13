# The *.result* format

Our measurements that count the number of cache misses write their output into a simple special format. It is intended as input for visualization scripts, rather than to be human readable.

I only include the results for the `hit_rate` benchmark here, as examples, but running the `cache_parameter_comparison` benchmark
will generate its results into this directory as well. And of course, running the `hit_rate` benchmark will rewrite these two initial files
(which will most likely lead to a little different results for `Random replacement`, but shouldn't change the results for the rest).

There are 3 types of miss count measurements we make, and so there are also 3 types of result files:
* **2D single** is the simplest, it counts the misses for a single datastructure with different parameters (it is currently only used to evaluate the parameters for the *LIRS* replacement strategy)
* **2D multi** is like *2D single*, but it counts misses for several structures instead of one (we use it to count the misses by cache size for the different replacement strategies)
* **3D** is used to evaluate the right parameters for the *2Q* and *2Q-LFU* replacement strategies. These structures are parameterized by two values rather than one.

### The format itself

All 3 types share the first five lines in their result files. Those contain
1. The measurement type (i.e. "2D single", "2D multi", or "3D", as described above)
2. The title (name) of our measurement
3. The number of unique keys that get accessed throughout the measurement
4. The total number of accesses *minus* the number of unique keys (the number on line 3, this number also gets subtracted from the miss counts, because when a key is accessed for the very first time, it induces a necessary cache miss)
5. *separated by spaces*: the sequence of numerical parameters for which we measure (in the case of the *3D* measurements, this really is just one sequence, because we measure for a cartesian power of the sequence)

Further lines differ by measurement type:

#### 2D single:
6. The name of our parameter (i.e. "HIR capacity" in the case of the LIRS strategy, which turned out to be the only usage of *2D single*)
7. *separated by spaces*: The miss counts themselves (the same count as there are parameters, the result for each parameter, that is)

#### 2D multi:
As this type of measurement evaluates multiple caching schemes, each separate result is described in two consecutive lines that contain
* The name of the measured item (i.e. cache replacement strategy)
* same as line *7.* in *2D single*, featuring the results for the item stated on previous line

#### 3D:
Line *6* and *7* tell us the names of the first and second parameter measured, respectively.

Then follow lines with triplets (separated by spaces) containing **[value of param. 1]** **[value of param. 2]** **[the measured miss count]**. These lines proceed in an arbitrary order, but describe state the results for the whole cartesian product of the parameter sequence stated on line *5.*
