<!--
SPDX-FileCopyrightText: 2024 2023 Martin Koreček

SPDX-License-Identifier: GPL-3.0-or-later
-->

# The *.in* and *.txn* files

Our measurements use access logs located in this directory for their execution. The measurements that only count cache misses observed with different replacement policies (i.e. `hit_rate` and `cache_parameter_comparison`), need just a sequential list of the *keys* accessed. That is what the *.in* files are for. They list the logged keys line by line, and on the very first line, they state how many distinct keys appear in the list, let's call this number **N**. The keys in the logs are then simple integers from **0** to **N-1**, which is to make things simpler (for example because of our function that computes the Bélady optima) and reduce the file size compared to listing long hashes.

We also have measurements that simulate transaction execution rather than accesses to records alone. The transactions in our *.txn* files are described as so: each transaction starts with a capital **T**, followed by an **S** or **M** and a number, let's call it **t**, separated by spaces on a single line. The **T** just stands for *new transaction*, the **S** or **M** reveals if the transaction is **S**earch only, or if it **M**odifies some records. **t** is the time in seconds that the transaction really took to perform on the machine where the log was recorded (we don't actually use it in any of our measurements however, and the generated workloads that we will talk about later set all the **t**s to zero).

After this initial line follows a list of records that get accessed by this transaction, each access on a separate line, the lines in the form of, again **S** or **M**, and a key, separated by a space. If the line starts with an **M**, the record with the respective key gets modified by this access.

### The access files in this directory

`output.in` and `Carabas.in` come from access logs recorded on real LDAP databases in production. We also call these logs *Log 1* and *Log 2*, respectively. The original *Log 2* also contained transaction IDs, so it could have also been translated into `Carabas.txn`. It really comes from the very same access log as `Carabas.in`, but some keys may appear in a little different order, as the original log lists them in the order they were really accessed, and `Carabas.txn` lists all keys from a transaction together (i.e. the keys within a transaction will keep their order in the `.txn` file, but transactions are intermingled in the `.in` file).

Additionally, we have two *.txn* files with a *gen_* prefix. Those are artificially generated logs. `gen_sequential.txn` is made of transactions that each only access one record. The records are just 500 keys sequentially iterated over and over 500 times, about 1% of the accesses are marked as modifying. `gen_rand.txn` Is made of 4000 search-only transactions, each accessing five keys. The keys are chosen uniformly at random from a range of 3456 keys in total.
