# Balanced BST in Rust
This repository contains Rust implementations of 4 variations of the weight-balanced tree (a.k.a BB[α] tree) that I made just to practice Rust.
In all variations, instead of using tree rotations, partial rebuilds were used to rebalance a tree.
Since partial rebuilds cost O(n), a single insert/delete operation may cost O(n). However, in an amortized sense, insert/delete operations cost O(logn).

Moreover, rebuild operations were parallelized in the later variations. In this way, we can utilize threads for higher performance, unlike tree rotation based weight-balanced trees.

- **bbst.rs** : An implementation of the weight-balanced tree that uses partial rebuilds.
- **bbst_locked.rs** : A coarse grained lock added to **bbst.rs**.
- **bbst_fast_rebuild.rs** : **bbst_locked.rs** with rebuilds parallelized.
- **bbst_fast_rebuild2.rs** : **bbst_locked.rs** with rebuilds parallelized, but unlike **bbst_fast_rebuild.rs**, we use message passing between threads.
