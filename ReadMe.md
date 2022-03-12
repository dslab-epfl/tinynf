TODO: rename TN_MODE to use strings rather than ints and error if unknown in each makefile, then each readme states which ones it supports

# Changes from the original C code

- Removed low-level functions, inlined them in the high-level one
- Removed fixed-size inline buffers in the agent struct, allocating them separately instead (required simplifying the external API for agent init as well)
- Moved to a packet processor definition that has an array of lengths instead of both returning a length and setting the output bools
- Moved to using 1 GB hugepages
- Moved to `static inline` functions for endianness so they can be directly inlined without LTO, as the C# code does


# TinyNF

This repository contains the code associated with the paper ["A Simpler and Faster NIC Driver Model for Network Functions"](https://www.usenix.org/conference/osdi20/presentation/pirelli) presented at OSDI 2020.
It was awarded the "Artifact Available", "Artifact Functional", and "Results Reproduced" badges after artifact evaluation.

The code of the "TinyNF" driver is in `code/`.

The benchmarking scripts for NFs, which are independent of TinyNF, are in `benchmarking/`.

The experiments presented in the paper, including replication instructions, are in `experiments/`.
