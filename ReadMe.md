-- WEIRD: This MUST be of size 64, otherwise the card locks up quickly (even the heatup in the benchmarks doesn't finish)

noinline run / inlined agent/queues run

# TinyNF

This repository contains code originally associated with the paper ["A Simpler and Faster NIC Driver Model for Network Functions"](https://www.usenix.org/conference/osdi20/presentation/pirelli) (OSDI 2020).
It has been extended with more programming languages, a second driver model, and different scripts for experiments.


## Code

The code of the drivers is in the `ada`, `c`, `csharp`, and `rust` folders.
We refer to "agents" in the code for the restricted TinyNF model and "queues" for the flexible DPDK model.

All languages use a `Makefile.benchmarking` file to compile, which itself delegates to the language's native compiler / build system.
The following parameters are available:

- `TN_CC` (`c` only): The compiler, tested with GCC and Clang
- `TN_MODE`: The kind of driver:
  - `restricted` (default): The "restricted" model, which is the original TinyNF one
  - `const` (`ada`, `c`, and `rust` only): The restricted model with a constant number of devices, instead of detecting them at run-time
  - `flexible`: The "flexible" model, using queues similar to DPDK
  - `noextensions` (`csharp` only): The flexible model using only safe C#, without the language extensions
- `TN_CSHARP_AOT` (`csharp` only): Use ahead-of-time compilation for C# rather than the default just-in-time (any value given to the variable = AOT, undefined = JIT)

Note that despite needing extensions, the Rust driver does not support `TN_MODE=safe` because, due to Rust's ownership model,
unsafe code _must_ be used in the hot loop for volatile reads and writes, whereas C# allows these reads and writes in safe code.


## Experiments

The benchmarking scripts for NFs, which are independent of the rest, are in `benchmarking/`.

The experiments presented in the paper, including replication instructions, are in `experiments/`.
We've also provided the actual data collected on our hardware in `experiments/results_example`; you can rename the folder to `results` and run the scripts to plot it as per the instructions.
