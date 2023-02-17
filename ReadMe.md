# TinyNF

This repository contains the "TinyNF" driver codebase.

It was originally associated with the paper ["A Simpler and Faster NIC Driver Model for Network Functions"](https://www.usenix.org/conference/osdi20/presentation/pirelli) (OSDI 2020).
You can still find that version of the code, and the experimental scripts to reproduce that paper, in the `osdi20` branch.

It was extended for the paper ["Safe low-level code without overhead is practical"](https://conf.researchr.org/details/icse-2023/icse-2023-technical-track/18/Safe-low-level-code-without-overhead-is-practical) (ICSE 2023).
The repo contains more programming languages, a second driver model, and scripts to reproduce the new paper's experiments.


## Code

The code of the drivers is in the `ada`, `c`, `csharp`, and `rust` folders.
We refer to "agents" in the code for the restricted TinyNF model and "queues" for the flexible DPDK model.

You can `make` each driver to compile it, and `make format` it to auto-format the code.

To run a driver with a minimal app, either manually run the binary produced by compilation,
or `make -f Makefile.benchmarking`, but see the `benchmarking/` folder for required environment variables.

The following environment variables are supported by each driver's Makefile:
- `TN_MODE`: The kind of driver:
  - `restricted` (default): The "restricted" model, which is the original TinyNF one
  - `const` (`ada`, `c`, and `rust` only): The restricted model with a constant number of devices, instead of detecting them at run-time
  - `flexible`: The "flexible" model, using queues similar to DPDK
  - `noextensions` (`csharp` only): The flexible model using only safe C#, without the language extensions
- `TN_CSHARP_AOT` (`csharp` only): Use ahead-of-time compilation for C# rather than the default just-in-time (any value given to the variable = AOT, undefined = JIT)

Note that despite needing extensions, the Rust driver does not support `TN_MODE=safe` because, due to Rust's ownership model,
unsafe code _must_ be used in the hot loop for volatile reads and writes, whereas C# allows these reads and writes in safe code.

All languages force inlining of the driver methods into a forced-not-inlined "run" method to ensure a fair comparison and to make extracting the hot loop code easy.

All languages use a 64-bit integer to represent packet lengths, even though the card only supports 16 bits, because not doing so often causes the card to lock up in non-C implementations.
(Yes, this sounds extremely weird, but that's what empirical evidence says...)


## Dependencies

To compile each language, you will need `make`, as well as a compiler:
- `ada`: `gnat`, though any other compiler might work
- `c`: `gcc` or `clang`, though any other C11 compiler should work
- `csharp`: `dotnet`, version 7 or above
- `rust`: `rustc`, a version that supports Rust 2021, and the `cargo` build system

If you don't want to install those on your machine, we provide a `Dockerfile`, just run `docker build -t tinynf . ; docker run -it tinynf` (you might need `sudo` for Docker).
This file is also useful if you want to know how to install the dependencies on any Ubuntu machine.
(The Dockerfile does not include `clang-format`, which is used for `make format` in `c`, you'll have to install that manually if you want to auto-format the C code)

Known good versions: GCC 12.1.0; Clang 14.0.0; Rustc and Cargo 1.67.1; .NET 7.0.200; GNAT 12.1.0; on Ubuntu 22.04.


## Experiments

The benchmarking scripts for network functions, which are independent of the rest, are in `benchmarking/`.

The experiments presented in the paper, including replication instructions, are in `experiments/`.
We've also provided the actual data collected on our hardware in `experiments/results_example`;
you can rename the folder to `results` and run the scripts to plot it as per the instructions.
