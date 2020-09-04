# TinyNF code

Structure:
- `env` contains the environment abstraction layer, with an implementaton for `linux-x86`
- `util` contains utilities for logging, parsing arguments, and microbenchmarking.
- `net` contains the network drivers, with an implementation for the Intel `82599` card
- `tinynf.c` is an example application that forwards packets.

Build with `make`; tested with GCC and clang.

Read the comments at the top of the `Makefile` for additional configuration; you likely want to add `-flto` to the compiler flags.
