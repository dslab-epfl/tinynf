Hi there! Thanks for taking a look!
The code is commented and the experiments are automated, but we didn't have time to properly document the build system & refactor some quirks.
Please use the experiment scripts as a base to understand which environment variables to give to each Makefile.

We've also provided the actual data collected on our hardware in `experiments/results_example`; you can rename the folder to `results` and run the scripts to plot it as per the instructions.

The code of the drivers is in the `ada`, `c`, `csharp`, and `rust` folders.
We refer to "agents" in the code for the restricted TinyNF model and "queues" for the flexible DPDK model.

The benchmarking scripts for NFs, which are independent of the rest, are in `benchmarking/`.

The experiments presented in the paper, including replication instructions, are in `experiments/`.
