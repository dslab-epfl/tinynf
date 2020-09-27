# TinyNF experiments

This folder contains experiments used for the OSDI'20 TinyNF paper.

Subfolders:
- `alternatives`: patches for TinyNF that make it worse but are interesting
- `baselines`: baseline NFs for various experiments
- `code-metrics`: scripts and data on code metrics such as number of lines of code
- `dpdk-shim`: a shim layer allowing DPDK NFs to use TinyNF, assuming they only need the TinyNF model
- `other-drivers`: scripts and data on other drivers, such as DPDK network drivers
- `perf-endtoend`: scripts for measuring "end to end" performance
- `perf-lowlevel`: scripts for measuring low-level performance metrics such as cache misses
- `verification`: experiments related to formally verifying NFs running on TinyNF


## Prerequisites

Most of the experiments are about performance, measured with benchmarks.

To run these benchmarks, you need two machines running Linux:
- A "device under test" machine with two Intel 82599ES NICs on the same NUMA node, from which you will run the experiment scripts
- A "tester" machine connected to the other one by two 10G Ethernet cables

As a first step, go to the `benchmarking` folder at the root of this repository, and follow the first list in the instructions ("Get ahold of two machines...").

Assuming a 2-CPU machine whose second CPU has cores 8 to 15, we recommend the following Linux kernel parameters for the two machines (add to `GRUB_CMDLINE_LINUX_DEFAULT` in `/etc/default/grub`):
- `nosmt`: Disable HyperThreading, to avoid contention among threads in benchmarks
- `intel_iommu=off`: Disable the IOMMU, we don't need it
- `hugepages=4096`: preallocate 4K hugepages of the default 2MB size
- `isolcpus=8-15 nohz_full=8-15 rcu_nocbs=8-15`: Isolate the second CPU entirely
- `nosoftlockup`: No backtraces for processes that appear to hang, such as NFs that run for a long time
- `processor.ignore_ppc=1`: Do not listen to the BIOS about CPU frequency limitations
- `pcie_aspm=off`: Force PCIe devices to run at full power
- `intel_idle.max_cstate=0 processor.max_cstate=0`: Disable CPU low power states
- `idle=poll cpuidle.off=1`: Force the CPU to spin instead of using waits for idling
- `intel_pstate=disable`: Allow Linux to set the CPU frequency via `cpupower` instead of letting the Intel driver choose

You will also need the following software:
- GCC 10 (any version should work, but that is the one we used for the paper)
- The build tools Make and CMake, available under these names in most package repositories
- The development versions of libC and libNUMA, for instance available in the `libc-dev` and `libnuma-dev` packages in Ubuntu
- The shell utilities `bc`, `cloc`, and `indent`, available under these names in most package repositories
- The shell utility `cpupower`, available under names such as `linux-tools-common` (Ubuntu) or `kernel-tools` (Fedora) in package repositories
- Python 3 with the `matplotlib` package

Due to how long some of these scripts take, if you are running them via SSH, you may want to use an utility such as `byobu`, `tmux`, or `screen`,
allowing you to detach from the SSH session while keeping the scripts running.


## Reproducing figures and tables

All figures and tables in the paper can be reproduced by running scripts, except those for illustration purposes only, and Figure 9 which requires some more setup.


### Figure 1

In `other-drivers`, run `./graph-dpdk-drivers-loc.py 'Figure 1'`, which should take <2min.

To understand which drivers were excluded from the figure and why, read `other-drivers/dpdk-drivers.md`.


### Figures 2 to 5

These figures are for illustration purposes, they do not contain data.
They are based on the source code of DPDK and TinyNF; the paper explains them.


### Figures 6 to 11 and Table 3

In `perf-endtoend`, run `./bench-all.py`, which should take under 5h.

Then run the following, which should take a minute:

```
# Figures
./graph-tput-vs-lat.py 'Figure 6' 50 99 vigor-pol-dpdk vigor-pol-dpdk-batched tinynf-pol \
                                        vigor-parallel-pol-dpdk vigor-parallel-pol-dpdk-batched tinynf-parallel-pol
./graph-tput-vs-lat.py 'Figure 7' 99 99 vigor-pol-dpdk vigor-pol-dpdk-batched tinynf-pol \
                                        vigor-parallel-pol-dpdk vigor-parallel-pol-dpdk-batched tinynf-parallel-pol
./graph-lat-ccdf.py 'Figure 8' vigor-pol-dpdk/latencies/1000 vigor-pol-dpdk-batched/latencies/1000 \
                               tinynf-pol/latencies/1000 vigor-parallel-pol-dpdk/latencies/1000 \
                               vigor-parallel-pol-dpdk-batched/latencies/1000 tinynf-parallel-pol/latencies/1000
./graph-tput-vs-lat.py 'Figure 9' 50 99 dpdk-nop-dpdk dpdk-nop-dpdk-batched ixy-nop ixy-nop-batched tinynf-nop
./graph-tput-vs-lat.py 'Figure 10' 50 99 dpdk-slow-nop-dpdk dpdk-slow-nop-dpdk-batched tinynf-slow-nop
./graph-lat-ccdf.py 'Figure 11' dpdk-nop-dpdk/latencies/0 dpdk-nop-dpdk-batched/latencies/0 \
                                ixy-nop/latencies/0 ixy-nop-batched/latencies/0 tinynf-nop/latencies/0
# Table 3
./tabulate-verified-nf-perf.sh
```

Please note that the latency of functions when the background load is close to their breaking point in terms of throughput can vary across runs, especially DPDK without batching.
This is also the case for the detailed latency graphs close to the 99.99% mark, when NIC timestamping stops being accurate as reported by [Primorac et al.](https://dl.acm.org/doi/10.1145/3098583.3098590).


### Table 1

The easiest way to do this, though it incurs some overhead, is with Docker.

Run `docker run -it --entrypoint bash dslabepfl/vigor` (you might need `sudo`) to start a container with the Vigor Docker image, then in the container run:

```
# Get the right version of Vigor
rm -rf vigor
git clone https://github.com/vigor-nf/vigor
git -C vigor checkout 01deebad8013231e19aa8b2386b1c063d4a739ce
# Update the PATH with the Vigor toolchain
. ~/paths.sh
# Get TinyNF
git clone https://github.com/dslab-epfl/tinynf
# Get the verification times with TinyNF
cd tinynf/experiments/verification
./measure-verification-times.sh ~/vigor
```

Alternatively, you can run these steps on your own machine, though you'll have to run Vigor's `setup.sh` script after the `checkout` command above, which will build its toolchain and take a few hours.

These instructions were for the TinyNF verification times.
The times with Vigor are merely replications of the Vigor SOSP'19 paper, whose artifact was judged reproducible already; if you'd like to reproduce these anyway,
you'll need a machine with at least 100 GB RAM and preferably dozens of CPU cores. Run `./measure-verification-times.sh ~/vigor original` as the last command in the script above.


### Table 2

For the numbers of functions and lines of code: in `code-metrics`, run `./tabulate-drivers-loc.sh`, which should take <10min.

For the numbers of paths: read the `code-metrics/PathsIn...` files.


### Table 4

In `perf-lowlevel`, run the following commands, which should take under 8h total and use 80GB of disk space:

```
# Measuring data
./measure-stats.sh
./measure-stats.sh write
./measure-stats.sh lookup
./measure-stats.sh pol
# Processing & displaying it
# (if you skip one of the commands above, its corresponding rows will not be displayed)
./tabulate-stats.sh
```
