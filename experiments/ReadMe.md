# TinyNF experiments

This folder contains experiments used for the OSDI'20 TinyNF paper.

Subfolders:
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

As a first step, go to the `benchmarking` folder at the root of this repository, copy `config.template` to `config` and change its values according to your setup.

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
- The shell utilities `bc`, `cloc`, `indent` and `ministat`, available under these names in most package repositories
- The shell utility `cpupower`, available under names such as `linux-tools-common` (Ubuntu) or `kernel-tools` (Fedora) in package repositories
- Python 3 with the `matplotlib` package


## Reproducing figures and tables

All figures and tables in the paper can be reproduced by running scripts, except those for illustration purposes only, and Figure 9 which requires some more setup.


### Figure 1

In `other-drivers`, run `./graph-dpdk-drivers-loc.py 'Figure 1'`, which should take <2min.


### Figures 2 to 5

These figures are for illustration purposes, they do not contain data.
They are based on the source code of DPDK and TinyNF; the paper explains them.


### Figures 6, 7, 8, 10, 11 and Table 3

Run `sudo cpupower -c 8-15 frequency-set -f 99GHz`, where `8-15` are all of the cores on the physical CPU on which you will run NFs.
That is, not only the cores configured in the `benchmarking/config` file, but also the other cores on the same physical CPU.
`99GHz` simply tells `cpupower` to use the highest possible frequency. You can double-check this by looking at `/proc/cpuinfo`.

In `perf-endtoend`, run `./bench-all.py`, which should take ~4h.

Then run the following, which should take a minute:

```
# Figures
./graph-tput-vs-lat.py 'Figure 6' 50 99 vigor-pol-dpdk vigor-pol-dpdk-batched tinynf-pol vigor-parallel-pol-dpdk vigor-parallel-pol-dpdk-batched tinynf-parallel-pol
./graph-tput-vs-lat.py 'Figure 7' 99 99 vigor-pol-dpdk vigor-pol-dpdk-batched tinynf-pol vigor-parallel-pol-dpdk vigor-parallel-pol-dpdk-batched tinynf-parallel-pol
./graph-tput-vs-lat.py 'Figure 8' 50 99 dpdk-nop-dpdk dpdk-nop-dpdk-batched ixy-nop ixy-nop-batched tinynf-nop
./graph-lat-ccdf.py 'Figure 10' dpdk-nop-dpdk/latencies/0 dpdk-nop-dpdk-batched/latencies/0 ixy-nop/latencies/0 ixy-nop-batched/latencies/0 tinynf-nop/latencies/0
./graph-lat-ccdf.py 'Figure 11' vigor-nat-dpdk/latencies-single/1000 vigor-nat-dpdk-batched/latencies-single/1000 vigor-nat/latencies-single/1000
# Table 3
./tabulate-verified-nf-perf.sh
```


### Figure 9

Run `sudo cpupower -c 8-15 frequency-set -f 2GHz`, where `8-15` are all of the cores on the physical CPU on which you will run NFs (same remark as above).
Note that due to how CPU frequencies work, the actual frequency may be a bit above or below the desired frequency; you can check this by looking at `/proc/cpuinfo`.

Remember to set the frequency back to normal afterwards (using the `99GHz` trick mentioned above), otherwise the results of other experiments will be off.

In `perf-endtoend`, run `./bench-all.py slow-nops`, which should take <1h.

Then run `./graph-tput-vs-lat.py 'Figure 9' 50 99 results-slow/dpdk-nop-dpdk results-slow/dpdk-nop-dpdk-batched results-slow/tinynf-nop`


### Table 1

First, clone the `vigor-nf/vigor` repo on GitHub and run its `setup.sh` script as indicated in its readme.

To get the times with TinyNF, in `verification`, run `./measure-verification-times.sh ~/vigor`, changing the location of the Vigor directory to match your setup.

If you want to get the times with Vigor, in `verification`, run `./measure-verification-times.sh ~/vigor original`, again changing the location to match.
However, this will take multiple hours even on a server with dozens of cores, and those numbers have already been reproduced as part of Vigor's artifact evaluation.

Alternatively, you can use the Vigor Docker image: run `sudo docker run -it --entrypoint bash dslabepfl/vigor` to start a container,
then in the container run `rm -rf vigor ; git clone https://github.com/vigor-nf/vigor` to get the latest Vigor and `. ~/paths.sh` to update your PATH with the toolchain,
then clone the TinyNF repo and proceed as indicated above. This might have some overhead compared to running it directly, though.


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
