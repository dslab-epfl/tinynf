# TinyNF experiments

This folder contains experiments used for the OSDI'20 TinyNF paper.

TODO explain in detail how this works


## Prerequisites

TODO describe benchmarking requirements/setup

The graphing and summarization scripts are intended to run on some kind of Linux-like system; we used Ubuntu 18.04, both on bare metal and within the Windows Subsystem for Linux.

You will need Python 3 with matplotlib, as well as the shell utilities `bc`, `cloc`, and `indent`, which are available under these names in most package repositories.


## Linux kernel parameters for performance benchmarks

Add the following to `GRUB_CMDLINE_LINUX_DEFAULT` in `/etc/default/grub`, assuming a 2-CPU machine with 8 physical cores each (adapt as needed):

- `nosmt`: Disable HyperThreading, to avoid contention among threads in benchmarks
- `intel_iommu=on iommu=pt`: Passthrough IOMMU, we don't need it
- `hugepages=4096`: preallocate 4K hugepages of the default 2MB size
- `isolcpus=6-15 nohz_full=6-15 rcu_nocbs=6-15`: Isolate the second CPU (8-15) entirely, and two cores on the first (6-7) for various experiments
- `nosoftlockup`: No backtraces for processes that appear to hang, such as NFs that run for a long time
- `processor.ignore_ppc=1`: Do not listen to the BIOS about CPU frequency limitations
- `pcie_aspm=off`: Force PCIe devices to run at full power
- `intel_idle.max_cstate=0 processor.max_cstate=0`: Disable CPU low power states
- `idle=poll cpuidle.off=1`: Force the CPU to spin instead of using waits for idling

Add `intel_pstate=disable` to be able to control the frequency (with e.g. cpupower). However, the max frequency might become lower... e.g. on our Xeon E5-2667v2 this caps the max freq at 3.3GHz instead of 3.6GHz...


## Reproducing figures and tables

Note that if you want to reproduce multiple figures, you only need to run the data-producing scripts like `./perf-endtoend/bench-all.py` once.

- **Figure 1**: In `other-drivers`, run `./graph-dpdk-drivers-loc.py`
- **Figures 2 to 5**: Illustration-only figures
- **Figure 6**: In `perf-endtoend`, run `./bench-all.py` then `./graph-tput-vs-lat.py 'Figure 6' 50 99 vigor-pol-dpdk vigor-pol-dpdk-batched tinynf-pol vigor-parallel-pol-dpdk vigor-parallel-pol-dpdk-batched tinynf-parallel-pol`
- **Figure 7**: In `perf-endtoend`, run `./bench-all.py` then `./graph-tput-vs-lat.py 'Figure 7' 99 99 vigor-pol-dpdk vigor-pol-dpdk-batched tinynf-pol vigor-parallel-pol-dpdk vigor-parallel-pol-dpdk-batched tinynf-parallel-pol`
- **Figure 8**: In `perf-endtoend`, run `./bench-all.py` then `./graph-tput-vs-lat.py 'Figure 8' 50 99 dpdk-nop-dpdk dpdk-nop-dpdk-batched ixy-nop ixy-nop-batched tinynf-nop`
- **Figure 9**: TODO NOP SLOW 50
- **Figure 10**: In `perf-endtoend`, run `./graph-lat-ccdf.py 'Figure 10' dpdk-nop-dpdk/latencies/0 dpdk-nop-dpdk-batched/latencies/0 ixy-nop/latencies/0 ixy-nop-batched/latencies/0 tinynf-nop/latencies/0`
- **Figure 11**: In `perf-endtoend`, run `./graph-lat-ccdf.py 'Figure 11' vigor-nat-dpdk/latencies-single/1000 vigor-nat-dpdk-batched/latencies-single/1000 vigor-nat/latencies-single/1000`

- **Table 1**: See [verification/ReadMe.md](verification/ReadMe.md)
- **Table 2**: In `code-metrics`, run `./tabulate-drivers-loc.sh`
- **Table 3**: In `perf-endtoend`, run `./bench-all.py` then `./tabulate-verified-nf-perf.sh`
- **Table 4**: In `perf-lowlevel`, run `./measure-stats.sh` then `./tabulate-stats.sh`
