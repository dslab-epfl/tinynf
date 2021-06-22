# Experiments

This folder contains experiments.

Subfolders:
- `perf`: performance across languages
- `code-metrics`: scripts on code metrics


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
- The shell utility  `cloc` available under that names in most package repositories
- The shell utility `cpupower`, available under names such as `linux-tools-common` (Ubuntu) or `kernel-tools` (Fedora) in package repositories
- Python 3 with the `matplotlib` package

Due to how long some of these scripts take, if you are running them via SSH, you may want to use an utility such as `byobu`, `tmux`, or `screen`,
allowing you to detach from the SSH session while keeping the scripts running.
