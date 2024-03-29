# Experiments

The ICSE 2023 paper's central claim is that it is possible to write safe code with no run-time overhead compared to C.
This is implemented as two driver models in C, Ada, C#, and Rust.

_By definition, you are unlikely to get the exact same results as the paper since it depends on your exact compiler versions and your CPU.
However, the relative claims should hold._


## Theory (minutes)

You will need `cloc` in addition to the compilers mentioned in the top-level readme; or use the provided Dockerfile.

Run `cd code-metrics ; ./tabulate-metrics.sh` which will generate an `assembly/` directory containing the assembly code for all hot loops in all drivers.
This can be manually checked for a lack of compiler-inserted bounds checks.
That script also outputs **Table 2** from the paper, and takes less than a minute.

## Practice (hours)

For the **figures**, with the exception of Figure 2 which is a simplified form of `rust/src/lifed.rs`, you need a proper testbed.
Check out the prerequisites below, `cd perf`, then `./bench.sh`, which will take a few hours.
Then `./plot.sh` assuming you have Python with Matplotlib; run `. setup-virtualenv-graphing.sh` on Ubuntu to create a virtualenv with it if needed.

To run the benchmarks, you need two machines running Linux:
- A "device under test" machine with two Intel 82599ES NICs on the same NUMA node, from which you will run the experiment scripts
- A "tester" machine connected to the other one by two 10G Ethernet cables

As a first step, go to the `benchmarking` folder at the root of this repository, and follow the first list in the instructions ("Get ahold of two machines...").

Assuming a 2-CPU machine whose second CPU has cores 8 to 15, we recommend the following Linux kernel parameters for the two machines (add to `GRUB_CMDLINE_LINUX_DEFAULT` in `/etc/default/grub`):
- `nosmt`: Disable HyperThreading, to avoid contention among threads in benchmarks
- `intel_iommu=off`: Disable the IOMMU, we don't need it
- `default_hugepagesz=1G hugepagesz=1G hugepages=8`: preallocate 8 hugepages of 1GB each
- `isolcpus=8-15 nohz_full=8-15 rcu_nocbs=8-15`: Isolate the second CPU entirely
- `nosoftlockup`: No backtraces for processes that appear to hang, such as NFs that run for a long time
- `processor.ignore_ppc=1`: Do not listen to the BIOS about CPU frequency limitations
- `pcie_aspm=off`: Force PCIe devices to run at full power
- `intel_idle.max_cstate=0 processor.max_cstate=0`: Disable CPU low power states
- `idle=poll cpuidle.off=1`: Force the CPU to spin instead of using waits for idling
- `intel_pstate=disable`: Allow Linux to set the CPU frequency via `cpupower` instead of letting the Intel driver choose

You will also need the following software on the device under test machine, in addition to the dependencies mentioned in the top-level readme:
- The library `libtbb2`, available under that name in most package repositories
- The shell utility `cpupower`, available under names such as `linux-tools-generic` (Ubuntu) in package repositories

Due to how long some of these scripts take, if you are running them via SSH, you may want to use an utility such as `byobu`, `tmux`, or `screen`,
allowing you to detach from the SSH session while keeping the scripts running.
