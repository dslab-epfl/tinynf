# TinyNF experiments

This folder contains experiments used for the OSDI'20 TinyNF paper.

TODO explain in detail how this works


## Prerequisites

TODO describe benchmarking requirements/setup

The graphing and summarization scripts are intended to run on some kind of Linux-like system; we used Ubuntu 18.04, both on bare metal and within the Windows Subsystem for Linux.

You will need Python 3 with matplotlib, as well as the shell utilities `bc`, `cloc`, and `indent`, which are available under these names in most package repositories.


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
