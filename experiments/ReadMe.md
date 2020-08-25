# TinyNF experiments

This folder contains experiments used for the OSDI'20 TinyNF paper.


## Prerequisites

You will need Python 3 with matplotlib, as well as the shell utilities `bc`, `cloc`, and `indent`, which are available under these names in most package repositories.


## Reproducing figures and tables

- **Figure 1**: In `other-drivers`, run `./graph-dpdk-drivers-loc.py`
- **Figures 2 to 5**: Illustration-only figures
- **Figure 6**: POL 50
- **Figure 7**: POL 99
- **Figure 8**: NOP 50
- **Figure 9**: NOP SLOW 50
- **Figure 10**: LAT NOP 0
- **Figure 11**: LAT NAT 1000 SINGLE

- **Table 1**: TODO
- **Table 2**: In `code-metrics`, run `./tabulate-drivers-loc.sh`
- **Table 3**: In `perf-endtoend`, run `./bench-all.py` then `./tabulate-verified-nf-perf.sh`
- **Table 4**: In `perf-lowlevel`, run `./measure-stats.sh` then `./tabulate-stats.sh`
