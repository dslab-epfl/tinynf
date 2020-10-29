# SR-IOV prototype

This is a prototype of an SR-IOV driver. It is far more experimental than the rest of this repository.
It also twists the API a bit by implementing different inputs/outputs as different VFs on a single PF.

**Important**: To run on your machine, check out `82599-vf/ixgbe-vf.c`'s `get_pcie_extended_address` and replace the constant there following the instructions.

To benchmark, go to the benchmarking directory and e.g. `./bench.sh ../experiments/sriov/ --flows 16 standard 2`.

You can also add `TN_CFLAGS=-DTN_SRIOV_NOP` to use a no-op instead of a policer.
