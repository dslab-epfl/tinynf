# Network function benchmarking scripts

This folder contains scripts to benchmark network functions, or "NFs" for short, using two machines.

The first machine is the "Device Under Test", or "DUT" for short, which runs the network function being benchmarked.
The second machine is the "tester" machine, which runs the MoonGen packet generator and some benchmarking logic.

## How to use

- Get ahold of two machines, directly connected by at least two network cables.
  - Copy `config.template` to `config` and set the values as needed in your setup.
  - Configure the machines' kernels with whatever performance-maximizing options you need, e.g. `isolcpus`
  - Create an SSH key on the DUT and add it to the authorized keys of the tester, to avoid entering your password during script execution
  - Ensure that your user can run "sudo" without a password, since this is necessary to run NFs
  - Ensure that you are starting these scripts from the DUT

- Create a `Makefile.benchmarking` file in your NF's folder, with the following targets:
  - `build` to build the NF, e.g. compile it
  - `run` to run the NF, with the PCI addresses of the network cards to use passed as `$(TN_ARGS)`
  - `print-nf-name` to print the name of the NF process, e.g. `@echo my-nf`
  - If your NF is based on DPDK, create an empty target `is-dpdk`
  - If your NF needs something done after it starts, such as sleeping for a while because it is slow to start, put this in a target `init`

- Double-check your NF's configuration:
  - If your NF tracks packet flows, it should be configured with a capacity of 65536 flows (only 60000 will be used)
  - Your NF should be built in "release" mode, i.e. no extraneous logging, all compiler optimizations, etc.

- Run `./bench.sh ../your/nf/folder bench-type layer`, where:
  - `bench-type` is one of `standard` (2-way throughput + latency) or `standard-single` (1-way throughput + latency)
  - `layer` is `2`, `3` or `4` depending the network layer your NF operates at, so that throughput is measured with different packet flows
  - You can add the following before `bench-type`:
    - `--latencyload X` where `X` is either a number of MBits/s to use as the only latency measurement or `-1` to disable latency measurement entirely.
      (By default, the script measures latency from 0 to max throughput in 1 Gb/s increments)
    - `--acceptableloss X` where `X` is the fraction of loss that is acceptable in the throughput benchmark, `0.003` by default.
    - `--flows X` where `X` is the number of different flows the packets should belong to
    - `--reverseheatup` for `standard-single` to also heat up in the other direction, useful for some NFs like a load balancer that gets heartbeat packets from backends
