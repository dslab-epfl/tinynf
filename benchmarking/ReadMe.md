# Network function benchmarking scripts

This folder contains scripts to benchmark network functions, or "NFs" for short, using two machines.

The first machine is the "Device Under Test", or "DUT" for short, which runs the network function being benchmarked.
The second machine is the "tester" machine, which runs the MoonGen packet generator and some benchmarking logic.

## How to use

- Get ahold of two machines, directly connected by at least two network cables.
  - Copy `config.template` to `config` and set the values as needed in your setup.
  - Configure the machines' kernels with whatever performance-maximizing options you need, e.g. `isolcpus`
  - Create an SSH key on the DUT and add it to the authorized keys of the tester, to avoid entering your password during script execution
  - Ensure that you are starting these scripts from the DUT

- Create a `Makefile.benchmarking` file in your NF's folder, with the following targets:
  - `build` to build the NF, e.g. compile it
  - `run` to run the NF, with the PCI addresses of the network cards to use passed as `$(TN_ARGS)`
  - `print-nf-name` to print the name of the NF process, e.g. `@echo my-nf`
  - If your NF is based on DPDK, create an empty target `is-dpdk`

- Double-check your NF's configuration:
  - If your NF tracks packet flows, it should be configured with a capacity of 65536 flows (only 60000 will be used)
  - Your NF should be built in "release" mode, i.e. no extraneous logging, all compiler optimizations, etc.

- Run `./bench.sh ../your/nf/folder bench-type layer`, where:
  - `bench-type` is one of `standard` (2-way throughput + latency) or `standard-single` (1-way throughput + latency)
  - `layer` is `2`, `3` or `4` depending the network layer your NF operates at, so that throughput is measured with different packet flows
