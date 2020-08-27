# Verifying the TinyNF driver with Vigor

The Vigor repository supports verifying TinyNF:

- Clone the `vigor-nf/vigor` repo on GitHub
- Run its `setup.sh` script
- Within a Vigor NF folder from that repo, such as `vignat`, assuming the TinyNF repo is at `~/tinynf`, run `TINYNF_DIR=~/tinynf RTE_SDK=~/tinynf/experiments/dpdk-shim RTE_TARGET=. make symbex-withdpdk validate`

You can compare to verifying with DPDK by running `make symbex-withdpdk validate` without overriding any variables (this will use the `RTE_SDK`/`RTE_TARGET` set by Vigor's setup script)
