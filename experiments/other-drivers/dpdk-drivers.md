This document classifies all DPDK NIC drivers according to whether they drive data plane hardware directly, as opposed to indirections or debugging utilities, and whether hardware they drive is based on a "descriptor" mechanism or not.

The list of drivers can be found at https://doc.dpdk.org/guides-20.02/nics/index.html, but some of the non-HW ones are not mentioned, such as "bonding".

For ease of scripting, the 'Name' column contains the exact names of the driver folders, in alphabetical order, and the document ends after the end of the table.

For ease of reading, cells with 'no' are left empty.


| ----------- | --- | ------ | ---------------------- |
| Name        | HW? | Descs? | Remarks                |
| ----------- | --- | ------ | ---------------------- |
| af_packet   |     |        | UNIX sockets           |
| af_xdp      |     |        | UNIX sockets           |
| ark         | yes |        | FPGA-based NICs        |
| atlantic    | yes | yes    |                        |
| avp         | yes |        | Appears to use a FIFO  |
| axgbe       | yes | yes    |                        |
| bnx2x       | yes | yes    |                        |
| bnxt        | yes | yes    |                        |
| bonding     |     |        | Performs link bonding  |
| cxgbe       | yes | yes    |                        |
| dpaa        | yes |        | Not sure; assuming no  |
| dpaa2       | yes |        | Not sure; assuming no  |
| e1000       | yes | yes    | Contains 'igb'         |
| ena         | yes | yes    |                        |
| enetc       | yes | yes    |                        |
| enic        | yes | yes    |                        |
| failsafe    |     |        | Supports hotplugging   |
| fm10k       | yes | yes    |                        |
| hinic       | yes | yes    |                        |
| hns3        | yes | yes    |                        |
| i40e        | yes | yes    |                        |
| iavf        | yes | yes    |                        |
| ice         | yes | yes    |                        |
| ionic       | yes | yes    |                        |
| ipn3ke      |     |        | Control plane only     |
| ixgbe       | yes | yes    |                        |
| kni         |     |        | Wrapper for rte_kni    |
| liquidio    | yes | yes    |                        |
| memif       |     |        | Shared memory          |
| mlx4        | yes | yes    |                        |
| mlx5        | yes | yes    |                        |
| mvneta      | yes | yes    |                        |
| mvpp2       | yes | yes    |                        |
| netvsc      | yes |        | Not sure; assuming no  |
| nfb         |     |        | Wrapper for libnfb     |
| nfp         | yes | yes    |                        |
| null        |     |        | Fake debug device      |
| octeontx    | yes |        | Command-based queue    |
| octeontx2   | yes |        | Command-based queue    |
| pcap        |     |        | Wrapper for libpcap    |
| pfe         | yes | yes    |                        |
| qede        | yes | yes    |                        |
| ring        |     |        | Wrapper for rte_ring   |
| sfc         | yes | yes    |                        |
| softnic     |     |        | Software-based NIC     |
| szedata2    | yes |        | FPGA-based NICs        |
| tap         |     |        | Software devices       |
| thunderx    | yes | yes    |                        |
| vdev_netvsc |     |        | Control plane only     |
| vhost       |     |        | Wrapper for rte_vhost  |
| virtio      | yes | yes    |                        |
| vmxnet3     | yes | yes    |                        |
