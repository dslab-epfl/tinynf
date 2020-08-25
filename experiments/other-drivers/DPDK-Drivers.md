This document classifies all DPDK NIC drivers according to whether they drive data plane hardware directly, as opposed to indirections or debugging utilities, and whether hardware they drive is based on a "descriptor" mechanism or not.

The list of drivers can be found at https://doc.dpdk.org/guides-20.02/nics/index.html (but some of the non-HW ones are not mentioned, such as "bonding")

For ease of reading, cells with 'no' are left empty


| ---------- | --- | ------ | ---------------------- |
| Name       | HW? | Descs? | Remarks                |
| ---------- | --- | ------ | ---------------------- |
| AF_PACKET  |     |        | UNIX sockets           |
| AF_XDP     |     |        | UNIX sockets           |
| ARK        | yes |        | FPGA-based NICs        |
| Atlantic   | yes | yes    |                        |
| AVP        | yes |        | Appears to use a FIFO  |
| AXGBE      | yes | yes    |                        |
| BNX2X      | yes | yes    |                        |
| BNXT       | yes | yes    |                        |
| Bonding    |     |        | Performs link bonding  |
| CXGBE      | yes | yes    |                        |
| DPAA       | yes |        | Not sure; assuming no  |
| DPAA2      | yes |        | Not sure; assuming no  |
| e1000/igb  | yes | yes    |                        |
| ENA        | yes | yes    |                        |
| ENETC      | yes | yes    |                        |
| ENIC       | yes | yes    |                        |
| Failsafe   |     |        | Supports hotplugging   |
| FM10K      | yes | yes    |                        |
| HINIC      | yes | yes    |                        |
| HNS3       | yes | yes    |                        |
| I40E       | yes | yes    |                        |
| IAVF       | yes | yes    |                        |
| ICE        | yes | yes    |                        |
| IONIC      | yes | yes    |                        |
| IPN3KE     |     |        | Control plane only     |
| IXGBE      | yes | yes    |                        |
| KNI        |     |        | Wrapper for rte_kni    |
| LiquidIO   | yes | yes    |                        |
| Memif      |     |        | Shared memory          |
| MLX4       | yes | yes    |                        |
| MLX5       | yes | yes    |                        |
| MVNETA     | yes | yes    |                        |
| MVPP2      | yes | yes    |                        |
| Netvsc     | yes |        | Not sure; assuming no  |
| NFB        | yes | yes    |                        |
| NFP        | yes | yes    |                        |
| Null       |     |        | Fake debug device      |
| OCTEON TX  | yes |        | Command-based queue    |
| OCTEON TX2 | yes |        | Command-based queue    |
| Pcap       |     |        | Wrapper for libpcap    |
| PFE        | yes | yes    |                        |
| QEDE       | yes | yes    |                        |
| Ring       |     |        | Wrapper for rte_ring   |
| SFC        | yes | yes    |                        |
| SoftNIC    |     |        | Software-based NIC     |
| SZEDATA2   | yes |        | FPGA-based NICs        |
| TAP        |     |        | Software devices       |
| ThunderX   | yes | yes    |                        |
| VDEVNETVSC | yes |        | Vdev version of Netvsc |
| vhost      |     |        | Wrapper for rte_vhost  |
| Virtio     | yes | yes    |                        |
| VMXNET3    | yes | yes    |                        |
