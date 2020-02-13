DPDK has 35 drivers.
Among those, 28 deal with hardware (real or virtualized), the rest are debugging utilities or indirections to Linux.
Among those, 25 refer to descriptors and 3 do not.
Among the 3 that do not, 2 are for FPGA-based NICs, and the other 1 is for proprietary virtualized hardware.

Not handling hardware:
- af_packet, virtual device using BSD sockets
- failsafe, virtual device that allows hotplugging
- kni, virtual device interfacing with the kernel
- null, virtual device that does nothing
- pcap, virtual device using libpcap
- ring, virtual device for in-memory loopback
- softnic, virtual device to build NIC pipelines in software

Not using descriptors:
- ark, which drives FPGA interconnects
- avp, virtualized hardware from Wind River Systems; appears to use some kind of FIFO... we'll conservatively say no
- szedata2, which drives FPGA-based programmable NICs, not zero-copy...
(vhost does not refer to descriptors but is a virtio implementation; it's an indirection to DPDK's libvhost)
