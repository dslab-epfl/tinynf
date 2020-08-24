DPDK has 52 network drivers.
Among those, 44 deal with hardware (real or virtualized), the rest are debugging utilities or indirections to Linux.
Among those, 40 refer to descriptors and 4 do not.
Among the 4 that do not, 3 are for FPGA-based NICs, and the other 1 is for proprietary virtualized hardware.

Not handling hardware:
- af_packet, virtual device using BSD sockets
- af_xdp, virtual device using AF_XDP sockets
- failsafe, virtual device that allows hotplugging
- kni, virtual device interfacing with the kernel
- null, virtual device that does nothing
- pcap, virtual device using libpcap
- ring, virtual device for in-memory loopback
- softnic, virtual device to build NIC pipelines in software

Not using descriptors:
- ark, which drives FPGA interconnects
- avp, virtualized hardware from Wind River Systems; appears to use some kind of FIFO... we'll conservatively say no
- ipn3ke, an FPGA control plane for the Intel *710 family
- szedata2, which drives FPGA-based programmable NICs, not zero-copy...
(vhost does not refer to descriptors but is a virtio implementation; it's an indirection to DPDK's libvhost)

TODO: make a table with all drivers or something (and look at "baseband" drivers, and any other kind...)
