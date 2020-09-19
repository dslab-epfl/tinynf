# DPDK shim layer

This code implements a shim layer on top of TinyNF that emulates basic DPDK APIs.

All emulated APIs are defined as inline functions in headers; there is only one C file for a few global variables.

This layer only works if the network function calls DPDK in a way that is compatible with the TinyNF model, namely by receiving and transmitting one packet at a time without any reordering.

Pass `-DASSUME_ONE_WAY` in `TN_CFLAGS` to go through a faster code path if you have 2 devices and your network function never sends packets back to the device they came from.
