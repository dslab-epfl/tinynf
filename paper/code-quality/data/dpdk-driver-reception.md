We start from ixgbe_recv_pkts, which is the simplest form of reception; the driver includes alternatives such as vectorized functions.

```
ixgbe_recv_pkts
- rx_desc_status_to_pkt_flags
- rx_desc_error_to_pkt_flags
- ixgbe_rxd_pkt_info_to_pkt_flags
- ixgbe_rxd_pkt_info_to_pkt_type
```
