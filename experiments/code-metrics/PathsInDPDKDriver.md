# Reception paths

We inspect `ixgbe_recv_pkts`, assuming:
- `nb_pkts` is 1
- `RTE_LIBRTE_IEEE1588` is not set
- `RTE_LIBRTE_SECURITY` is not set

Let `A_F` be the number of failure paths in `rte_mbuf_raw_alloc` and `A_S` the number of success paths.

`1` path: `staterr` doesn't have the DD flag set -> no packet
`A_F` paths: `staterr` has the DD flag set, but `rte_mbuf_raw_alloc` fails -> no packet
Multiply remaining paths by 2 due to the `rx_id == rxq->nb_rx_desc` check
Multiply remaining paths by 2 due to the `(rx_id & 0x3) == 0` check
Multiply remaining paths by 3 due to the `rx_status & ...` checks in `rx_desc_error_to_pkt_flags`, which includes a `&&`
Multiply remaining paths by 2 due to the `pkt_info & IXGBE_RXDADV_PKTTYPE_ETQF` check in `ixgbe_rxd_pkt_info_to_pkt_type`
Multiply remaining paths by 2 due to the `pkt_info & IXGBE_PACKET_TYPE_TUNNEL_BIT` check in `ixgbe_rxd_pkt_info_to_pkt_type`
Multiply remaining paths by 3 due to the `pkt_flags & PKT_RX_RSS_HASH` check, which includes an `else if`
Multiply remaining paths by 2 due to the `nb_hold > rxq->rx_free_thresh` check
`A_S` paths: happy path of receiving the packet.

Total paths:
- `A_F + 1` without a packet
- `2*2*3*2*2*3*2*A` = `288 * A_S` with a packet


# Transmission paths

We inspect `ixgbe_xmit_pkts_simple`, assuming:
- `nb_pkts` is 1
- All previously sent packets came from the same mbuf pool
- `RTE_IXGBE_TX_MAX_FREE_BUF_SZ` is infinitely large, i.e., freeing packets never needs to do so in multiple chunks

Let `T` be the configured `tx_rs_thresh`

Let `F_S` be the number of paths in `rte_pktmbuf_prefree_seg` that return a non-NULL value and `F_N` the number of paths that do.

Let `P` be the number of paths in `rte_mempool_put_bulk`

In `ixgbe_tx_free_bufs`, there are `(F_S + F_N)^T` paths in the "free buffers one at a time" loop,
of which all but `F_N^T` will trigger the `nb_free > 0` check; then the number of paths is doubled
due to the final overflow check. There is 1 additional path at the start if the DD flag is not set.
Thus `ixgbe_tx_free_bufs` has `1` failure path and `2 * (((F_S + F_N)^T - F_N^T) * P + F_N^T)` success paths.

`1` path: There are no available descriptors because `ixgbe_tx_free_bufs` failed.
Multiply remaining paths by 1 + the number of success paths in `ixgbe_tx_free_bufs`; the 1 is for the case that function needs not be called.
`1` path: Packet sent with wrap-around in the ring.
`1` path: Packet sent without wrap-around in the ring, without RS bit
`1` path: Packet sent without wrap-around in the ring, with RS bit, without updating `tx_next_rs`
`1` path: Packet sent without wrap-around in the ring, with RS bit, with updating `tx_next_rs`
Each of the "without wrap-around" path counts above is doubled due to wrap-around afterwards.

Total paths:
- `1` failing to transmit
- `7 + 14 * (((F_S + F_N)^T - F_N^T) * P + F_N^T)` successfully transmitting

DPDK supports transmission queues separately, so the number of paths for N queues is (number for 1 queue)^N.
