# Reception paths

We inspect `ixgbe_recv_pkts` and assume nb_pkts == 1.

Paths:
- `staterr` doesn't have the DD flag set -> no packet
- `rte_mbuf_raw_alloc` fails -> error
- `rx_id` is `rxq->nb_rx_desc` (sets `rx_id` to 0; multiplies remaining paths by 2)
- `rx_id` is 3 modulo 4 (does some prefetching; multiplies remaining paths by 2)
- `pkt_flags` contains `PKT_RX_RSS_HASH`, OR contains `PKT_RX_FDIR`, OR nothing (sets some flags; multiplies remaining paths by 3)
- `nb_hold` is greater than `rxq->rx_free_thresh` (sets a register; multiples remaining paths by 2)

Total paths: 1 + 1 + 2 * 2 * 3 * 2 = 26, 25 of which have a packet.

# Transmission paths

We inspect `ixgbe_xmit_pkts_simple` and assume nb_pkts == 1.

Paths:
- `txq->nb_tx_free` is less than `txq->tx_free_thresh`
  - If yes, then call `ixgbe_tx_free_bufs`, whose paths are:
    - `status` doesn't have the DD flag set -> return
    - Loop from 0 to `txq->tx_rs_thresh`, with 3 paths in the body (two ifs, the first of which causes a 'continue' if the condition is satisfied), thus multiples remaining paths by `3 * txq->tx_rs_thresh`
    - `nb_free` is greater than 0 (if yes, calls `rte_mempool_put_bulk`, multiplies remaining paths by 2)
    - `txq->tx_next_dd` is greater than or equal `txq->nb_tx_desc` (sets `txq->tx_next_dd`, multiplies remaining paths by 2)
  - Overall, multiples remaining paths by `1 + (1 + (3 * `txq->tx_rs_thresh`) * 2 * 2)`
- `txq->tx_tail + 1` is greater than `txq->nb_tx_desc` (if yes, calls `ixgbe_tx_fill_hw_ring`, which has a single path given that nb_pkts = 1; multiplies remaining paths by 2)
- `txq->tx_tail` is greater than `txq->tx_next_rs`
  - If yes, checks if `txq->tx_next_rs` is greater than `txq->nb_tx_desc`
  - Overall, multiplies remaining paths by 3
- `txq->tx_tail` is greater than or equal to `txq->nb_tx_desc` (sets `txq->tx_tail` to 0; multiplies remaining paths by 2)

Total paths: (1 + (1 + (3 * `txq->tx_rs_thresh`) * 2 * 2)) * 2 * 3 * 2 = 24 + 144 * `txq->tx_rs_thresh`

DPDK supports transmission queues separately, so the number of paths for N queues is (number for 1 queue)^N.


# Total

To receive 1 packet and send it to O outputs, with a value N for tx_rs_thresh, there are `1 + 25 * (24 + 144N)^O` paths.
With a default tx_rs_thresh of 32, this is `1 + 25 * 4632^O`.
With a minimal tx_rs_thresh of 1, this is `1 + 25 * 148^O`.

