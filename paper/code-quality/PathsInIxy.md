# Reception paths

We inspect `ixgbe_rx_batch` and assume `num_bufs` is 1, `interrupts_enabled` is false, and the NIC cannot produce multi-buffer packets since it is not configured to do so by Ixy.

Paths:
- `status` does not have the `IXGBE_RXDADV_STAT_DD` flag set -> no packet
- `pkt_buf_alloc` succeeds -> OK, there is a packet
- `pkt_buf_alloc` fails -> error

Total paths: 3, 1 of which has a packet.

# Transmission paths

We inspect `ixgbe_tx_batch` and assume `num_bufs` == 1 and the size of the TX ring is the default of 512 and there are between 0 and 63 packets to clean (otherwise it gets messier but also extremely unlikely).

Paths in first loop:
- `cleanable` can be <0 or not (doubles the number of future paths)
- `cleanable` can be less than `TX_CLEAN_BATCH` (skips the rest of the loop)
- `cleanup_to >= queue->num_entries` can be true or not (doubles the number of future paths)
- `status & IXGBE_ADVTXD_STAT_DD` can be false (skips the rest of the loop)
- or it can be true, in which case there is a single path (despite the somewhat unusual loop shape designed to wrap-around the index on the ring)

Paths in second loop:
- `clean_index == next_index` can be true -> end, no packet sent
- or it can be false -> end, packet sent

Total paths:
- If 0 to 31 packets might be cleanable, then 2 (first loop) * 2 (second loop)
- If 32 to 63 packets might be cleanable but less than 31 are, then 4 (first loop) * 2 (second loop)
- If 32 to 63 packets are cleanable, then 4 (first loop first iter) * 2 (first loop second iter) * 2 (second loop)

for a grand total of 28, half of which fail to send a packet.


# Total

To receive 1 packet and send it to L links, there are 2 + 28^L paths, and a little under half of those do not end up sending a packet.

