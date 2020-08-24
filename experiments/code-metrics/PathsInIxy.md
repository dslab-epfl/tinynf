# Reception paths

We inspect `ixgbe_rx_batch`, assuming:
- `num_bufs` is 1
- `interrupts_enabled` is false
- the NIC cannot produce multi-buffer packets since it is not configured to do so by Ixy

Let `A_S` be the number of success paths in `pkt_buf_alloc` and `A_F` the number of failure paths.

`1` path: `status` does not have the DD flag set -> no packet
`A_F` paths: `pkt_buf_alloc` fails -> no packet
`A_S` paths: `pkt_buf_alloc` succeeded (thus `rx_index != last_rx_index` is always true)

Total paths:
- `1 + A_F` without a packet
- `A_S` with a packet


# Transmission paths

We inspect `ixgbe_tx_batch`, assuming:
- `num_bufs` is 1
- there is at most one full "batch" of packets to clean (otherwise it gets messier but also extremely unlikely)

Let `B` be the value of `TX_CLEAN_BATCH`.

Let `P` be the number of paths in `pkt_buf_free`. 

Multiply remaining paths by 2 due to the `cleanable < 0` check
`1` path: there is nothing to clean and `clean_index == next_index` -> no transmission
`1` path: there is nothing to clean and `clean_index != next_index` -> transmission
Multiply remaining paths by 2 due to the `cleanup_to >= queue->num_entries` check
`1` path: there is something to clean but DD is not set and `clean_index == next_index` -> no transmission
`1` path: there is something to clean but DD is not set and `clean_index != next_index` -> transmission
Multiply remaining paths by `P^B` due to the cleaning loop
Multiply remaining paths by 2 due to the `cleanable < 0` check on the next iteration
`1` path: transmission succeeds (packets have been cleaned so `clean_index != next_index)`

Total paths:
- `6` failing to transmit
- `6 + 2*P^B` successfully transmitting

Ixy supports transmission queues separately, so the number of paths for N queues is (number for 1 queue)^N.
