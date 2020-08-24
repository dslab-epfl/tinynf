Note that TinyNF uses non-short-circuiting operators for the conditions specifically to reduce the number of paths.

# Reception paths

We inspect `tn_net_pipe_receive`.

- There may be a packet or not (bit 32 of `receive_metadata`)
  - If there isn't, we may decide to flush or not

Total: 3, 1 of which results in a packet


# Transmission paths

We inspect `tn_net_pipe_send`.

- We may need to flush
- We may need to move completed transmit descriptors to the receive queue
  - In this case there are 2^L-1 paths to compute the minimum, where L is the number of links (-1 because the first comparison always succeeds)

Total: `3 + 2^L - 1 = 2 + 2^L`


# Total

There are `2 + 1 * (2 + 2^L) = 4 + 2^L` paths total.
