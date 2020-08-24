TinyNF handles multiple transmission queues at the same time; let `O` be the number of outputs.

# Reception paths

We inspect `tn_net_agent_receive`.

`1` path: there is no packet and the agent flushes
`1` path: there is no packet and the agent does not flush
`1` path: there is a packet

Total:
- `2` paths without a packet
- `1` path with a packet


# Transmission paths

We inspect `tn_net_agent_transmit`.

Multiply remaining paths by 2 due to the `flush_counter` check
`1` path where `rs_bit != 0`
`2^(O-1)` paths where `rs_bit == 0`, since the first `diff <= min_diff` check always succeeds

Total:
- `2 + 2^O` paths successfully transmitting
