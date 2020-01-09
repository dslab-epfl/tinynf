# Reception paths

We inspect `tn_net_pipe_receive` assuming a fixed number of transmission queues has been configured.

Paths:

- If the scheduling algorithm decides to schedule the trackers
  - The first execution of the loop will always enter the 'if' body since `min_diff` starts at `-1` which is larger than any real difference can be; further executions may or may not enter the body.
  - Thus, the number of paths is `1 + 2^(#transmission_queues - 1)`.
- Bit 32 in `receive_metadata` may be set or not

Total: (1 + 2^(#transmission_queues - 1)) * 2 = 2 + 2^#transmission_queues;


# Transmission paths

We inspect `tn_net_pipe_send`.

There is only 1 path, since the loop's bounds are statically determined.
