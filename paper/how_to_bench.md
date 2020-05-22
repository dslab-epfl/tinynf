# Tips for benchmarking

- Make sure you are not in debug mode; you can even use TN_DEBUG=0 to disable all logging, though this makes debugging issues harder.
- Use link-time optimizations by adding `-flto` to both TN_CFLAGS and TN_LDFLAGS; this improves performance a lot!
- Use as few agent outputs as your NF needs; for instance, VigNAT only needs 2 agents that each receive from one device and send to the other,
  so they only need one output per agent since by design VigNAT cannot send a packet back to the device that it received it from.
  To do this, set `IXGBE_AGENT_OUTPUTS_MAX` to a number, and only configure one output per agent (this is done for the baselines by setting the `ASSUME_ONEWAY` define)
