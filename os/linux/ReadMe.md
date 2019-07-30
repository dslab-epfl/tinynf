Linux implementation of the OS abstraction layer.

This implementation is NUMA-aware, but hides the existence of NUMA from above layers: if resource-allocating operations cannot allocate a resource on the same node as the CPU, they fail.
