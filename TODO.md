- Use C17
- clang?
- enable as many warnings as possible

- currently the packet size doesn't make much sense, we don't support jumbo packets so we only need to support the MTU of 1518...

Optimizations:
- DCA (direct cache access)
- NUMA awareness of memory/NICs
- IOMMU to have "phys"==virtual
