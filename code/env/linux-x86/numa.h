// Non-Uniform Memory Accesses (NUMA) abstraction, internal to the linux environment abstraction.
// https://en.wikipedia.org/wiki/Non-uniform_memory_access
// The goal is not to actually deal with non-uniform accesses, but instead to fail if the program's allocated resources are not all on the same node.

#pragma once

#include "env/pci.h"

#include <stdbool.h>
#include <stdint.h>


bool tn_numa_is_current_node(uint64_t node);

bool tn_numa_get_addr_node(void* addr, uint64_t* out_node);

bool tn_numa_get_device_node(struct tn_pci_address address, uint64_t* out_node);
