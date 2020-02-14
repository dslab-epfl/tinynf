// Non-Uniform Memory Accesses (NUMA) abstraction.
// https://en.wikipedia.org/wiki/Non-uniform_memory_access
// The goal is not to actually deal with non-uniform accesses, but instead to fail if the program's allocated resources are not all on the same node.

#pragma once

#include <stdbool.h>
#include <stdint.h>


bool tn_numa_is_current_node(uint64_t node);

bool tn_numa_get_addr_node(uintptr_t addr, uint64_t* out_node);
