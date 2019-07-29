#pragma once

#include <stdbool.h>
#include <stdint.h>

#include "os/cpu.h"


// Gets the physical address backing the given address, or returns false.
bool tn_mem_get_phys_addr(uintptr_t addr, uintptr_t* out_phys_addr);

// Gets the NUMA node containing the memory pointed to by the given address, or returns false.
bool tn_mem_get_node(uintptr_t addr, node_t* out_node);
