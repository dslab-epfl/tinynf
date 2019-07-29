#pragma once

#include <stdbool.h>
#include <stddef.h>
#include <stdint.h>

#include "os/cpu.h"


struct tn_memory_block {
	uintptr_t virt_addr;
	uintptr_t phys_addr;
};


// Allocates a pinned memory block of the given size on the given NUMA node, or returns false.
bool tn_mem_allocate(size_t size, node_t node, struct tn_memory_block* out_block);
