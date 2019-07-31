#pragma once

#include <stdbool.h>
#include <stddef.h>
#include <stdint.h>


struct tn_memory_block {
	uintptr_t virt_addr;
	uintptr_t phys_addr;
};


// Allocates a pinned memory block of the given size, or returns false.
bool tn_mem_allocate(size_t size, struct tn_memory_block* out_block);

// Frees the given memory block.
void tn_mem_free(struct tn_memory_block block);
