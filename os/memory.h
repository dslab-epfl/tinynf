#pragma once

#include <stdbool.h>
#include <stdint.h>


struct tn_memory_block {
	uintptr_t virt_addr;
	uintptr_t phys_addr;
};


// Allocates a pinned, zero-initialized memory block of the given size, aligned to the size, or returns false.
bool tn_mem_allocate(uint64_t size, struct tn_memory_block* out_block);

// Frees the given memory block.
// TODO this is unused
void tn_mem_free(struct tn_memory_block block);

// Maps the region of physical address memory defined by (address, size) into memory usable by the program, or returns false.
bool tn_mem_phys_to_virt(uintptr_t addr, uint64_t size, uintptr_t* virt_addr);

// Gets the physical address corresponding to the given virtual address, or returns false.
bool tn_mem_virt_to_phys(uintptr_t addr, uintptr_t* phys_addr);
