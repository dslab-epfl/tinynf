// Memory allocation/deallocation, and conversion of physical/virtual addresses
// https://en.wikipedia.org/wiki/Virtual_memory
// https://en.wikipedia.org/wiki/Direct_memory_access

#pragma once

#include <stdbool.h>
#include <stdint.h>


// Allocates a pinned, zero-initialized memory block of the given size, aligned to the size, or returns false.
// "Pinned" here means "the virtual-to-physical mapping will never change", not just that it will always be in memory.
// This allows the allocated memory's physical address to be given to a device for DMA.
bool tn_mem_allocate(uint64_t size, uintptr_t* out_addr);

// Frees the given memory block.
void tn_mem_free(uintptr_t addr);

// Maps the region of physical address memory defined by (address, size) into virtual memory, or returns false.
bool tn_mem_phys_to_virt(uintptr_t addr, uint64_t size, uintptr_t* out_virt_addr);

// Gets the physical address corresponding to the given virtual address, or returns false.
bool tn_mem_virt_to_phys(uintptr_t addr, uintptr_t* out_phys_addr);
