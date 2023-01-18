// Memory allocation, and conversion of physical/virtual addresses
// https://en.wikipedia.org/wiki/Virtual_memory
// https://en.wikipedia.org/wiki/Direct_memory_access

#pragma once

#include <stddef.h>
#include <stdint.h>

// Allocates a pinned, zero-initialized memory block of the given size, aligned to the size, or crashes.
// "Pinned" here means "the virtual-to-physical mapping will never change", not just that it will always be in memory.
// This allows the allocated memory's physical address to be given to a device for DMA.
// No freeing, it's a research prototype anyway, and that makes life easier
void* tn_mem_allocate(size_t size);

// Maps the region of physical address memory defined by (address, size) into virtual memory, or crashes.
void* tn_mem_phys_to_virt(uint64_t addr, size_t size); // addr is uint64_t, not uintptr_t, because PCI BARs are 64-bit

// Gets the physical address corresponding to the given virtual address, or crashes.
uintptr_t tn_mem_virt_to_phys(void* addr);
