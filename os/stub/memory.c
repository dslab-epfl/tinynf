#include "os/memory.h"

#include "os/stub/symbol.h"

#include <assert.h>
#include <stdlib.h>


bool tn_mem_allocate(const size_t size, struct tn_memory_block* out_block)
{
	if (symbol_bool("mem_allocate")) {
		void* result = calloc(size, sizeof(uint8_t));
		assert(result != NULL);
		out_block->virt_addr = (uintptr_t) result;
		out_block->phys_addr = out_block->virt_addr; // We assume no memory virtualization
		return true;
	}

	return false;
}
