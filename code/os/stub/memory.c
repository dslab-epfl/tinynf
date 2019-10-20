#include "os/memory.h"

#include "os/stub/symbol.h"

#include <stdlib.h>


bool tn_mem_allocate(uint64_t size, uintptr_t* out_addr)
{
	if (symbol_bool("tn_mem_allocate_result")) {
		*out_addr = (uintptr_t) calloc(size, 1); // ASSUMPTION: calloc never fails
		return true;
	}

	return false;
}

void tn_mem_free(uintptr_t addr)
{
	free((void*) addr);
}

bool tn_mem_phys_to_virt(uintptr_t addr, uint64_t size, uintptr_t* virt_addr)
{
	???
}

bool tn_mem_virt_to_phys(uintptr_t addr, uintptr_t* phys_addr)
{
	???
}
