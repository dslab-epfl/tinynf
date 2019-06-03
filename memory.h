#pragma once

#include <stdint.h>

const uintptr_t TN_MEM_BAD_PHYSICAL_ADDRESS = (uintptr_t) -1;

// Returns the physical address backing the given address, or TN_MEM_BAD_PHYSICAL_ADDRESS in case of an error.
uintptr_t tn_mem_virtual_to_physical_address(void* address);
