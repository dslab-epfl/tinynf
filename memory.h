#pragma once

#include <stdint.h>

// Returns the physical address backing the given address, or (uintptr_t) -1 in case of an error.
uintptr_t tn_mem_virtual_to_physical_address(uintptr_t address);
