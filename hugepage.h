#pragma once

#include <stddef.h>
#include <stdint.h>


// Returns the address of a newly-allocated hugepage of the given size, or (uintptr_t) -1 on error.
uintptr_t tn_hp_allocate(size_t size);
