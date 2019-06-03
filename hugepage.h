#pragma once

#include <stddef.h>


// Allocates a hugepage of the given size, if possible.
// Returns NULL on error.
void* tn_hp_allocate(size_t size);
