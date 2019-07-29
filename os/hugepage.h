#pragma once

#include <stdbool.h>
#include <stddef.h>
#include <stdint.h>

#include "os/cpu.h"


// Allocates a hugepage of the given size on the given node, or returns false.
bool tn_hp_allocate(size_t size, node_t node, uintptr_t* out_addr);
