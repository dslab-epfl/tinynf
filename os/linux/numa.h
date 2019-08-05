#pragma once

#include <stdbool.h>
#include <stdint.h>


bool tn_numa_is_current_node(uint64_t node);

bool tn_numa_get_addr_node(uintptr_t addr, uint64_t* out_node);
