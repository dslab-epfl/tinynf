#pragma once

#include <stdint.h>


uint64_t tn_numa_get_current_node(void);

uint64_t tn_numa_get_addr_node(uintptr_t addr);
