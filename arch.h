#pragma once

#include <stdint.h>

uint32_t tn_cpu_to_le(uint32_t const val);
uint32_t tn_le_to_cpu(uint32_t const val);

void tn_read_barrier(void);
void tn_write_barrier(void);
