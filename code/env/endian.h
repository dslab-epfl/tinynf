#pragma once

#include <stdint.h>


// Converts the given value from the CPU's native endianness to litle endian.
uint32_t tn_cpu_to_le(uint32_t val);

// Converts the given value from little endian to the CPU's native endianness.
uint32_t tn_le_to_cpu(uint32_t val);
