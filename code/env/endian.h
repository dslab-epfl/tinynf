// Endianness abstraction
// https://en.wikipedia.org/wiki/Endianness

#pragma once

#include <stdint.h>


// Converts the given unsigned 16-bit value from the CPU's native endianness to litle endian.
uint16_t tn_cpu_to_le16(uint16_t val);

// Converts the given unsigned 16-bit value from little endian to the CPU's native endianness.
uint16_t tn_le_to_cpu16(uint16_t val);


// Converts the given unsigned 32-bit value from the CPU's native endianness to litle endian.
uint32_t tn_cpu_to_le32(uint32_t val);

// Converts the given unsigned 32-bit value from little endian to the CPU's native endianness.
uint32_t tn_le_to_cpu32(uint32_t val);


// Converts the given unsigned 64-bit value from the CPU's native endianness to litle endian.
uint64_t tn_cpu_to_le64(uint64_t val);

// Converts the given unsigned 64-bit value from little endian to the CPU's native endianness.
uint64_t tn_le_to_cpu64(uint64_t val);
