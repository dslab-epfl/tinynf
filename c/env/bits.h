#pragma once

#include <stdint.h>

// Bit N, 0-based
#define BIT(n) (1u << (n))

// Bit N, 0-based, as a long
#define BITL(n) (1ull << (n))

// Bits N to M, both inclusive
#define BITS(start, end) (((end) == 31 ? 0u : (0xFFFFFFFFu << ((end) + 1))) ^ (0xFFFFFFFFu << (start)))

// https://en.wikipedia.org/wiki/Find_first_set
static inline uint32_t find_first_set(uint32_t value)
{
	if (value == 0) {
		return 0;
	}
	uint32_t n = 0;
	while (((value >> n) & 1) == 0) {
		n = n + 1;
	}
	return n;
}
