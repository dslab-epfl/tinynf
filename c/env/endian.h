// Endianness abstraction
// https://en.wikipedia.org/wiki/Endianness

#pragma once

#include <stdint.h>

#if __BYTE_ORDER__ == __ORDER_LITTLE_ENDIAN__
static inline uint16_t tn_cpu_to_le16(const uint16_t val)
{
	return val;
}

static inline uint16_t tn_le_to_cpu16(const uint16_t val)
{
	return val;
}


static inline uint32_t tn_cpu_to_le32(const uint32_t val)
{
	return val;
}

static inline uint32_t tn_le_to_cpu32(const uint32_t val)
{
	return val;
}


static inline uint64_t tn_cpu_to_le64(const uint64_t val)
{
	return val;
}

static inline uint64_t tn_le_to_cpu64(const uint64_t val)
{
	return val;
}
#else
#error too lazy to implement this sorry
#endif
