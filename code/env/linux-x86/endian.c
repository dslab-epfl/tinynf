// The x86 architecture is little-endian, so the implementations here are trivial

#include "env/endian.h"


uint16_t tn_cpu_to_le16(const uint16_t val)
{
	return val;
}

uint16_t tn_le_to_cpu16(const uint16_t val)
{
	return val;
}


uint32_t tn_cpu_to_le32(const uint32_t val)
{
	return val;
}

uint32_t tn_le_to_cpu32(const uint32_t val)
{
	return val;
}


uint64_t tn_cpu_to_le64(const uint64_t val)
{
	return val;
}

uint64_t tn_le_to_cpu64(const uint64_t val)
{
	return val;
}
