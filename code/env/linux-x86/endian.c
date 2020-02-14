// The x86 architecture is little-endian, so the implementations here are trivial

#include "env/endian.h"


uint32_t tn_cpu_to_le(const uint32_t val)
{
	return val;
}
uint32_t tn_le_to_cpu(const uint32_t val)
{
	return val;
}
