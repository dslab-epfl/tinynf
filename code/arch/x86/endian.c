#include "arch/endian.h"


// x86 is little-endian
uint32_t tn_cpu_to_le(const uint32_t val)
{
	return val;
}
uint32_t tn_le_to_cpu(const uint32_t val)
{
	return val;
}
