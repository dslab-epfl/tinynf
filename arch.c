#include "arch.h"

#include <emmintrin.h>
#include <xmmintrin.h>


// x86 is little-endian
uint32_t tn_cpu_to_le(const uint32_t val)
{
	return val;
}
uint32_t tn_le_to_cpu(const uint32_t val)
{
	return val;
}

// TODO check if we really need barriers
void tn_read_barrier(void)
{
	// Load fence
	_mm_lfence();
}
void tn_write_barrier(void)
{
	// Store fence
	_mm_sfence();
}
