#include "os/arch.h"


// TODO little endian system as well

uint32_t tn_cpu_to_le(const uint32_t val)
{
	return val;
}

uint32_t tn_le_to_cpu(const uint32_t val)
{
	return val;
}

void tn_read_barrier(void)
{
	// Nothing, we assume a strong memory model
}

void tn_write_barrier(void)
{
	// Nothing, we assume a strong memory model
}
