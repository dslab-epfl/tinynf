#include "arch/barrier.h"

#include <emmintrin.h>
#include <xmmintrin.h>


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
