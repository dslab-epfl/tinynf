#include "arch/barrier.h"

//#include <emmintrin.h>
//#include <xmmintrin.h>
#include <x86intrin.h>

// TODO check if we really need barriers
void tn_barrier_read(void)
{
	// Load fence
	_mm_lfence();
}

void tn_barrier_write(void)
{
	// Store fence
	_mm_sfence();
}
