#pragma once

static inline void rte_prefetch0(const volatile void* p)
{
	(void) p;

	// Nothing
}
