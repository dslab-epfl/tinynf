#pragma once

typedef int (lcore_function_t)(void*);


static inline int rte_eal_remote_launch(lcore_function_t* f, void* arg, unsigned slave_id)
{
	(void) f;
	(void) arg;
	(void) slave_id;

	// Cannot be called since no slaves
	return -1;
}

static inline void rte_eal_mp_wait_lcore(void)
{
	// Nothing to do, no slaves to wait for
}
