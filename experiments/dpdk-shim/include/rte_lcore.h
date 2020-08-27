#pragma once

// Click depends on this transitive include
#include <rte_launch.h>


// There are no slaves
#define RTE_LCORE_FOREACH_SLAVE(i) if(0)


static inline unsigned rte_lcore_id(void)
{
	return 0;
}

static inline unsigned rte_socket_id(void)
{
	return 0;
}

static inline unsigned rte_lcore_count(void)
{
	return 1;
}
