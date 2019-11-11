#pragma once

#include <stdlib.h>


struct rte_mempool
{
	// Nothing
};

typedef void(rte_mempool_ctor_t) (struct rte_mempool*, void*);
typedef void(rte_mempool_obj_cb_t) (struct rte_mempool* mp, void* opaque, void* obj, unsigned obj_idx);


static inline struct rte_mempool* rte_mempool_create(
	const char* name, unsigned n, unsigned elt_size, unsigned cache_size, unsigned private_data_size,
	rte_mempool_ctor_t* mp_init, void* mp_init_arg, rte_mempool_obj_cb_t* obj_init, void* obj_init_arg,
	int socket_id, unsigned flags)
{
	(void) name;
	(void) n;
	(void) elt_size;
	(void) cache_size;
	(void) private_data_size;
	(void) mp_init;
	(void) mp_init_arg;
	(void) obj_init;
	(void) obj_init_arg;
	(void) socket_id;
	(void) flags;

	return (struct rte_mempool*) malloc(sizeof(struct rte_mempool));
}

static inline unsigned int rte_mempool_avail_count(const struct rte_mempool* mp)
{
	(void) mp;

	// Doesn't matter - needed by Click element DPDKInfo to compile
	return 0;
}
