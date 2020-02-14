#pragma once

#include <stdbool.h>
#include <stdint.h>
#include <stdlib.h>

#include <rte_mempool.h>
// Click depends on this transitive include
#include <rte_prefetch.h>

#include <tn_dpdk.h>
#include "net/network.h"


#define rte_pktmbuf_mtod(m,t) ((t) (m)->buf_addr)

#define PKT_TX_TCP_SEG (1ull << 50)

#define RTE_MBUF_DEFAULT_BUF_SIZE 2048


struct rte_mbuf
{
	void* buf_addr;
	uint16_t data_off;
	uint32_t pkt_len;
	uint16_t data_len;
	uint16_t port;
	uint16_t refcnt;
// BEGIN: Not in DPDK
	struct tn_dpdk_device* tn_dpdk_device;
// END
};

#define rte_pktmbuf_pkt_len(m) ((m)->pkt_len)
#define rte_pktmbuf_data_len(m) ((m)->data_len)

struct rte_pktmbuf_pool_private
{
	// Nothing
};


static inline uint16_t rte_pktmbuf_headroom(const struct rte_mbuf* m)
{
	(void) m;

	return 0;
}

static inline struct rte_mbuf* rte_pktmbuf_alloc(struct rte_mempool* mp)
{
	(void) mp;

	// Click only needs this for the EnsureDPDKBuffer element, we don't use it...
	return NULL;
}

static inline void rte_pktmbuf_init(struct rte_mempool* mp, void* opaque_arg, void* m, unsigned i)
{
	(void) mp;
	(void) opaque_arg;
	(void) m;
	(void) i;

	// Nothing
}

static inline void rte_pktmbuf_pool_init(struct rte_mempool* mp, void* opaque_arg)
{
	(void) mp;
	(void) opaque_arg;

	// Nothing
}

static inline struct rte_mempool* rte_pktmbuf_pool_create(const char* name, unsigned n, unsigned cache_size, uint16_t priv_size, uint16_t data_room_size, int socket_id)
{
	(void) name;
	(void) n;
	(void) cache_size;
	(void) priv_size;
	(void) data_room_size;
	(void) socket_id;

	return (struct rte_mempool*) malloc(sizeof(struct rte_mempool));
}

static inline uint16_t rte_mbuf_refcnt_update(struct rte_mbuf* m, int16_t value)
{
	m->refcnt += value;
	return m->refcnt;
}

static inline void rte_mbuf_refcnt_set(struct rte_mbuf* m, uint16_t new_value)
{
	m->refcnt = new_value;
}

static inline void rte_pktmbuf_free(struct rte_mbuf* m)
{
	// Assume that if freeing, the mbuf is supposed to be dropped
	bool outputs[TN_DPDK_DEVICES_MAX_COUNT] = {0};
	tn_net_agent_transmit(m->tn_dpdk_device->agent, m->data_len, outputs);
	m->tn_dpdk_device->is_processing = false;
}

static inline uint16_t rte_pktmbuf_tailroom(const struct rte_mbuf* m)
{
	(void) m;

	return 0;
}
