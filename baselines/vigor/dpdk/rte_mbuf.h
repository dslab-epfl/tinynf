#pragma once

#include <stdbool.h>
#include <stdint.h>
#include <stdlib.h>

#include <tn_dpdk.h>


#define rte_pktmbuf_mtod(m,t) ((t) (m)->buf_addr)

#define PKT_TX_TCP_SEG (1ull << 50)

#define RTE_MBUF_DEFAULT_BUF_SIZE 2048


struct rte_mbuf
{
	void* buf_addr;
	uint32_t pkt_len;
	uint16_t data_len;
	uint16_t port;
	uint16_t refcnt;
// BEGIN: Not in DPDK
	struct tn_dpdk_device* tn_dpdk_device;
// END
};

struct rte_mempool
{
	// Nothing
};

static inline struct rte_mempool* rte_pktmbuf_pool_create(const char *name, unsigned n, unsigned cache_size, uint16_t priv_size, uint16_t data_room_size, int socket_id)
{
	return malloc(sizeof(struct rte_mempool));
}

static inline void rte_mbuf_refcnt_set(struct rte_mbuf *m, uint16_t new_value)
{
	m->refcnt = new_value;
}

static inline void rte_pktmbuf_free(struct rte_mbuf* m)
{
	// Assume that if freeing the mbuf is dropping it
	bool send_list[TN_DPDK_DEVICES_MAX_COUNT] = {0};
	tn_net_pipe_send(m->tn_dpdk_device->pipe, m->data_len, send_list);
	m->tn_dpdk_device->is_processing = false;
}
