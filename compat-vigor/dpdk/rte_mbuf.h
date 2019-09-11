#pragma once

#include <stdint.h>


#define rte_pktmbuf_mtod(m,t) ((t) (m)->buf_addr)

#define PKT_TX_TCP_SEG (1ull << 50)

// No need to define all fields
struct rte_mbuf
{
	void* buf_addr;
	uint32_t pkt_len;
	uint16_t port;
};

static inline void rte_pktmbuf_free(struct rte_mbuf* m)
{
	// Not actually used
}
