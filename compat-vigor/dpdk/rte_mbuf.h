#pragma once

#define rte_pktmbuf_mtod(m,t) ((t) (m)->buf_addr)

// No need to define all fields
struct rte_mbuf
{
	void* buf_addr;
	uint32_t pkt_len;
	uint16_t port;
};

// Not actually used, just needed for linking
static void rte_pktmbuf_free(struct rte_mbuf* m)
{
	// Nothing
}
