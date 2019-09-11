#pragma once

#include <rte_ether.h>
#include <rte_mbuf.h>

// HACK: Global variable here set in main.c
extern uint16_t devices_count;

uint16_t rte_eth_dev_count(void)
{
	return devices_count;
}

static inline uint16_t rte_eth_rx_burst(uint16_t port_id, uint16_t queue_id, struct rte_mbuf** rx_pkts, uint16_t nb_pkts)
{
	// Not actually used
}

static inline uint16_t rte_eth_tx_burst(uint16_t port_id, uint16_t queue_id, struct rte_mbuf** tx_pkts, uint16_t nb_pkts)
{
	// Not actually used
}

void rte_eth_macaddr_get(uint16_t port_id, struct ether_addr* mac_addr)
{
	// TODO make this actually work... for benchmarking we don't really care
	mac_addr->addr_bytes[0] = (uint8_t) port_id;
	mac_addr->addr_bytes[1] = 0;
	mac_addr->addr_bytes[2] = 0;
	mac_addr->addr_bytes[3] = 0;
	mac_addr->addr_bytes[4] = 0;
	mac_addr->addr_bytes[5] = 0;
}
