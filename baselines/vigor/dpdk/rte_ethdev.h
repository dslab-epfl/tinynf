#pragma once

#include <stdbool.h>
#include <stddef.h>
#include <stdint.h>
#include <string.h>

#include <rte_ether.h>
#include <rte_mbuf.h>

#include <tn_dpdk.h>


struct rte_eth_rxmode
{
	uint16_t hw_strip_crc;
};

struct rte_eth_conf
{
	struct rte_eth_rxmode rxmode;
};


static inline uint16_t rte_eth_dev_count(void)
{
	return tn_dpdk_devices_count;
}

static inline int rte_eth_dev_socket_id(uint16_t port_id)
{
	return 0;
}

static inline int rte_eth_dev_configure(uint16_t port_id, uint16_t nb_rx_queue, uint16_t nb_tx_queue, const struct rte_eth_conf* eth_conf)
{
	if (nb_rx_queue != 1 || nb_tx_queue != 1) {
		return -1;
	}

	return 0;
}

static inline int rte_eth_rx_queue_setup(uint16_t port_id, uint16_t rx_queue_id, uint16_t nb_rx_desc, unsigned int socket_id, const struct rte_eth_rxconf* rx_conf, struct rte_mempool *mb_pool)
{
	return 0;
}

static inline int rte_eth_tx_queue_setup(uint16_t port_id, uint16_t tx_queue_id, uint16_t nb_tx_desc, unsigned int socket_id, const struct rte_eth_txconf* tx_conf)
{
	return 0;
}

static inline int rte_eth_dev_start(uint16_t port_id)
{
	return 0;
}

static inline void rte_eth_promiscuous_enable(uint16_t port_id)
{
	tn_net_device_set_promiscuous(tn_dpdk_devices[port_id].device);
	tn_dpdk_devices[port_id].is_promiscuous = true;
}

static inline int rte_eth_promiscuous_get(uint16_t port_id)
{
	return tn_dpdk_devices[port_id].is_promiscuous;
}

static inline uint16_t rte_eth_rx_burst(uint16_t port_id, uint16_t queue_id, struct rte_mbuf** rx_pkts, uint16_t nb_pkts)
{
	if (queue_id != 0) {
		return 0;
	}

	if (tn_dpdk_devices[port_id].is_processing) {
		return 0;
	}

	rx_pkts[0] = (struct rte_mbuf*) &(tn_dpdk_devices[port_id].buffer);

	if (tn_net_pipe_receive(tn_dpdk_devices[port_id].pipe, (uint8_t**) &(rx_pkts[0]->buf_addr), &(rx_pkts[0]->data_len))) {
		rx_pkts[0]->pkt_len = rx_pkts[0]->data_len;
		rx_pkts[0]->port = port_id;
		rx_pkts[0]->refcnt = 1;
		rx_pkts[0]->tn_dpdk_device = &(tn_dpdk_devices[port_id]);
		tn_dpdk_devices[port_id].is_processing = true;

#ifdef ASSUME_ONE_WAY
		memset(tn_dpdk_devices[port_id].current_send_list, 1, TN_DPDK_DEVICES_MAX_COUNT * sizeof(bool));
#else
		memset(tn_dpdk_devices[port_id].current_send_list, 0, TN_DPDK_DEVICES_MAX_COUNT * sizeof(bool));
#endif
		return 1;
	}

	return 0;
}

static inline uint16_t rte_eth_tx_burst(uint16_t port_id, uint16_t queue_id, struct rte_mbuf** tx_pkts, uint16_t nb_pkts)
{
	struct tn_dpdk_device* dev = tx_pkts[0]->tn_dpdk_device;

#ifdef ASSUME_ONE_WAY
	tn_net_pipe_send(dev->pipe, tx_pkts[0]->data_len, dev->current_send_list);
	dev->is_processing = false;
#else
	dev->current_send_list[port_id] = true;
	tx_pkts[0]->refcnt--;
	// Assume that if the ref count is more than 1 on sending, the intent is to send to another device as well
	if (tx_pkts[0]->refcnt == 0) {
		tn_net_pipe_send(dev->pipe, tx_pkts[0]->data_len, dev->current_send_list);
		dev->is_processing = false;
	}
#endif

	return 1;
}

static inline void rte_eth_macaddr_get(uint16_t port_id, struct ether_addr* mac_addr)
{
	// TODO make this actually work... for benchmarking we don't really care
	mac_addr->addr_bytes[0] = (uint8_t) port_id;
	mac_addr->addr_bytes[1] = 0;
	mac_addr->addr_bytes[2] = 0;
	mac_addr->addr_bytes[3] = 0;
	mac_addr->addr_bytes[4] = 0;
	mac_addr->addr_bytes[5] = 0;
}
