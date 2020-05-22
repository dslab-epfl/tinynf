#pragma once

#include <stdbool.h>
#include <stddef.h>
#include <stdint.h>
#include <string.h>

#include <rte_ether.h>
#include <rte_mbuf.h>
#include <rte_pci.h>

#include <tn_dpdk.h>
#include "net/network.h"


#define ETH_RSS_IP 0
#define ETH_RSS_UDP 0
#define ETH_RSS_TCP 0

#define ETH_TXQ_FLAGS_NOMULTSEGS 0
#define ETH_TXQ_FLAGS_NOOFFLOADS 0

#define ETH_LINK_FULL_DUPLEX 1

#define RTE_ETH_XSTATS_NAME_SIZE 64


enum rte_eth_rx_mq_mode
{
	ETH_MQ_RX_RSS
};

struct rte_eth_rxmode
{
	enum rte_eth_rx_mq_mode mq_mode;
	uint16_t hw_strip_crc;
};

struct rte_eth_rss_conf
{
	uint8_t* rss_key;
	uint64_t rss_hf;
};

struct rte_eth_conf
{
	struct rte_eth_rxmode rxmode;
	struct {
		struct rte_eth_rss_conf rss_conf;
	} rx_adv_conf;
};

struct rte_eth_thresh
{
	uint8_t pthresh;
	uint8_t hthresh;
	uint8_t wthresh;
};

struct rte_eth_rxconf
{
	struct rte_eth_thresh rx_thresh;
};

struct rte_eth_txconf
{
	struct rte_eth_thresh tx_thresh;
	uint32_t txq_flags;
};

struct rte_eth_desc_lim
{
	uint16_t nb_min;
	uint16_t nb_max;
};

struct rte_eth_dev_info
{
	struct rte_pci_device* pci_dev;
	const char* driver_name;
	uint32_t max_rx_queues;
	uint32_t max_tx_queues;
	struct rte_eth_rxconf default_rxconf;
	struct rte_eth_txconf default_txconf;
	struct rte_eth_desc_lim rx_desc_lim;
	struct rte_eth_desc_lim tx_desc_lim;
	uint16_t nb_rx_queues;
	uint16_t nb_tx_queues;
};

struct rte_eth_link
{
	uint32_t link_speed;
	uint16_t link_duplex;
	uint16_t link_autoneg;
	uint16_t link_status;
};

struct rte_eth_stats
{
	uint64_t ipackets;
	uint64_t opackets;
	uint64_t ibytes;
	uint64_t obytes;
	uint64_t imissed;
	uint64_t ierrors;
	uint64_t oerrors;
};

struct rte_eth_xstat_name
{
	char name[RTE_ETH_XSTATS_NAME_SIZE];
};

struct rte_eth_xstat
{
	uint64_t id;
	uint64_t value;
};


static inline uint16_t rte_eth_dev_count(void)
{
	return tn_dpdk_devices_count;
}

static inline int rte_eth_dev_socket_id(uint16_t port_id)
{
	(void) port_id;

	return 0;
}

static inline int rte_eth_dev_configure(uint16_t port_id, uint16_t nb_rx_queue, uint16_t nb_tx_queue, const struct rte_eth_conf* eth_conf)
{
	(void) port_id;
	(void) eth_conf;

	if (nb_rx_queue != 1 || nb_tx_queue != 1) {
		return -1;
	}

	return 0;
}

static inline int rte_eth_rx_queue_setup(uint16_t port_id, uint16_t rx_queue_id, uint16_t nb_rx_desc, unsigned int socket_id, const struct rte_eth_rxconf* rx_conf, struct rte_mempool *mb_pool)
{
	(void) port_id;
	(void) rx_queue_id;
	(void) nb_rx_desc;
	(void) socket_id;
	(void) rx_conf;
	(void) mb_pool;

	return 0;
}

static inline int rte_eth_tx_queue_setup(uint16_t port_id, uint16_t tx_queue_id, uint16_t nb_tx_desc, unsigned int socket_id, const struct rte_eth_txconf* tx_conf)
{
	(void) port_id;
	(void) tx_queue_id;
	(void) nb_tx_desc;
	(void) socket_id;
	(void) tx_conf;

	return 0;
}

static inline int rte_eth_dev_start(uint16_t port_id)
{
	(void) port_id;

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
	(void) nb_pkts;

	if (queue_id != 0) {
		return 0;
	}

	if (tn_dpdk_devices[port_id].is_processing) {
		return 0;
	}

	rx_pkts[0] = (struct rte_mbuf*) &(tn_dpdk_devices[port_id].buffer);

	if (tn_net_agent_receive(tn_dpdk_devices[port_id].agent, (uint8_t**) &(rx_pkts[0]->buf_addr), &(rx_pkts[0]->data_len))) {
		rx_pkts[0]->pkt_len = rx_pkts[0]->data_len;
		rx_pkts[0]->port = port_id;
		rx_pkts[0]->refcnt = 1;
		rx_pkts[0]->tn_dpdk_device = &(tn_dpdk_devices[port_id]);
		tn_dpdk_devices[port_id].is_processing = true;

#ifdef ASSUME_ONE_WAY
		memset(tn_dpdk_devices[port_id].current_outputs, 1, TN_DPDK_DEVICES_MAX_COUNT * sizeof(bool));
#else
		memset(tn_dpdk_devices[port_id].current_outputs, 0, TN_DPDK_DEVICES_MAX_COUNT * sizeof(bool));
#endif
		return 1;
	}

	return 0;
}

static inline uint16_t rte_eth_tx_burst(uint16_t port_id, uint16_t queue_id, struct rte_mbuf** tx_pkts, uint16_t nb_pkts)
{
	(void) nb_pkts;
	(void) queue_id;

	struct tn_dpdk_device* dev = tx_pkts[0]->tn_dpdk_device;

#ifdef ASSUME_ONE_WAY
	tn_net_agent_transmit(dev->agent, tx_pkts[0]->data_len, dev->current_outputs);
	dev->is_processing = false;
#else
	dev->current_outputs[port_id] = true;
	tx_pkts[0]->refcnt--;
	// Assume that if the ref count is more than 1 on transmit, the intent is to transmit to another device as well
	if (tx_pkts[0]->refcnt == 0) {
		tn_net_agent_transmit(dev->agent, tx_pkts[0]->data_len, dev->current_outputs);
		dev->is_processing = false;
	}
#endif

	return 1;
}

static inline void rte_eth_macaddr_get(uint16_t port_id, struct ether_addr* mac_addr)
{
	// for benchmarking we don't really care
	mac_addr->addr_bytes[0] = (uint8_t) port_id;
	mac_addr->addr_bytes[1] = 0;
	mac_addr->addr_bytes[2] = 0;
	mac_addr->addr_bytes[3] = 0;
	mac_addr->addr_bytes[4] = 0;
	mac_addr->addr_bytes[5] = 0;
}

static inline void rte_eth_dev_info_get(uint16_t port_id, struct rte_eth_dev_info* dev_info)
{
	(void) port_id;

	dev_info->driver_name = "Fake driver";
	dev_info->max_rx_queues = 1;
	dev_info->max_tx_queues = 1;
	dev_info->rx_desc_lim.nb_max = (uint16_t) -1;
	dev_info->tx_desc_lim.nb_max = (uint16_t) -1;
	dev_info->nb_rx_queues = 1;
	dev_info->nb_tx_queues = 1;

	// Nothing for the pci_dev; Click only needs this in case one uses PCI device addresses with a DPDKDevice, but we don't...
}

static inline int rte_eth_dev_default_mac_addr_set(uint16_t port, struct ether_addr* mac_addr)
{
	(void) port;
	(void) mac_addr;

	// Click needs it to compile
	return -1;
}

static inline int rte_eth_dev_mac_addr_add(uint16_t port, struct ether_addr* mac_addr, uint32_t pool)
{
	(void) port;
	(void) mac_addr;
	(void) pool;

	// Click needs it to compile
	return -1;
}

static inline int rte_eth_dev_set_mtu(uint16_t port_id, uint16_t mtu)
{
	(void) port_id;
	(void) mtu;

	// Click needs it to compile
	return -1;
}

static inline void rte_eth_link_get_nowait(uint16_t port_id, struct rte_eth_link* link)
{
	(void) port_id;

	link->link_speed = 10 * 1000 * 1000; // 10G... whatever...
	link->link_status = 1;
	link->link_duplex = 1;
	link->link_autoneg = 1;
}

static inline int rte_eth_stats_get(uint16_t port_id, struct rte_eth_stats* stats)
{
	(void) port_id;
	(void) stats;

	// No stats available
	return 0;
}

static inline int rte_eth_xstats_get_names(uint16_t port_id, struct rte_eth_xstat_name* xstats_names, unsigned int size)
{
	(void) port_id;
	(void) xstats_names;
	(void) size;

	// If xstats_names is NULL, the function returns the required number of elements
	// Otherwise, it returns the number of entries filled
	return 0;
}

static inline int rte_eth_xstats_get(uint16_t port_id, struct rte_eth_xstat* xstats, unsigned int n)
{
	(void) port_id;
	(void) xstats;
	(void) n;

	// Should never be called since get_names returns 0
	return -1;
}
