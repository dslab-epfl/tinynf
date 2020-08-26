#pragma once

#include <stdint.h>


struct rte_pci_addr
{
	uint32_t domain;
	uint8_t bus;
	uint8_t devid;
	uint8_t function;
};

struct rte_pci_device
{
	struct rte_pci_addr addr;
};
