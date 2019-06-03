#include "device.h"
#include "hugepage.h"
#include "ixgbe_82599.h"
#include "pci.h"

#include <errno.h>
#include <stdlib.h>
#include <stdint.h>
#include <stdio.h>


struct tn_device {
	// Base address to access memory
	uint64_t base_addr;

	// Receive state
	uint64_t recv_base;
	uint64_t recv_head;
	uint64_t recv_tail;

	// Send state
	uint64_t send_base;
	uint64_t send_head;
	uint64_t send_tail;
};

// Known devices
struct tn_device tn_devices[2];

// Packet processing state
void** tn_packets;
size_t tn_packet_index;
uint16_t tn_packet_length;

// Initialization; returns 0 or error code.
int tn_dev_init(void)
{
	// Allocate a 2MB hugepage, enough for 128 16KB buffers
	const uintptr_t hugepage = tn_hp_allocate(128 * 16 * 1024);
	if (hugepage == (uintptr_t) -1) {
		return ENOMEM;
	}

	for (uint8_t n = 0; n < 2; n++) {
		// TODO hardcoded addrs...
		const uintptr_t dev_base_addr = tn_pci_get_device_address(0x85, 0x00, n, 512 * 1024); // length comes from manually checking
		if (dev_base_addr == (uintptr_t) -1) {
			return EINVAL;
		}

		tn_devices[n].base_addr = dev_base_addr;
		if (!ixgbe_device_init(dev_base_addr)) {
			return EINVAL;
		}
	}
	// Detect the NICs
	// read the 1st memory line in /resource; then any reg is just the memory addr + reg
	// Initialize the NICs
	// Create 1 RX, 1 TX queue on NICs
	// Start the NICs
	// Set NICs to promiscuous mode (or do that before start?)
	// Our custom setup:
	// - All RX_DD = 0
	// - RX_HD/TL = 0
	// - All TX_DD = 1
	// - TX_HD/TL = 0
	// - RX[n] = TX[n] = &hugepage[n * 16 * 1024]
	return 0;
}

void tn_dev_receive(void)
{
}

void tn_dev_transmit(void)
{
}

// TODO: tn_dev_drop(void);

uintptr_t tn_dev_get_packet(void)
{
	return 0;
}

uint16_t tn_dev_get_packet_length(void)
{
	return 0;
}
