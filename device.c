#include "device.h"

// TODO most of this file should be in ixgbe

#include "os/hugepage.h"
#include "os/pci.h"
//#include "arch.h"
// TODO remove above once we include stuff in ixgbe instead

#include "ixgbe_82599.h"

// TODO none of those should be here
#include <errno.h>
#include <stdlib.h>
#include <stdint.h>
#include <stdio.h>

struct tn_device {
	// Base address to access memory
	uintptr_t base_addr;

	// Receive state
	uint64_t* recv_base;
	uint16_t recv_head;
	uint16_t recv_tail;

	// Send state
	uint16_t send_head;
	uint16_t send_tail;
	uint64_t* send_base;
};

// Known devices
struct tn_device tn_devices[2];

// Packet processing state
uintptr_t tn_packets;
uint16_t tn_packet_index;
uint16_t tn_packet_length;

// Initialization; returns 0 or error code.
int tn_dev_init(void)
{
	// Allocate a 2MB hugepage, enough for 128 16KB buffers, or 256 8 KB buffers
	const uintptr_t packet_buffers = tn_hp_allocate(2 * 1024 * 1024);
	if (packet_buffers == (uintptr_t) -1) {
		return ENOMEM;
	}

	// Another 2MB hugepage for the receive descriptors
	const uintptr_t receive_ring = tn_hp_allocate(2 * 1024 * 1024);
	if (receive_ring == (uintptr_t) -1) {
		return ENOMEM;
	}

	// Another 2MB hugepage for the send descriptors
	const uintptr_t send_ring = tn_hp_allocate(2 * 1024 * 1024);
	if (send_ring == (uintptr_t) -1) {
		return ENOMEM;
	}

	for (uint8_t n = 0; n < 2; n++) {
		// TODO hardcoded addrs and len...
		const uintptr_t dev_base_addr = tn_pci_get_device_address(0x83, 0x00, n, 512 * 1024); // length comes from manually checking
		if (dev_base_addr == (uintptr_t) -1) {
			return EINVAL;
		}
		if (!ixgbe_device_init(dev_base_addr)) {
			return EINVAL;
		}

	
	
if (n == 0) {
		if (!ixgbe_device_init_receive(dev_base_addr, 0, receive_ring, 128, packet_buffers)) {
			return EINVAL;
		}
		if (!ixgbe_device_set_promiscuous(dev_base_addr)) {
			return EINVAL;
		}

		tn_devices[n].recv_base = (uint64_t*) receive_ring;
} else {
		if (!ixgbe_device_init_send(dev_base_addr, 0, send_ring, 128, packet_buffers)) {
			return EINVAL;
		}

		tn_devices[n].send_base = (uint64_t*) send_ring;
}
//ixgbe_stats_reset(dev_base_addr);
//ixgbe_sanity_check(dev_base_addr);

		tn_devices[n].base_addr = dev_base_addr;
	}

	tn_packets = packet_buffers;

	return 0;
}

//static void tn_dev_reg_write(uintptr_t addr, uint32_t reg, uint32_t value) { tn_write_barrier(); *((volatile uint32_t*)((char*)addr + reg)) = tn_cpu_to_le(value); }
#include <inttypes.h>
void tn_dev_receive(void)
{
	tn_packet_index = tn_devices[0].recv_head & 255; // 128 buffers, 2 lines each -> 256 addresses
	uint64_t packet_metadata;
	do {
		packet_metadata = *((volatile uint64_t*)(tn_devices[0].recv_base + tn_packet_index + 1));
	} while((packet_metadata & 1) == 0);
	tn_packet_length = (packet_metadata >> 32) & 0xFFFFu;
	tn_devices[0].recv_head = (uint16_t) (tn_devices[0].recv_head + 2u);
	// TODO do this at TX time! otherwise RX might overwrite it.
//	tn_devices[1].recv_tail = 2;
	// TODO in fact we don't need recv tail, it should be head at this point
	//tn_dev_reg_write(tn_devices[1].base_addr, 0x06018u, tn_devices[1].recv_tail & 255);
}

void tn_dev_transmit(void)
{
}

// TODO: tn_dev_drop(void);

uintptr_t tn_dev_get_packet(void)
{
	return tn_packets + (uintptr_t) (tn_packet_index * IXGBE_PACKET_SIZE_MAX);
}

uint16_t tn_dev_get_packet_length(void)
{
	return tn_packet_length;
}
