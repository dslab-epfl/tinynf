#include "device.h"
#include "filesystem.h"
#include "hugepage.h"
#include "pci.h"

#include <errno.h>
#include <stdlib.h>
#include <stdint.h>
#include <stdio.h>


static int ret_;
#define DO_OR_RET(call) ret_ = call; if (ret_ != 0) return ret_;


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
}

// Known devices
char* tn_device_addrs[] = { "0000:85:00.0", "0000:85:00.1", NULL };
struct tn_device tn_devices[2];

// Packet processing state
void** tn_packets;
size_t tn_packet_index;
uint16_t tn_packet_length;

static int tn_dev_init(struct tn_device* device)
{
}

static int tn_dev_init_recv(struct tn_device* device, void** packets_base_addr, uint16_t packets_count)
{
}

static int tn_dev_init_send(struct tn_device* device, void** packets_base_addr, uint16_t packets_count)
{
}

static int tn_dev_start(struct tn_device* device)
{
}

// Initialization; returns 0 or error code.
int tn_dev_init(void)
{
	// Allocate a 2MB hugepage, enough for 128 16KB buffers
	void* hugepage = tn_hp_allocate(128 * 16 * 1024);
	if (hugepage == NULL) {
		return ENOMEM;
	}

	for (int n = 0; tn_device_addrs[n] != NULL; n++) {
		char* dev_pci_addr = tn_device_addrs[n];

		uint64_t dev_base_addr = tn_pci_get_device(tn_device_addrs[n], 0x7FFFF); // length comes from manually checking
		if (dev_base_addr == 0) {
			return EINVAL;
		}

		tn_devices[n].base_addr = dev_base_addr;
		DO_OR_RET(tn_dev_init(&tn_devices[n]));
		DO_OR_RET(tn_dev_init_recv(&tn_devices[n], hugepage, 128));
		DO_OR_RET(tn_dev_init_send(&tn_devices[n], hugepage, 128));
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
}

void tn_dev_init(void)
{
	/sys/bus/pci/devices/0000\:85\:00.0/resource
}

void tn_dev_receive(void);

void tn_dev_transmit(void);

// TODO: tn_dev_drop(void);

void* tn_dev_get_packet(void);
int16_t tn_dev_get_packet_length(void);
