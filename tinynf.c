#include "config.h"
#include "ixgbe_82599.h"

#include "os/cpu.h"
#include "os/memory.h"

#include <stdbool.h>
#include <stdio.h>
#include <inttypes.h>

// Packet processing
int main(int argc, char** argv)
{
	setvbuf(stdout, NULL, _IONBF, 0);

	(void) argc;
	(void) argv;

	if(!tn_cpu_set_current(TN_CONFIG_CPU)) {
		return -1;
	}

	node_t this_node;
	if (!tn_cpu_get_current_node(&this_node)) {
		return 33;
	}

	struct tn_memory_block packet_buffers;
	if (!tn_mem_allocate(IXGBE_PACKET_SIZE_MAX * IXGBE_RING_SIZE, this_node, &packet_buffers)) {
		return 1;
	}

	struct ixgbe_queue queue_receive;
	struct ixgbe_queue queue_send;
	for (uint8_t n = 0; n < 2; n++) {
		struct tn_pci_device pci_device = {.bus=0x83, .device=0x00, .function=n};
		node_t device_node;
		if (!tn_pci_get_device_node(pci_device, &device_node)) {
			return 10 + 100*n;
		}

		if (device_node != this_node) {
			return 11 + 100*n;
		}

		struct ixgbe_device device;
		if (!ixgbe_device_get(pci_device, &device)) {
			return 2 + 100*n;
		}
		if (!ixgbe_device_init(&device)) {
			return 3 + 100*n;
		}
		if (!ixgbe_device_set_promiscuous(&device)) {
			return 4 + 100*n;
		}

		if (n == 0) {
			if (!ixgbe_device_init_receive_queue(&device, 0, packet_buffers.phys_addr, &queue_receive)) {
				return 5;
			}
		} else {
			if (!ixgbe_device_init_send_queue(&device, 0, packet_buffers.phys_addr, &queue_send)) {
				return 6;
			}
		}
	}
printf("Initialized successfully!\n");
	while (true) {
//	for (int n = 0; n < 50; n++) {
		uint16_t packet_len = ixgbe_receive(&queue_receive);
//		printf("Received a packet!\n");
		uint8_t* packet = (uint8_t*) (packet_buffers.virt_addr + IXGBE_PACKET_SIZE_MAX * queue_receive.packet_index);
//	for (uint16_t n = 0; n < packet_len; n++) {
//		printf("0x%02"PRIx8" ", packet[n]);
//	}
		// SRC MAC (90:e2:ba:55:14:11)
		packet[0] = 0x90;
		packet[1] = 0xE2;
		packet[2] = 0xBA;
		packet[3] = 0x55;
		packet[4] = 0x14;
		packet[5] = 0x11;
		// DST MAC (90:e2:ba:55:12:25)
		packet[6] = 0xFF;
		packet[7] = 0xFF;
		packet[8] = 0xFF;
		packet[9] = 0xFF;
		packet[10]= 0xFF;
		packet[11]= 0xFF;

		ixgbe_send(&queue_send, packet_len);
//		printf("Sent a packet!\n");
	}

	return 0;
}
