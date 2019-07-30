#include "ixgbe_82599.h"
#include "os/memory.h"
#include "os/pci.h"
#include "util/log.h"
#include "util/perf.h"

// Packet processing
int main(int argc, char** argv)
{
	setvbuf(stdout, NULL, _IONBF, 0);

	(void) argc;
	(void) argv;

	struct tn_memory_block packet_buffers;
	if (!tn_mem_allocate(IXGBE_PACKET_SIZE_MAX * IXGBE_RING_SIZE, &packet_buffers)) {
		TN_INFO("Couldn't alloc packet buffers");
		return 1;
	}

	struct ixgbe_queue* queue_receive;
	struct ixgbe_queue* queue_send;
	for (uint8_t n = 0; n < 2; n++) {
		struct tn_pci_device pci_device = {.bus=0x83, .device=0x00, .function=n};
		struct ixgbe_device* device;
		if (!ixgbe_device_get(pci_device, &device)) {
			TN_INFO("Couldn't get device");
			return 2 + 100*n;
		}
		if (!ixgbe_device_init(device)) {
			TN_INFO("Couldn't init device");
			return 3 + 100*n;
		}
		if (!ixgbe_device_set_promiscuous(device)) {
			TN_INFO("Couldn't make device promiscuous");
			return 4 + 100*n;
		}

		if (n == 0) {
			if (!ixgbe_device_init_receive_queue(device, 0, packet_buffers.phys_addr, &queue_receive)) {
				TN_INFO("Couldn't init RX queue");
				return 5;
			}
		} else {
			if (!ixgbe_device_init_send_queue(device, 0, packet_buffers.phys_addr, &queue_send)) {
				TN_INFO("Couldn't init TX queue");
				return 6;
			}
		}
	}

	TN_INFO("Initialized successfully!");

	TN_PERF_START();

	while (true) {
//	for (uint64_t _ = 0; _ < 1000; _++) {
		for (uint64_t n = 0; n < IXGBE_RING_SIZE; n++) {
			uint16_t packet_len = ixgbe_receive(queue_receive);
			uint8_t* packet = (uint8_t*) (packet_buffers.virt_addr + IXGBE_PACKET_SIZE_MAX * n);
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
			// DST MAC
			packet[6] = 0xFF;
			packet[7] = 0xFF;
			packet[8] = 0xFF;
			packet[9] = 0xFF;
			packet[10]= 0xFF;
			packet[11]= 0xFF;

			ixgbe_send(queue_send, packet_len);
		}
	}

	TN_PERF_DUMP();

	TN_INFO("Done!");

	return 0;
}
