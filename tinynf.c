#include "ixgbe_82599.h"

#include "os/hugepage.h"

#include <stdbool.h>
#include <stdio.h>
#include <inttypes.h>

// Packet processing
int main(int argc, char** argv)
{
	setvbuf(stdout, NULL, _IONBF, 0);

	(void) argc;
	(void) argv;

	const uintptr_t packet_buffers = tn_hp_allocate(IXGBE_PACKET_SIZE_MAX * IXGBE_RING_SIZE);
	if (packet_buffers == (uintptr_t) -1) {
		return 1;
	}

	struct ixgbe_queue queue_receive;
	struct ixgbe_queue queue_send;
	for (uint8_t n = 0; n < 2; n++) {
		struct ixgbe_device device;
		if (!ixgbe_device_get(0x83, 0x00, n, &device)) {
			return 2 + 100*n;
		}
		if (!ixgbe_device_init(&device)) {
			return 3 + 100*n;
		}
		if (!ixgbe_device_set_promiscuous(&device)) {
			return 4 + 100*n;
		}

		if (n == 0) {
			if (!ixgbe_device_init_receive_queue(&device, 0, packet_buffers, &queue_receive)) {
				return 5;
			}
		} else {
			if (!ixgbe_device_init_send_queue(&device, 0, packet_buffers, &queue_send)) {
				return 6;
			}
		}
	}
printf("Initialized successfully!\n");
	while (true) {
//	for (int n = 0; n < 50; n++) {
		uint16_t packet_len = ixgbe_receive(&queue_receive);
//		printf("Received a packet!\n");
		uint8_t* packet = (uint8_t*) (packet_buffers + IXGBE_PACKET_SIZE_MAX * queue_receive.packet_index);
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
