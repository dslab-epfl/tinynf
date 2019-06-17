#include "ixgbe_82599.h"

#include "os/hugepage.h"

#include <stdio.h>
#include <inttypes.h>

// Packet processing
int main(int argc, char** argv)
{
	setvbuf(stdout, NULL, _IONBF, 0);

	(void) argc;
	(void) argv;

	const uintptr_t packet_buffers = tn_hp_allocate(2 * 1024 * 1024);
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
	uint16_t packet_len = ixgbe_receive(&queue_receive);
	uint8_t* packet = (uint8_t*) (packet_buffers + IXGBE_PACKET_SIZE_MAX * queue_receive.packet_index);
printf("Received a packet!\n");
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
	// DST MAC (01:02:03:04:05:06)
	packet[6] = 0x01;
	packet[7] = 0x02;
	packet[8] = 0x03;
	packet[9] = 0x04;
	packet[10]= 0x05;
	packet[11]= 0x06;

	ixgbe_send(&queue_send, packet_len);
printf("Sent a packet!\n");

	return 0;
}
