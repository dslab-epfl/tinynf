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

	uint64_t ring_size = ixgbe_get_ring_size();
	uint64_t packet_size_max = ixgbe_get_packet_size_max();

	struct tn_memory_block packet_buffers;
	if (!tn_mem_allocate(packet_size_max * ring_size, &packet_buffers)) {
		TN_INFO("Couldn't alloc packet buffers");
		return 1;
	}

	struct ixgbe_pipe* pipe;
	if (!ixgbe_pipe_init(packet_buffers.phys_addr, &pipe)) {
		TN_INFO("Couldn't init pipe");
		return 2;
	}
	for (uint8_t n = 0; n < 2; n++) {
		struct tn_pci_device pci_device = {.bus=0x83, .device=0x00, .function=n};
		struct ixgbe_device* device;
		if (!ixgbe_device_init(pci_device, &device)) {
			TN_INFO("Couldn't init device");
			return 3 + 100*n;
		}
		if (!ixgbe_device_set_promiscuous(device)) {
			TN_INFO("Couldn't make device promiscuous");
			return 4 + 100*n;
		}

		if (n == 0) {
			if (!ixgbe_pipe_set_receive(pipe, device, 0)) {
				TN_INFO("Couldn't set pipe RX");
				return 5;
			}
		} else {
			if (!ixgbe_pipe_set_send(pipe, device, 0)) {
				TN_INFO("Couldn't set pipe TX");
				return 6;
			}
		}
	}

	TN_INFO("Initialized successfully!");

//	TN_PERF_START();

	while (true) {
//	for (uint64_t _ = 0; _ < 1000; _++) {
		uint64_t packet_length;
		uint64_t packet_index;
		if (!ixgbe_receive(pipe, &packet_length, &packet_index)) {
			continue;
		}
		uint8_t* packet = (uint8_t*) (packet_buffers.virt_addr + packet_size_max * packet_index);
//	for (uint64_t n = 0; n < packet_length; n++) {
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

		ixgbe_send(pipe, packet_length);
	}

//	TN_PERF_DUMP();

	TN_INFO("Done!");

	return 0;
}
