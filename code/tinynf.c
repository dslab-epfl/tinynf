#include "env/memory.h"
#include "env/pci.h"
#include "net/network.h"
#include "util/log.h"
#include "util/parse.h"


#define DEVICES_MAX_COUNT 128u

static uint16_t tinynf_packet_handler(uint8_t* packet, uint16_t packet_length, bool* send_list)
{
	// SRC MAC
	packet[0] = 0x00;
	packet[1] = 0x01;
	packet[2] = 0x02;
	packet[3] = 0x03;
	packet[4] = 0x04;
	packet[5] = 0x05;
	// DST MAC
	packet[6] = 0xFF;
	packet[7] = 0xFF;
	packet[8] = 0xFF;
	packet[9] = 0xFF;
	packet[10]= 0xFF;
	packet[11]= 0xFF;

	send_list[0] = true;

	return packet_length;
}

int main(int argc, char** argv)
{
	uint64_t devices_count = (uint64_t) argc - 1;
	struct tn_pci_device pci_devices[DEVICES_MAX_COUNT];
	if (devices_count == 0 || devices_count > DEVICES_MAX_COUNT || !tn_util_parse_pci(devices_count, argv+1, pci_devices)) {
		TN_INFO("Couldn't parse PCI devices from argv");
		return 1;
	}

	if (devices_count != 2) {
		TN_INFO("Sorry, this simple NF is just for bench purposes so it supports 2 devices exactly");
		return 1;
	}

	struct tn_net_pipe* pipes[DEVICES_MAX_COUNT];
	struct tn_net_device* devices[DEVICES_MAX_COUNT];
	for (uint8_t n = 0; n < devices_count; n++) {
		if (!tn_net_pipe_init(&(pipes[n]))) {
			TN_INFO("Couldn't init pipe");
			return 2 + 100*n;
		}
		if (!tn_net_device_init(pci_devices[n], &(devices[n]))) {
			TN_INFO("Couldn't init device");
			return 3 + 100*n;
		}
		if (!tn_net_device_set_promiscuous(devices[n])) {
			TN_INFO("Couldn't make device promiscuous");
			return 4 + 100*n;
		}
		if (!tn_net_pipe_set_receive(pipes[n], devices[n], 0)) {
			TN_INFO("Couldn't set pipe RX");
			return 5 + 100*n;
		}
	}

	for (uint8_t n = 0; n < devices_count; n++) {
		if (!tn_net_pipe_add_send(pipes[n], devices[1 - n], 0)) {
			TN_INFO("Couldn't set pipe TX");
			return 6 + 100*n;
		}
	}

	TN_INFO("TinyNF initialized successfully!");

	while(true) {
		tn_net_pipe_run_step(pipes[0], tinynf_packet_handler);
		tn_net_pipe_run_step(pipes[1], tinynf_packet_handler);
	}
}
