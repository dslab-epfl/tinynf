#include "env/pci.h"
#include "net/network.h"
#include "util/log.h"
#include "util/parse.h"
#include "util/perf.h"

// This NF does as little as possible, it's only intended for benchmarking/profiling the driver

static uint16_t tinynf_packet_handler(uint8_t* packet, uint16_t packet_length, bool* send_list)
{
	(void) packet;

	send_list[0] = true;
	return packet_length;
}

int main(int argc, char** argv)
{
	uint64_t devices_count = (uint64_t) argc - 1;
	struct tn_pci_device pci_devices[2];
	if (devices_count != 2 || !tn_util_parse_pci(devices_count, argv + 1, pci_devices)) {
		TN_INFO("Couldn't parse two PCI devices from argv");
		return 1;
	}

	struct tn_net_pipe* pipes[2];
	struct tn_net_device* devices[2];
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
	TN_PERF_PAPI_START();

	while(true) {
		for (uint64_t p = 0; p < 2; p++) {
			TN_PERF_PAPI_RESET();
			tn_net_pipe_process(pipes[p], tinynf_packet_handler);
			TN_PERF_PAPI_RECORD();
		}
	}
}
