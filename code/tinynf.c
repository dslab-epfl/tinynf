#include "env/pci.h"
#include "net/network.h"
#include "util/log.h"
#include "util/parse.h"
#include "util/perf.h"

// This NF does as little as possible, it's only intended for benchmarking/profiling the driver

#ifndef TRUE_NOP
static uint16_t tinynf_packet_handler(uint8_t* packet, uint16_t packet_length, void* state, bool* outputs)
{
	(void) state;

	// SRC MAC
	packet[0] = 0;
	packet[1] = 0;
	packet[2] = 0;
	packet[3] = 0;
	packet[4] = 0;
	packet[5] = 1;
	// DST MAC
	packet[6] = 0;
	packet[7] = 0;
	packet[8] = 0;
	packet[9] = 0;
	packet[10] = 0;
	packet[11] = 0;

	outputs[0] = true;
	return packet_length;
}
#endif

int main(int argc, char** argv)
{
	struct tn_pci_device pci_devices[2];
	if (argc - 1 != 2 || !tn_util_parse_pci(2, argv + 1, pci_devices)) {
		TN_INFO("Couldn't parse two PCI devices from argv");
		return 1;
	}

	struct tn_net_agent* agents[2];
	struct tn_net_device* devices[2];
	for (uint8_t n = 0; n < 2; n++) {
		if (!tn_net_agent_init(&(agents[n]))) {
			TN_INFO("Couldn't init agent");
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
		if (!tn_net_agent_set_input(agents[n], devices[n])) {
			TN_INFO("Couldn't set agent RX");
			return 5 + 100*n;
		}
	}

	for (uint8_t n = 0; n < 2; n++) {
		if (!tn_net_agent_add_output(agents[n], devices[1 - n], 0)) {
			TN_INFO("Couldn't set agent TX");
			return 6 + 100*n;
		}
	}

	TN_INFO("TinyNF initialized successfully!");
	TN_PERF_PAPI_START();

#ifdef TRUE_NOP
	uint8_t* packet;
	uint16_t packet_length;
	while(true) {
		for (uint64_t p = 0; p < 2; p++) {
			TN_PERF_PAPI_RESET();
			tn_net_agent_receive(agents[p], &packet, &packet_length);
			bool output = true;
			tn_net_agent_transmit(agents[p], packet_length, &output);
			TN_PERF_PAPI_RECORD(1);
		}
	}
#else
	tn_net_packet_handler* handlers[2] = { tinynf_packet_handler, tinynf_packet_handler };
	void* states[2]; // unused
	tn_net_run(2, agents, handlers, states);
#endif
}
