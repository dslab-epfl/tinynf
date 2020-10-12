#include "env/pci.h"
#include "net/network.h"
#include "util/log.h"
#include "util/parse.h"
#include "util/perf.h"

// This NF does as little as possible, it's only intended for benchmarking/profiling the driver

#ifndef TN_DEBUG_PERF
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
	struct tn_pci_address pci_addresses[2];
	if (argc - 1 != 1 || !tn_util_parse_pci(1, argv + 1, pci_addresses)) {
		TN_INFO("Couldn't parse one PCI device from argv");
		return 1;
	}

	struct tn_net_agent* agents[2];
	struct tn_net_device* devices[2];
	for (uint8_t n = 0; n < 2; n++) {
		if (!tn_net_agent_init(&(agents[n]))) {
			TN_INFO("Couldn't init agent %d", n);
			return 2 + 100*n;
		}
		if (!tn_net_device_init(pci_addresses[n], &(devices[n]))) {
			TN_INFO("Couldn't init device %d", n);
			return 3 + 100*n;
		}
		if (!tn_net_device_set_promiscuous(devices[n])) {
			TN_INFO("Couldn't make device promiscuous %d", n);
			return 4 + 100*n;
		}
		if (!tn_net_agent_set_input(agents[n], devices[n])) {
			TN_INFO("Couldn't set agent RX");
			return 5 + 100*n;
		}
	}

	for (uint8_t n = 0; n < 2; n++) {
		if (!tn_net_agent_add_output(agents[n], devices[1 - n])) {
			TN_INFO("Couldn't set agent TX");
			return 6 + 100*n;
		}
	}

	TN_INFO("TinyNF initialized successfully!");

#ifndef TN_DEBUG_PERF
	tn_net_packet_handler* handlers[2] = { tinynf_packet_handler, tinynf_packet_handler };
	void* states[2] = {0}; // unused
	tn_net_run(2, agents, handlers, states);
#else
	uint8_t lookup_table[256 * 256];
	for (uint64_t n = 0; n < sizeof(lookup_table)/sizeof(uint8_t); n++) {
		lookup_table[n] = (uint8_t) (n * 123);
	}

	uint8_t* packet;
	uint16_t packet_length;
	bool output = true;
	TN_PERF_PAPI_INIT();
	while(true) {
		for (uint64_t a = 0; a < 2; a++) {
			for (uint64_t p = 0; p < 8; p++) { // sync '8' here with PROCESS_PERIOD in ixgbe
				TN_PERF_PAPI_RESET();
				if (!tn_net_agent_receive(agents[a], &packet, &packet_length)) {
					break;
				}
#ifdef TN_DEBUG_PERF_DOWRITE
				packet[0] = lookup_table[0];
				packet[1] = lookup_table[1];
				packet[2] = lookup_table[2];
				packet[3] = lookup_table[3];
				packet[4] = lookup_table[4];
				packet[5] = lookup_table[5];
#elif defined(TN_DEBUG_PERF_DOLOOKUP)
				packet[0] = lookup_table[(packet[6] << 8) | packet[7]];
				packet[1] = lookup_table[(packet[7] << 8) | packet[6]];
				packet[2] = lookup_table[(packet[8] << 8) | packet[9]];
				packet[3] = lookup_table[(packet[9] << 8) | packet[8]];
				packet[4] = lookup_table[(packet[10] << 8) | packet[11]];
				packet[5] = lookup_table[(packet[11] << 8) | packet[10]];
#endif
				tn_net_agent_transmit(agents[a], packet_length, &output);
				TN_PERF_PAPI_RECORD(1);
			}
		}
	}
#endif
}
