#include "env/pci.h"
#include "net/network.h"
#include "util/log.h"
#include "util/parse.h"

#include <tn_dpdk.h>

#include "nf.h"

#define PF_COUNT 2
#define AGENTS_PER_PF 16

static uint16_t tinynf_packet_handler(uint8_t* packet, uint16_t packet_length, void* state, bool* outputs)
{
	uint16_t device = (uint16_t) state;
	int vigor_output = nf_process(device, packet, packet_length, current_time());
	outputs[0] = vigor_output != device;
	return packet_length;
}

int main(int argc, char** argv)
{
	struct tn_pci_address pci_addresses[PF_COUNT];
	if (argc - 1 < PF_COUNT || !tn_util_parse_pci(PF_COUNT, argv + 1, pci_addresses)) {
		TN_INFO("Couldn't parse PCI devices from argv");
		return 1;
	}

	// Devices
	struct tn_net_device* devices[PF_COUNT];
	for (uint8_t d = 0; d < PF_COUNT; d++) {
		if (!tn_net_device_init(pci_addresses[d], &(devices[d]))) {
			TN_INFO("Couldn't init device");
			return 2 + 100*d;
		}
		if (!tn_net_device_set_promiscuous(devices[d])) {
			TN_INFO("Couldn't make device promiscuous");
			return 3 + 100*d;
		}
	}

	// Agents
	struct tn_net_agent* agents[AGENTS_PER_PF * PF_COUNT];
	for (uint8_t a = 0; a < AGENTS_PER_PF * PF_COUNT; a++) {
		if (!tn_net_agent_init(&(agents[a]))) {
			TN_INFO("Couldn't init agent");
			return 4 + 100*a;
		}
	}

	// Inputs
	for (uint8_t a = 0; a < AGENTS_PER_PF * PF_COUNT; a++) {
		if (!tn_net_agent_set_input(agents[a], devices[(a / AGENTS_PER_PF)])) {
			TN_INFO("Couldn't set agent RX");
			return 5 + 100*a;
		}
	}

	// Outputs
	for (uint8_t a = 0; a < AGENTS_PER_PF * PF_COUNT; a++) {
		if (!tn_net_agent_add_output(agents[a], devices[1 - (a / AGENTS_PER_PF)])) {
			TN_INFO("Couldn't set agent TX");
			return 6 + 100*a;
		}
	}

	// The policer ask DPDK for the devices count
	tn_dpdk_devices_count = PF_COUNT;
	nf_config_init(argc - PF_COUNT - 1, argv + PF_COUNT + 1); // skip the 0th (program name) and the PCI addresses
	nf_config_print();
	if (!nf_init()) {
		return 7;
	}

	TN_INFO("TinyNF on SR-IOV initialized successfully!");

	tn_net_packet_handler* handlers[AGENTS_PER_PF * PF_COUNT];
	void* states[AGENTS_PER_PF * PF_COUNT];
	for (uint16_t n = 0; n < AGENTS_PER_PF * PF_COUNT; n++) {
		handlers[n] = tinynf_packet_handler;
		states[n] = (void*) (n / AGENTS_PER_PF);
	}
	tn_net_run(AGENTS_PER_PF * PF_COUNT, agents, handlers, states);
}
