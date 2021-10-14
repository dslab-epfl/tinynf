#include "env/pci.h"
#include "net/network.h"
#include "util/log.h"
#include "util/parse.h"


static void tinynf_packet_handler(uint8_t* packet, uint16_t packet_length, uint16_t* outputs)
{
	// DST MAC
	packet[0] = 0;
	packet[1] = 0;
	packet[2] = 0;
	packet[3] = 0;
	packet[4] = 0;
	packet[5] = 1;
	// SRC MAC
	packet[6] = 0;
	packet[7] = 0;
	packet[8] = 0;
	packet[9] = 0;
	packet[10] = 0;
	packet[11] = 0;

	outputs[0] = packet_length;
}

static void run(struct tn_net_agent** agents)
{
	while (true) {
		tn_net_run(agents[0], &tinynf_packet_handler);
		tn_net_run(agents[1], &tinynf_packet_handler);
	}
}

int main(int argc, char** argv)
{
	struct tn_pci_address pci_addresses[2];
	if (argc - 1 != 2 || !tn_util_parse_pci(2, argv + 1, pci_addresses)) {
		TN_INFO("Couldn't parse two PCI devices from argv");
		return 1;
	}

	struct tn_net_device* devices[2];
	for (uint8_t n = 0; n < 2; n++) {
		if (!tn_net_device_init(pci_addresses[n], &(devices[n]))) {
			TN_INFO("Couldn't init device");
			return 3 + 100*n;
		}
		if (!tn_net_device_set_promiscuous(devices[n])) {
			TN_INFO("Couldn't make device promiscuous");
			return 4 + 100*n;
		}
	}

	struct tn_net_agent* agents[2];
	for (uint8_t n = 0; n < 2; n++) {
		if (!tn_net_agent_init(devices[n], 1, &devices[1 - n], &(agents[n]))) {
			TN_INFO("Couldn't init agent");
			return 2 + 100*n;
		}
	}

	TN_INFO("TinyNF initialized successfully!");

	run(agents);
}
