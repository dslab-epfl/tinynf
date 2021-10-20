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

int main(int argc, char** argv)
{
	struct tn_pci_address pci_addresses[2];
	if (argc - 1 != 2 || !tn_util_parse_pci(2, argv + 1, pci_addresses)) {
		TN_INFO("Couldn't parse two PCI devices from argv");
		return 1;
	}

	struct tn_net_device* devices[2];
	if (!tn_net_device_init(pci_addresses[0], &(devices[0]))) {
		TN_INFO("Could not init device 0");
		return 2;
	}
	if (!tn_net_device_init(pci_addresses[1], &(devices[1]))) {
		TN_INFO("Could not init device 0");
		return 3;
	}

	if (!tn_net_device_set_promiscuous(devices[0])) {
		TN_INFO("Could not make device 0 promiscuous");
		return 4;
	}
	if (!tn_net_device_set_promiscuous(devices[1])) {
		TN_INFO("Could not make device 1 promiscuous");
		return 5;
	}

	struct tn_net_agent* agents[2];
	if (!tn_net_agent_init(devices[0], 1, &(devices[1]), &(agents[0]))) {
		TN_INFO("Could not init agent 0");
		return 6;
	}
	if (!tn_net_agent_init(devices[1], 1, &(devices[0]), &(agents[1]))) {
		TN_INFO("Could not init agent 1");
		return 6;
	}

	TN_INFO("TinyNF initialized successfully!");

	while (true) {
		tn_net_run(agents[0], &tinynf_packet_handler);
		tn_net_run(agents[1], &tinynf_packet_handler);
	}
}
