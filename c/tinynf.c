#include "env/pci.h"
#include "net/network.h"
#include "util/log.h"
#include "util/parse.h"


static void tinynf_packet_handler(volatile uint8_t* packet, uint16_t packet_length, uint16_t* outputs)
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

// This noinline function is there so GCC realizes it can use all registers
// (otherwise it keeps some regs unused, presumably because initialization
//  makes it think they will be used later...)
__attribute__((noinline))
static void run(struct tn_net_agent agent0, struct tn_net_agent agent1)
{
	while (true) {
#ifdef DANGEROUS
		tn_net_run(&agent0, &tinynf_packet_handler, 1);
		tn_net_run(&agent1, &tinynf_packet_handler, 1);
#else
		tn_net_run(&agent0, &tinynf_packet_handler);
		tn_net_run(&agent1, &tinynf_packet_handler);
#endif
	}
}

int main(int argc, char** argv)
{
	struct tn_pci_address pci_addresses[2];
	if (argc - 1 != 2 || !tn_util_parse_pci(2, argv + 1, pci_addresses)) {
		TN_INFO("Couldn't parse two PCI devices from argv");
		return 1;
	}

	struct tn_net_device device0;
	struct tn_net_device device1;
	if (!tn_net_device_init(pci_addresses[0], &device0)) {
		TN_INFO("Could not init device 0");
		return 2;
	}
	if (!tn_net_device_init(pci_addresses[1], &device1)) {
		TN_INFO("Could not init device 0");
		return 3;
	}

	if (!tn_net_device_set_promiscuous(&device0)) {
		TN_INFO("Could not make device 0 promiscuous");
		return 4;
	}
	if (!tn_net_device_set_promiscuous(&device1)) {
		TN_INFO("Could not make device 1 promiscuous");
		return 5;
	}

	struct tn_net_agent agent0;
	struct tn_net_agent agent1;
	if (!tn_net_agent_init(&device0, 1, &device1, &agent0)) {
		TN_INFO("Could not init agent 0");
		return 6;
	}
	if (!tn_net_agent_init(&device1, 1, &device0, &agent1)) {
		TN_INFO("Could not init agent 1");
		return 6;
	}

	TN_INFO("TinyNF initialized successfully!");

	run(agent0, agent1);
}
