// TinyNF
#include "net/network.h"
#include "util/log.h"
#include "util/parse.h"

// Vigor
#include "nf.h"
#include "nf-util.h"

// DPDK devices count
#include <tn_dpdk.h>

#include <stdbool.h>
#include <stddef.h>


// A bit hacky to hardcode this; but we don't need more for benchmarking
#define DEVICES_COUNT 2u

static uint16_t device;
static uint16_t compat_packet_handler(uint8_t* packet, uint16_t packet_length, bool* outputs)
{
	vigor_time_t vigor_now = current_time();

	int vigor_output = nf_process(device, packet, packet_length, vigor_now);
	// Vigor needs this to be called after nf_process
	nf_return_all_chunks(packet);

#ifdef ASSUME_ONE_WAY
	outputs[0] = vigor_output != device;
#else
	if (vigor_output == device) {
		for (uint16_t n = 0; n < DEVICES_COUNT; n++) {
			outputs[n] = false;
		}
	} else { // flood or send, same thing with 2 devices...
		for (uint16_t n = 0; n < DEVICES_COUNT; n++) {
			outputs[n] = n != device;
		}
	}
#endif

	// Vigor cannot change the packet length
	return packet_length;
}

int main(int argc, char** argv)
{
	struct tn_pci_address pci_addresses[DEVICES_COUNT];
	if (argc - 1 < DEVICES_COUNT || !tn_util_parse_pci(DEVICES_COUNT, argv + 1, pci_addresses)) {
		TN_INFO("Couldn't parse two PCI devices from argv");
		return 1;
	}

	// TinyNF init
	struct tn_net_device* devices[DEVICES_COUNT];
	struct tn_net_agent* agents[DEVICES_COUNT];
	for (uint16_t n = 0; n < DEVICES_COUNT; n++) {
		if (!tn_net_device_init(pci_addresses[n], &(devices[n]))) {
			return 1000 + n;
		}
		if (!tn_net_device_set_promiscuous(devices[n])) {
			return 2000 * n;
		}
		if (!tn_net_agent_init(&(agents[n]))) {
			return 3000 + n;
		}
		if (!tn_net_agent_set_input(agents[n], devices[n])) {
			return 4000 + n;
		}
	}

#ifdef ASSUME_ONE_WAY
	for (uint16_t p = 0; p < DEVICES_COUNT; p++) {
		if (!tn_net_agent_add_output(agents[p], devices[1 - p])) {
			return 10000 + p;
		}
	}
#else
	for (uint16_t p = 0; p < DEVICES_COUNT; p++) {
		for (uint16_t q = 0; q < DEVICES_COUNT; q++) {
			if (!tn_net_agent_add_output(agents[p], devices[q])) {
				return 10000 + p * q;
			}
		}
	}
#endif

	// Vigor NFs ask DPDK for the devices count
	tn_dpdk_devices_count = DEVICES_COUNT;

	nf_config_init(argc - DEVICES_COUNT - 1, argv + DEVICES_COUNT + 1);
	nf_config_print();

	if (!nf_init()) {
		return 3;
	}

	// Compat layer
	TN_INFO("Running Vigor NF on top of TinyNF...");
#ifdef ASSUME_ONE_WAY
	TN_INFO("Assuming the NF only needs one-way agents, hope you know what you're doing...");
#endif
	while (true) {
		for (device = 0; device < DEVICES_COUNT; device++) {
			tn_net_run(agents[device], &compat_packet_handler);
		}
	}
}
