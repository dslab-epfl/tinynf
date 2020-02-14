// TinyNF
#include "net/network.h"
#include "util/log.h"
#include "util/parse.h"

// Vigor
#include "nf.h"
#include "nf-util.h"

// DPDK devices count and args parsing
#include <tn_dpdk.h>
#include <rte_ethdev.h>
#include <rte_eal.h>

#include <stdbool.h>
#include <stddef.h>


#define DEVICES_MAX_COUNT 2u

static uint16_t current_device;
static uint16_t devices_count;
static vigor_time_t vigor_now;
static uint16_t compat_packet_handler(uint8_t* packet, uint16_t packet_length, bool* outputs)
{
	int vigor_output = nf_process(current_device, packet, packet_length, vigor_now);
	// Vigor needs this to be called after nf_process
	nf_return_all_chunks(packet);

#ifdef ASSUME_ONE_WAY
	outputs[0] = vigor_output != current_device;
#else
	if (vigor_output == FLOOD_FRAME) {
		for (uint16_t n = 0; n < devices_count; n++) {
			outputs[n] = n != current_device;
		}
	} else if (vigor_output == current_device) {
		// Nothing; this means "drop", Vigor has no notion of sending back to the same device
	} else {
		outputs[vigor_output] = true;
	}
#endif

	// Vigor cannot change the packet length
	return packet_length;
}

int main(int argc, char** argv)
{
	int consumed = rte_eal_init(argc, argv);
	if (consumed < 0) {
		return 1;
	}

	argc -= consumed;
	argv += consumed;

	devices_count = rte_eth_dev_count();

	// TinyNF init
	struct tn_net_device* devices[DEVICES_MAX_COUNT];
	struct tn_net_agent* agents[DEVICES_MAX_COUNT];
	for (uint16_t n = 0; n < devices_count; n++) {
		if (!tn_net_device_init(tn_dpdk_pci_devices[n], &(devices[n]))) {
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
	if (devices_count != 2) {
		return 2;
	}

	for (uint16_t p = 0; p < devices_count; p++) {
		if (!tn_net_agent_add_output(agents[p], devices[1 - p], 0)) {
			return 10000 + p;
		}
	}
#else
	for (uint16_t p = 0; p < devices_count; p++) {
		for (uint16_t q = 0; q < devices_count; q++) {
			if (!tn_net_agent_add_output(agents[p], devices[q], p)) {
				return 10000 + p * q;
			}
		}
	}
#endif

	nf_config_init(argc, argv);
	nf_config_print();

	if (!nf_init()) {
		return 3;
	}

	// Compat layer
	TN_INFO("Running Vigor NF on top of TinyNF...");
#ifdef ASSUME_ONE_WAY
	TN_INFO("Assuming the NF only needs one-way agents, hope you know what you're doing...");
#endif
	while(true) {
		vigor_now = current_time();
		for (current_device = 0; current_device < devices_count; current_device++) {
			tn_net_agent_process(agents[current_device], compat_packet_handler);
		}
	}
}
