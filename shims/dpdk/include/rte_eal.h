#pragma once

#include <stdbool.h>

#include <tn_dpdk.h>
#include "net/network.h"
#include "util/parse.h"


// We do not accept real DPDK arguments, but instead a list of PCI addresses for devices
static inline int rte_eal_init(int argc, char** argv)
{
	int devices_count = 0;
	int other_count = 0;
	char* devices_args[TN_DPDK_DEVICES_MAX_COUNT];
	// note that argv[0] is the program name
	for (int n = 1; n < argc; n++) {
		if (argv[n][0] == '-' && argv[n][1] == '-') {
			if (argv[n][2] == '\0') {
				break;
			} else {
				// some other arg, like --no-shconf
				other_count++;
				continue;
			}
		}
		devices_args[devices_count] = argv[n];
		devices_count++;
	}

	if (!tn_util_parse_pci(devices_count, devices_args, tn_dpdk_pci_devices)) {
		return -1;
	}

	for (int n = 0; n < devices_count; n++) {
		if (!tn_net_device_init(tn_dpdk_pci_devices[n], &(tn_dpdk_devices[n].device))) {
			return -2;
		}

		if (!tn_net_agent_init(&(tn_dpdk_devices[n].agent))) {
			return -3;
		}

		if (!tn_net_agent_set_input(tn_dpdk_devices[n].agent, tn_dpdk_devices[n].device)) {
			return -4;
		}
	}

#ifdef ASSUME_ONE_WAY
	if (devices_count != 2) {
		return -5;
	}

	for (int n = 0; n < devices_count; n++) {
		if (!tn_net_agent_add_output(tn_dpdk_devices[n].agent, tn_dpdk_devices[1 - n].device, n)) {
			return -6;
		}
	}
#else
	for (int n = 0; n < devices_count; n++) {
		for (int d = 0; d < devices_count; d++) {
			if (!tn_net_agent_add_output(tn_dpdk_devices[n].agent, tn_dpdk_devices[d].device, n)) {
				return -7;
			}
		}
	}
#endif

	tn_dpdk_devices_count = devices_count;

	return devices_count + other_count + 1; // consumed count, plus argv[0]; but if the -- marker is present it stays, since argv[0] is expected to be ignored!
}
