#include "env/pci.h"
#include "net/network.h"
#include "util/log.h"
#include "util/parse.h"

#ifdef TN_DEBUG_PERF
#include <stdio.h>
#include "papi.h"
#endif

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

#ifdef TN_DEBUG_PERF
	TN_INFO("Counters: instructions, L1d, L1i, L2, L3");
	int papi_events[] = {PAPI_TOT_INS, PAPI_L1_DCM, PAPI_L1_ICM, PAPI_L2_TCM, PAPI_L3_TCM};
	#define papi_events_count sizeof(papi_events)/sizeof(papi_events[0])
	#define papi_batch_size 10000
	long long papi_values[papi_batch_size][papi_events_count];
	if (PAPI_start_counters(papi_events, papi_events_count) != PAPI_OK) {
		TN_INFO("Couldn't start PAPI counters.");
		return 7;
	}
	uint64_t papi_counter = 0;
#endif

	while(true) {
		for (uint64_t p = 0; p < 2; p++) {
#ifdef TN_DEBUG_PERF
			PAPI_read_counters(papi_values[papi_counter], papi_events_count);
#endif
			tn_net_pipe_process(pipes[p], tinynf_packet_handler);

#ifdef TN_DEBUG_PERF
			PAPI_read_counters(papi_values[papi_counter], papi_events_count);

			papi_counter++;
			if (papi_counter == papi_batch_size) {
				papi_counter = 0;
				for (uint64_t n = 0; n < papi_batch_size; n++) {
					for (uint64_t e = 0; e < papi_events_count; e++) {
						printf("%lld ", papi_values[n][e]);
					}
					printf("\n");
				}
			}
#endif
		}
	}
}
