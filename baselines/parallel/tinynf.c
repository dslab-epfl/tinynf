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

static uint16_t packet_handler0(uint8_t* packet, uint16_t packet_length, bool* outputs)
{
	int vigor_output = nf_process(0, packet, packet_length, current_time());
	nf_return_all_chunks(packet);
	outputs[0] = vigor_output != 0;
	return packet_length;
}
static uint16_t packet_handler1(uint8_t* packet, uint16_t packet_length, bool* outputs)
{
	int vigor_output = nf_process(1, packet, packet_length, current_time());
	nf_return_all_chunks(packet);
	outputs[0] = vigor_output != 1;
	return packet_length;
}

static struct tn_net_agent* agents[DEVICES_MAX_COUNT];

void* thread0(void* arg)
{
	while(true) {
		tn_net_agent_process(agents[0], packet_handler0);
	}
}
void* thread1(void* arg)
{
	while(true) {
		tn_net_agent_process(agents[1], packet_handler0);
	}
}

int main(int argc, char** argv)
{
	int consumed = rte_eal_init(argc, argv);
	if (consumed < 0) {
		return 1;
	}

	argc -= consumed;
	argv += consumed;

	uint16_t devices_count = rte_eth_dev_count();

	// TinyNF init
	struct tn_net_device* devices[DEVICES_MAX_COUNT];
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

	if (devices_count != 2) {
		return 2;
	}

	for (uint16_t p = 0; p < devices_count; p++) {
		if (!tn_net_agent_add_output(agents[p], devices[1 - p], 0)) {
			return 10000 + p;
		}
	}

	nf_config_init(argc, argv);
	nf_config_print();

	if (!nf_init()) {
		return 3;
	}

	TN_INFO("Running Vigor NF on top of TinyNF... IN PARALLEL!");
	TN_INFO("Assuming the NF only needs one-way agents, hope you know what you're doing...");

	pthread_t t0, t1;
	int ret0 = pthread_create(&t0, NULL, thread0, NULL);
	int ret1 = pthread_create(&t1, NULL, thread1, NULL);
	if (ret0 != 0 || ret1 != 0) {
		return 4;
	}
	return 0;
}
