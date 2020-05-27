// TinyNF
#include "net/network.h"
#include "util/log.h"
#include "util/parse.h"

// Vigor
#include "nf.h"

// DPDK devices count and args parsing
#include <tn_dpdk.h>
#include <rte_ethdev.h>
#include <rte_eal.h>

#include <stdbool.h>
#include <stddef.h>
#include <pthread.h>

#define DEVICES_MAX_COUNT 2u

static uint16_t packet_handler(uint8_t* packet, uint16_t packet_length, void* state, bool* outputs)
{
	uint16_t device = (uint16_t) state;
	int vigor_output = nf_process(device, packet, packet_length, current_time());
	outputs[0] = vigor_output != device;
	return packet_length;
}

static struct tn_net_agent* agents[DEVICES_MAX_COUNT];

void* thread0(void* arg)
{
	void* state = (uint16_t) 0;
	tn_net_packet_handler* handlers[1] = { packet_handler };
	tn_net_run(1, &(agents[0]), handlers, &state);
}
void* thread1(void* arg)
{
	void* state = (uint16_t) 1;
	tn_net_packet_handler* handlers[1] = { packet_handler };
	tn_net_run(1, &(agents[1]), handlers, &state);
}

int main(int argc, char** argv)
{
	int consumed = rte_eal_init(argc, argv);
	if (consumed < 0) {
		return 1;
	}

	argc -= 3;
	argv += 3;

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

        cpu_set_t s0, s1;
        CPU_ZERO(&s0);
        CPU_ZERO(&s1);
        CPU_SET(8, &s0);
        CPU_SET(9, &s1);
        ret0 = pthread_setaffinity_np(t0, sizeof(cpu_set_t), &s0);
        ret1 = pthread_setaffinity_np(t1, sizeof(cpu_set_t), &s1);
	if (ret0 != 0 || ret1 != 0) {
		return 5;
	}

	pthread_join(t0, NULL);
	pthread_join(t1, NULL);
	return 0;
}
