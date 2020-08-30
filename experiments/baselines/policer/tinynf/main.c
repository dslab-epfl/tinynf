// TinyNF
#include "net/network.h"
#include "util/log.h"
#include "util/parse.h"

// DPDK devices count
#include <tn_dpdk.h>

#include "nf.h"

#include <stdbool.h>
#include <stddef.h>
#include <pthread.h>

// Hacky but fine for benchmarks
#define DEVICES_COUNT 2u

static uint16_t packet_handler(uint8_t* packet, uint16_t packet_length, void* state, bool* outputs)
{
	uint16_t device = (uint16_t) state;
	int vigor_output = nf_process(device, packet, packet_length, current_time());
	outputs[0] = vigor_output != device;
	return packet_length;
}

static struct tn_net_agent* agents[DEVICES_COUNT];

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
	struct tn_pci_address pci_addresses[DEVICES_COUNT];
	if (argc - 1 < DEVICES_COUNT || !tn_util_parse_pci(DEVICES_COUNT, argv + 1, pci_addresses)) {
		TN_INFO("Couldn't parse two PCI devices from argv");
		return 1;
	}

	// TinyNF init
	struct tn_net_device* devices[DEVICES_COUNT];
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

	for (uint16_t p = 0; p < DEVICES_COUNT; p++) {
		if (!tn_net_agent_add_output(agents[p], devices[1 - p])) {
			return 10000 + p;
		}
	}

	// The policer ask DPDK for the devices count
	tn_dpdk_devices_count = DEVICES_COUNT;

	nf_config_init(argc - DEVICES_COUNT - 1, argv + DEVICES_COUNT + 1); // skip the 0th (program name) and the PCI addresses
	nf_config_print();

	if (!nf_init()) {
		return 3;
	}

	TN_INFO("Running Vigor NF on top of TinyNF...");
#ifdef TN_2CORE
	TN_INFO("...on 2 cores!");

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
#else
	void* states[2] = { 0, 1 };
	tn_net_packet_handler* handlers[2] = { packet_handler, packet_handler };
	tn_net_run(2, agents, handlers, states);
#endif
	return 0;
}
