#include <stdnoreturn.h>

#include "env/pci.h"
#include "ixgbe/agent.h"
#include "ixgbe/device.h"
#include "util/log.h"
#include "util/parse.h"

#include "ixgbe/queues.h"


// Three options for the TN_MODE variable:
// - 0 for the agent-based original TinyNF
// - 1 for the agent-based version with hardcoded outputs count (~= const generics)
// - 2 for the queue-based DPDK-like version

static int init(int argc, char** argv, struct ixgbe_device* out_device0, struct ixgbe_device* out_device1)
{
	struct tn_pci_address pci_addresses[2];
	if (argc - 1 != 2 || !tn_util_parse_pci(2, argv + 1, pci_addresses)) {
		TN_INFO("Couldn't parse two PCI devices from argv");
		return 1;
	}

	if (!ixgbe_device_init(pci_addresses[0], out_device0)) {
		TN_INFO("Could not init device 0");
		return 2;
	}
	if (!ixgbe_device_init(pci_addresses[1], out_device1)) {
		TN_INFO("Could not init device 0");
		return 3;
	}

	if (!ixgbe_device_set_promiscuous(out_device0)) {
		TN_INFO("Could not make device 0 promiscuous");
		return 4;
	}
	if (!ixgbe_device_set_promiscuous(out_device1)) {
		TN_INFO("Could not make device 1 promiscuous");
		return 5;
	}

	return 0;
}

static inline void packet_handler(volatile uint8_t* data)
{
	// DST MAC
	data[0] = 0;
	data[1] = 0;
	data[2] = 0;
	data[3] = 0;
	data[4] = 0;
	data[5] = 1;
	// SRC MAC
	data[6] = 0;
	data[7] = 0;
	data[8] = 0;
	data[9] = 0;
	data[10] = 0;
	data[11] = 0;
}

#if TN_MODE == 0 || TN_MODE == 1
static void agent_packet_handler(volatile uint8_t* packet, uint16_t packet_length, uint16_t* outputs)
{
	packet_handler(packet);
	// Output on opposite device
	outputs[0] = packet_length;
}

// This noinline function is there so GCC realizes it can use all registers
// (otherwise it keeps some regs unused, presumably because initialization
//  makes it think they will be used later...)
__attribute__((noinline))
noreturn static void run(struct ixgbe_agent agent0, struct ixgbe_agent agent1)
{
	while (true) {
		ixgbe_run(&agent0, &agent_packet_handler);
		ixgbe_run(&agent1, &agent_packet_handler);
	}
}

int main(int argc, char** argv)
{
	struct ixgbe_device device0, device1;
	int ret = init(argc, argv, &device0, &device1);
	if (ret != 0) {
		return ret;
	}

	struct ixgbe_agent agent0, agent1;
	if (!ixgbe_agent_init(&device0, 1, &device1, &agent0)) {
		TN_INFO("Could not init agent 0");
		return 6;
	}
	if (!ixgbe_agent_init(&device1, 1, &device0, &agent1)) {
		TN_INFO("Could not init agent 1");
		return 6;
	}

#if TN_MODE == 0
	TN_INFO("TinyNF (agent) initialized successfully!");
#else
	TN_INFO("TinyNF (agent with hardcoded count) initialized successfully!");
#endif

	run(agent0, agent1);
}

#elif TN_MODE == 2

#define TINYNF_QUEUE_BATCH 32
#define TINYNF_QUEUE_POOLSIZE 65536

// I haven't tested if this noinline is also necessary but since it is for the agent case let's just do it
__attribute__((noinline))
noreturn static void run(struct ixgbe_queue_rx* rx0, struct ixgbe_queue_rx* rx1, struct ixgbe_queue_tx* tx0, struct ixgbe_queue_tx* tx1)
{
	struct ixgbe_buffer* buffers[TINYNF_QUEUE_BATCH];
	uint8_t nb_rx, nb_tx;
	while (true) {
		nb_rx = ixgbe_queue_rx_batch(rx0, buffers, TINYNF_QUEUE_BATCH);
		for (size_t n = 0; n < nb_rx; n++) {
			packet_handler(buffers[n]->data->data);
		}
		nb_tx = ixgbe_queue_tx_batch(tx1, buffers, nb_rx);
		for (size_t n = nb_tx; n < nb_rx; n++) {
			// if this fails we're screwed and will stop xmitting packets so don't even check
			ixgbe_buffer_pool_give(tx1->pool, buffers[n]);
		}

		nb_rx = ixgbe_queue_rx_batch(rx1, buffers, TINYNF_QUEUE_BATCH);
		for (size_t n = 0; n < nb_rx; n++) {
			packet_handler(buffers[n]->data->data);
		}
		nb_tx = ixgbe_queue_tx_batch(tx0, buffers, nb_rx);
		for (size_t n = nb_tx; n < nb_rx; n++) {
			ixgbe_buffer_pool_give(tx1->pool, buffers[n]);
		}
	}
}

int main(int argc, char** argv)
{
	struct ixgbe_device device0, device1;
	int ret = init(argc, argv, &device0, &device1);
	if (ret != 0) {
		return ret;
	}

	struct ixgbe_buffer_pool* pool0 = ixgbe_buffer_pool_allocate(TINYNF_QUEUE_POOLSIZE);
	struct ixgbe_buffer_pool* pool1 = ixgbe_buffer_pool_allocate(TINYNF_QUEUE_POOLSIZE);

	struct ixgbe_queue_rx rx0, rx1;
	if (!ixgbe_queue_rx_init(&device0, pool0, &rx0) || !ixgbe_queue_rx_init(&device1, pool1, &rx1)) {
		TN_INFO("Could not init RX");
		return 6;
	}

	// Note the pool inversion, rx0 sends on tx1 so they share a pool and vice-versa
	struct ixgbe_queue_tx tx0, tx1;
	if (!ixgbe_queue_tx_init(&device0, pool1, &tx0) || !ixgbe_queue_tx_init(&device1, pool0, &tx1)) {
		TN_INFO("Could not init TX");
		return 7;
	}

	TN_INFO("TinyNF (queue) initialized successfully!");

	run(&rx0, &rx1, &tx0, &tx1);
}

#else
#error Please set TN_MODE to a supported value, see the code
#endif
