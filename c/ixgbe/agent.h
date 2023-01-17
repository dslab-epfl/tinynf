#pragma once

// Optionally define IXGBE_AGENT_OUTPUTS_COUNT to a number to hardcode this number instead of using a size stored in the struct
// which is equivalent to constant generics... but obviously less easy to use

#include <stdbool.h>
#include <stddef.h>
#include <stdint.h>

#include "env/endian.h"
#include "env/memory.h"
#include "util/log.h"

#include "device.h"


// Max number of packets before updating the transmit tail (>= 1, and < RING_SIZE)
#define IXGBE_AGENT_FLUSH_PERIOD 8

// Updating period for receiving transmit head updates from the hardware and writing new values of the receive tail based on it (>= 1, < RING_SIZE, and a power of 2 for fast modulo)
#define IXGBE_AGENT_RECYCLE_PERIOD 64


struct ixgbe_agent
{
	volatile struct ixgbe_packet_data* restrict buffers;
	volatile struct ixgbe_descriptor* restrict* rings; // 0 == shared receive/transmit, rest are exclusive transmit
	volatile uint32_t* restrict receive_tail_addr;
	volatile struct ixgbe_transmit_head* restrict transmit_heads;
	volatile uint32_t* restrict* restrict transmit_tail_addrs;
	uint16_t* restrict outputs;
	size_t processed_delimiter;
#ifndef IXGBE_AGENT_OUTPUTS_COUNT
	size_t outputs_count;
#endif
};


static inline bool ixgbe_agent_init(struct ixgbe_device* input_device, size_t outputs_count, struct ixgbe_device* output_devices, struct ixgbe_agent* out_agent)
{
#ifdef IXGBE_AGENT_OUTPUTS_COUNT
	// just so we don't have to change the signature
	if (outputs_count != IXGBE_AGENT_OUTPUTS_COUNT) {
		TN_DEBUG("Wrong number of outputs");
		return false;
	}
#else
	out_agent->outputs_count = outputs_count;
#endif

	if (outputs_count < 1) {
		TN_DEBUG("Too few outputs");
		return false;
	}

	out_agent->buffers = tn_mem_allocate(IXGBE_RING_SIZE * sizeof(struct ixgbe_packet_data));
	out_agent->transmit_heads = tn_mem_allocate(outputs_count * sizeof(struct ixgbe_transmit_head));
	out_agent->rings = tn_mem_allocate(outputs_count * sizeof(struct ixgbe_descriptor*));
	out_agent->transmit_tail_addrs = tn_mem_allocate(outputs_count * sizeof(uint32_t*));
	out_agent->outputs = tn_mem_allocate(outputs_count * sizeof(uint16_t));

	for (size_t r = 0; r < outputs_count; r++) {
		out_agent->rings[r] = tn_mem_allocate(IXGBE_RING_SIZE * sizeof(struct ixgbe_descriptor));
		// Program all descriptors' buffer addresses now
		for (size_t n = 0; n < IXGBE_RING_SIZE; n++) {
			// Section 7.2.3.2.2 Legacy Transmit Descriptor Format:
			// "Buffer Address (64)", 1st line offset 0
			uintptr_t packet_phys_addr = tn_mem_virt_to_phys((void*) &(out_agent->buffers[n]));
			// INTERPRETATION-MISSING: The data sheet does not specify the endianness of descriptor buffer addresses..
			// Since Section 1.5.3 Byte Ordering states "Registers not transferred on the wire are defined in little endian notation.", we will assume they are little-endian.
			out_agent->rings[r][n].addr = tn_cpu_to_le64(packet_phys_addr);
		}
		if (!ixgbe_device_add_output(&(output_devices[r]), (struct ixgbe_descriptor*) out_agent->rings[r], (struct ixgbe_transmit_head*) &(out_agent->transmit_heads[r]), &(out_agent->transmit_tail_addrs[r]))) {
			TN_DEBUG("Could not set input");
			return false;
		}
	}

	if (!ixgbe_device_add_input(input_device, (struct ixgbe_descriptor*) out_agent->rings[0], &(out_agent->receive_tail_addr))) {
		TN_DEBUG("Could not set input");
		return false;
	}

	out_agent->processed_delimiter = 0;

	return true;
}

// --------------
// High-level API
// --------------

typedef void ixgbe_packet_handler(volatile struct ixgbe_packet_data* restrict packet, uint16_t packet_length, uint16_t* restrict outputs);

__attribute__((always_inline))
static inline void ixgbe_run(struct ixgbe_agent* agent, ixgbe_packet_handler* handler)
{
#ifdef IXGBE_AGENT_OUTPUTS_COUNT
#define outs_count IXGBE_AGENT_OUTPUTS_COUNT
#else
#define outs_count agent->outputs_count
#endif

	size_t p;
	for (p = 0; p < IXGBE_AGENT_FLUSH_PERIOD; p++) {
		uint64_t receive_metadata = tn_le_to_cpu64(agent->rings[0][agent->processed_delimiter].metadata);
		if ((receive_metadata & IXGBE_RX_METADATA_DD) == 0) {
			break;
		}

		volatile struct ixgbe_packet_data* restrict packet = &(agent->buffers[agent->processed_delimiter]);
		uint16_t packet_length = IXGBE_RX_METADATA_LENGTH(receive_metadata);
		handler(packet, packet_length, agent->outputs);

		uint64_t rs_bit = (agent->processed_delimiter % IXGBE_AGENT_RECYCLE_PERIOD) == (IXGBE_AGENT_RECYCLE_PERIOD - 1) ? IXGBE_TX_METADATA_RS : 0;
		for (uint64_t n = 0; n < outs_count; n++) {
			agent->rings[n][agent->processed_delimiter].metadata = tn_cpu_to_le64(IXGBE_TX_METADATA_LENGTH(agent->outputs[n]) | rs_bit | IXGBE_TX_METADATA_IFCS | IXGBE_TX_METADATA_EOP);
			agent->outputs[n] = 0;
		}

		agent->processed_delimiter = (agent->processed_delimiter + 1u) % IXGBE_RING_SIZE;

		if (rs_bit != 0) {
			uint32_t earliest_transmit_head = (uint32_t) agent->processed_delimiter;
			uint64_t min_diff = (uint64_t) -1;
			for (uint64_t n = 0; n < outs_count; n++) {
				uint32_t head = tn_le_to_cpu32(agent->transmit_heads[n].value);
				uint64_t diff = head - agent->processed_delimiter;
				if (diff <= min_diff) {
					earliest_transmit_head = head;
					min_diff = diff;
				}
			}

			reg_write_raw(agent->receive_tail_addr, earliest_transmit_head);
		}
	}
	if (p != 0) {
		for (uint64_t n = 0; n < outs_count; n++) {
			reg_write_raw(agent->transmit_tail_addrs[n], (uint32_t) agent->processed_delimiter);
		}
	}
}
