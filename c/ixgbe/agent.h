#pragma once

// TODO: The "unsafe" version should be controlled by #include-ing this with a predefined macro, instead of a global compile switch that makes code look weird

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
	uint8_t* buffer;
	volatile struct ixgbe_descriptor** rings; // 0 == shared receive/transmit, rest are exclusive transmit
	uint32_t* receive_tail_addr;
	uint8_t processed_delimiter;
	uint8_t _padding[7]; // for alignment of transmit_heads
	volatile struct ixgbe_transmit_head* transmit_heads;
	uint32_t** transmit_tail_addrs;
	uint16_t* outputs;
#ifndef DANGEROUS
	size_t outputs_count;
#endif
};


static inline bool ixgbe_agent_init(struct ixgbe_device* input_device, size_t outputs_count, struct ixgbe_device* output_devices, struct ixgbe_agent* out_agent)
{
	if (outputs_count < 1) {
		TN_DEBUG("Too few outputs");
		return false;
	}

	if (!tn_mem_allocate(IXGBE_RING_SIZE * PACKET_BUFFER_SIZE, (void**) &(out_agent->buffer))) {
		TN_DEBUG("Could not allocate buffer for agent");
		return false;
	}

	if (!tn_mem_allocate(outputs_count * sizeof(struct ixgbe_transmit_head), (void**) &(out_agent->transmit_heads))) {
		TN_DEBUG("Could not allocate transmit heads for agent");
		return false;
	}

	if (!tn_mem_allocate(outputs_count * sizeof(struct ixgbe_descriptor*), (void**) &(out_agent->rings))) {
		TN_DEBUG("Could not allocate rings for agent");
		return false;
	}

	if (!tn_mem_allocate(outputs_count * sizeof(uint32_t*), (void**) &(out_agent->transmit_tail_addrs))) {
		TN_DEBUG("Could not allocate transmit tail addrs for agent");
		return false;
	}

	if (!tn_mem_allocate(outputs_count * sizeof(uint16_t), (void**) &(out_agent->outputs))) {
		TN_DEBUG("Could not allocate outputs for agent");
		return false;
	}

	for (size_t r = 0; r < outputs_count; r++) {
		if (!tn_mem_allocate(IXGBE_RING_SIZE * sizeof(struct ixgbe_descriptor), (void**) &(out_agent->rings[r]))) { // 16 bytes per descriptor, i.e. 2x64bits
			TN_DEBUG("Could not allocate ring");
			return false;
		}
		// Program all descriptors' buffer addresses now
		for (size_t n = 0; n < IXGBE_RING_SIZE; n++) {
			// Section 7.2.3.2.2 Legacy Transmit Descriptor Format:
			// "Buffer Address (64)", 1st line offset 0
			void* packet_addr = out_agent->buffer + n * PACKET_BUFFER_SIZE;
			uintptr_t packet_phys_addr;
			if (!tn_mem_virt_to_phys(packet_addr, &packet_phys_addr)) {
				TN_DEBUG("Could not get a packet's physical address");
				return false;
			}

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

#ifndef DANGEROUS
	out_agent->outputs_count = outputs_count;
#endif

	return true;
}

// --------------
// High-level API
// --------------

typedef void ixgbe_packet_handler(volatile uint8_t* packet, uint16_t packet_length, uint16_t* outputs);

__attribute__((always_inline)) inline
static void ixgbe_run(struct ixgbe_agent* agent, ixgbe_packet_handler* handler
#ifdef DANGEROUS
, size_t outs_count
#else
#define outs_count agent->outputs_count
#endif
)
{
	size_t p;
	for (p = 0; p < IXGBE_AGENT_FLUSH_PERIOD; p++) {
		uint64_t receive_metadata = tn_le_to_cpu64(agent->rings[0][agent->processed_delimiter].metadata);
		if ((receive_metadata & BITL(32)) == 0) {
			break;
		}

		uint8_t* packet = agent->buffer + (PACKET_BUFFER_SIZE * agent->processed_delimiter);
		uint16_t packet_length = receive_metadata & 0xFFFFu;
		handler(packet, packet_length, agent->outputs);

		uint64_t rs_bit = (agent->processed_delimiter & (IXGBE_AGENT_RECYCLE_PERIOD - 1)) == (IXGBE_AGENT_RECYCLE_PERIOD - 1) ? BITL(24+3) : 0;
		for (uint64_t n = 0; n < outs_count; n++) {
			agent->rings[n][agent->processed_delimiter].metadata = tn_cpu_to_le64(((uint64_t) agent->outputs[n]) | rs_bit | BITL(24+1) | BITL(24));
			agent->outputs[n] = 0;
		}

		agent->processed_delimiter = (agent->processed_delimiter + 1u) & (IXGBE_RING_SIZE - 1);

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

			reg_write_raw(agent->receive_tail_addr, (earliest_transmit_head - 1) & (IXGBE_RING_SIZE - 1));
		}
	}
	if (p != 0) {
		for (uint64_t n = 0; n < outs_count; n++) {
			reg_write_raw(agent->transmit_tail_addrs[n], (uint32_t) agent->processed_delimiter);
		}
	}
}
