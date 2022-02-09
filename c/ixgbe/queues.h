#pragma once

#include <stdbool.h>
#include <stdint.h>
#include <stddef.h>

#include "buffer_pool.h"
#include "device.h"


struct ixgbe_queue_rx {
	struct ixgbe_descriptor* ring;
	struct ixgbe_buffer** buffers; // kept in sync with ring
	struct ixgbe_buffer_pool* pool;
	uint32_t* receive_tail_addr;
	uint8_t next;
};

static inline bool ixgbe_queue_rx_init(struct ixgbe_device* device, struct ixgbe_buffer_pool* pool, struct ixgbe_queue_rx* out_queue) {
	out_queue->ring = tn_mem_allocate(sizeof(struct ixgbe_descriptor) * IXGBE_RING_SIZE);
	out_queue->buffers = tn_mem_allocate(sizeof(struct ixgbe_buffer*) * IXGBE_RING_SIZE);
	out_queue->pool = pool;
	out_queue->next = 0;
	for (size_t n = 0; n < IXGBE_RING_SIZE; n++) {
		// not cleaned up if we fail later #ResearchCode
		out_queue->buffers[n] = ixgbe_buffer_pool_take(out_queue->pool);
		if (out_queue->buffers[n] == NULL) {
			return false;
		}
		out_queue->ring[n].addr = out_queue->buffers[n]->phys_addr;
		out_queue->ring[n].metadata = 0;
	}
	if (!ixgbe_device_add_input(device, out_queue->ring, &(out_queue->receive_tail_addr))) {
		return false;
	}
	reg_write_raw(out_queue->receive_tail_addr, IXGBE_RING_SIZE - 1);
	return true;
}

static inline uint8_t ixgbe_queue_rx_batch(struct ixgbe_queue_rx* queue, struct ixgbe_buffer** buffers, uint8_t buffers_count) {
	uint8_t returned_count = 0;
	while (returned_count < buffers_count) {
		uint64_t metadata = queue->ring[queue->next].metadata;
		if ((metadata & IXGBE_RX_METADATA_DD) == 0) {
			break;
		}

		struct ixgbe_buffer* new_buffer = ixgbe_buffer_pool_take(queue->pool);
		if (new_buffer == NULL) {
			break;
		}

		buffers[returned_count] = queue->buffers[queue->next];
		buffers[returned_count]->length = IXGBE_RX_METADATA_LENGTH(metadata);

		queue->buffers[queue->next] = new_buffer;
		queue->ring[queue->next].addr = new_buffer->phys_addr;
		queue->ring[queue->next].metadata = 0;

		queue->next++;
		returned_count++;
	}

	if (returned_count > 0) {
		reg_write_raw(queue->receive_tail_addr, queue->next);
	}
	return returned_count;
}
