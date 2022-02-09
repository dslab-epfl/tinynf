#pragma once

#include <stdbool.h>
#include <stdint.h>
#include <stddef.h>

#include "buffer_pool.h"
#include "device.h"


struct ixgbe_queue_rx {
	struct ixgbe_descriptor* ring;
	struct ixgbe_buffer** buffers;
	struct ixgbe_buffer_pool* pool;
	uint32_t* receive_tail_addr;
	uint8_t next;
};

static inline struct ixgbe_rx_queue* ixgbe_queue_rx_init(struct ixgbe_device* device, uint8_t queue_index, struct ixgbe_buffer_pool* pool) {
	// TODO
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
		reg_write_raw(queue->receive_tail_addr, (uint8_t) (queue->next - 1));
	}
	return returned_count;
}
