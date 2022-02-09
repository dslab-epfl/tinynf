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
	uint8_t rx_count = 0;
	while (rx_count < buffers_count) {
		uint64_t metadata = tn_le_to_cpu64(queue->ring[queue->next].metadata);
		if ((metadata & IXGBE_RX_METADATA_DD) == 0) {
			break;
		}

		struct ixgbe_buffer* new_buffer = ixgbe_buffer_pool_take(queue->pool);
		if (new_buffer == NULL) {
			break;
		}

		buffers[rx_count] = queue->buffers[queue->next];
		buffers[rx_count]->length = IXGBE_RX_METADATA_LENGTH(metadata);

		queue->buffers[queue->next] = new_buffer;
		queue->ring[queue->next].addr = tn_cpu_to_le64(new_buffer->phys_addr);
		queue->ring[queue->next].metadata = tn_cpu_to_le64(0);

		queue->next++;
		rx_count++;
	}
	if (rx_count > 0) {
		reg_write_raw(queue->receive_tail_addr, queue->next);
	}
	return rx_count;
}


#define IXGBE_QUEUE_TX_RECYCLE_PERIOD 32

struct ixgbe_queue_tx {
	struct ixgbe_descriptor* ring;
	struct ixgbe_buffer** buffers; // kept in sync with ring
	struct ixgbe_buffer_pool* pool;
	uint32_t* transmit_head_addr;
	uint32_t* transmit_tail_addr;
	uint8_t transmit_head; // where we last saw it, to avoid expensive HW reads
	uint8_t next;
};

static inline bool ixgbe_queue_tx_init(struct ixgbe_device* device, struct ixgbe_buffer_pool* pool, struct ixgbe_queue_tx* out_queue) {
	// TODO
}

static inline uint8_t ixgbe_queue_tx_batch(struct ixgbe_queue_tx* queue, struct ixgbe_buffer** buffers, uint8_t buffers_count) {
	// 2* period so we are much more likely to recycle something since the last "batch" before an RS bit was likely not fully sent yet
	if (queue->transmit_head - queue->next >= 2 * IXGBE_QUEUE_TX_RECYCLE_PERIOD) {
		uint32_t actual_transmit_head = reg_read_raw(queue->transmit_head_addr);
		while (queue->transmit_head < actual_transmit_head) {
			if (!ixgbe_buffer_pool_give(queue->pool, queue->buffers[queue->transmit_head])) {
				break;
			}
			queue->transmit_head++;
		}
	}

	uint8_t tx_count = 0;
	while (tx_count < buffers_count) {
		// don't overwrite buffers not yet transmitted
		// -1 is necessary since they will be equal when all buffers are transmitted (e.g. at the start when no buffers need transmission)
		if (queue->next == queue->transmit_head - 1) {
			break;
		}

		uint64_t rs_bit = (queue->next & (IXGBE_QUEUE_TX_RECYCLE_PERIOD - 1)) == (IXGBE_QUEUE_TX_RECYCLE_PERIOD - 1) ? IXGBE_TX_METADATA_RS : 0;
		queue->ring[queue->next].addr = tn_cpu_to_le64(buffers[tx_count]->phys_addr);
		queue->ring[queue->next].metadata = tn_cpu_to_le64(IXGBE_TX_METADATA_LENGTH(buffers[tx_count]->length) | rs_bit | IXGBE_TX_METADATA_IFCS | IXGBE_TX_METADATA_EOP);

		queue->buffers[queue->next] = buffers[tx_count];

		queue->next++;
		tx_count++;
	}
	if (tx_count > 0) {
		reg_write_raw(queue->transmit_tail_addr, queue->next);
	}
	return tx_count;
}
