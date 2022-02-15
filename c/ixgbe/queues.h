#pragma once

#include <stdbool.h>
#include <stdint.h>
#include <stddef.h>

#include "buffer_pool.h"
#include "device.h"


struct ixgbe_queue_rx
{
	volatile struct ixgbe_descriptor* restrict ring;
	struct ixgbe_buffer* restrict* buffers; // kept in sync with ring
	struct ixgbe_buffer_pool* pool;
	volatile uint32_t* restrict receive_tail_addr;
	uint8_t next; // TODO size_t? (also for tx)
};

static inline bool ixgbe_queue_rx_init(struct ixgbe_device* device, struct ixgbe_buffer_pool* pool, struct ixgbe_queue_rx* out_queue)
{
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

static inline uint8_t ixgbe_queue_rx_batch(struct ixgbe_queue_rx* queue, struct ixgbe_buffer* restrict* buffers, uint8_t buffers_count)
{
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

		queue->next = (queue->next + 1u) % IXGBE_RING_SIZE;
		rx_count++;
	}
	if (rx_count > 0) {
		// -1 because queue->next might be RDH at this point, and RDT==RDH means all packets are software-owned so no further RX which we must avoid
		reg_write_raw(queue->receive_tail_addr, (queue->next - 1u) % IXGBE_RING_SIZE);
	}
	return rx_count;
}


#define IXGBE_QUEUE_TX_RECYCLE_PERIOD 32u

struct ixgbe_queue_tx
{
	volatile struct ixgbe_descriptor* restrict ring;
	struct ixgbe_buffer* restrict* buffers; // kept in sync with ring
	struct ixgbe_buffer_pool* pool;
	volatile struct ixgbe_transmit_head* restrict transmit_head_addr;
	volatile uint32_t* restrict transmit_tail_addr;
	uint8_t recycled_head; // where we last saw the transmit head
	uint8_t next;
};

static inline bool ixgbe_queue_tx_init(struct ixgbe_device* device, struct ixgbe_buffer_pool* pool, struct ixgbe_queue_tx* out_queue)
{
	out_queue->ring = tn_mem_allocate(sizeof(struct ixgbe_descriptor) * IXGBE_RING_SIZE);
	out_queue->buffers = tn_mem_allocate(sizeof(struct ixgbe_buffer*) * IXGBE_RING_SIZE);
	out_queue->pool = pool;
	out_queue->transmit_head_addr = tn_mem_allocate(sizeof(struct ixgbe_transmit_head));
	out_queue->recycled_head = 0;
	out_queue->next = 0;
	return ixgbe_device_add_output(device, out_queue->ring, out_queue->transmit_head_addr, &(out_queue->transmit_tail_addr));
}

static inline uint8_t ixgbe_queue_tx_batch(struct ixgbe_queue_tx* queue, struct ixgbe_buffer* restrict* buffers, uint8_t buffers_count)
{
	// 2* period so we are much more likely to recycle something since the last "batch" before an RS bit was likely not fully sent yet
	if ((uint8_t) (queue->next - queue->recycled_head) >= 2 * IXGBE_QUEUE_TX_RECYCLE_PERIOD) {
		uint32_t actual_transmit_head = queue->transmit_head_addr->value;
		// !=, not <, since it's really "< modulo ring size"
		while (queue->recycled_head != actual_transmit_head) {
			if (!ixgbe_buffer_pool_give(queue->pool, queue->buffers[queue->recycled_head])) {
				break;
			}
			queue->recycled_head = (queue->recycled_head + 1u) % IXGBE_RING_SIZE;
		}
	}

	uint8_t tx_count = 0;
	while (tx_count < buffers_count) {
		// don't overwrite buffers not yet transmitted
		// -1 is necessary since they will be equal when all buffers are transmitted (e.g. at the start when no buffers need transmission)
		if (queue->next == queue->recycled_head - 1) {
			break;
		}

		uint64_t rs_bit = (queue->next % IXGBE_QUEUE_TX_RECYCLE_PERIOD) == (IXGBE_QUEUE_TX_RECYCLE_PERIOD - 1) ? IXGBE_TX_METADATA_RS : 0;
		queue->ring[queue->next].addr = tn_cpu_to_le64(buffers[tx_count]->phys_addr);
		queue->ring[queue->next].metadata = tn_cpu_to_le64(IXGBE_TX_METADATA_LENGTH(buffers[tx_count]->length) | rs_bit | IXGBE_TX_METADATA_IFCS | IXGBE_TX_METADATA_EOP);

		queue->buffers[queue->next] = buffers[tx_count];

		queue->next = (queue->next + 1u) % IXGBE_RING_SIZE;
		tx_count++;
	}
	if (tx_count > 0) {
		reg_write_raw(queue->transmit_tail_addr, queue->next);
	}
	return tx_count;
}
