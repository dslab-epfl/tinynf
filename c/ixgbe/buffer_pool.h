#pragma once

#include <stdbool.h>
#include <stddef.h>
#include <stdint.h>

#include "env/memory.h"

#include "device.h"



struct ixgbe_buffer
{
	struct ixgbe_packet_data* data;
	uintptr_t phys_addr;
	uint16_t length;
};


struct ixgbe_buffer_pool
{
	struct ixgbe_buffer** buffers;
	uint16_t index;
	uint16_t size;
};


static inline struct ixgbe_buffer_pool* ixgbe_buffer_pool_allocate(size_t size)
{
	struct ixgbe_buffer_pool* pool = tn_mem_allocate(sizeof(struct ixgbe_buffer_pool));
	pool->buffers = tn_mem_allocate(sizeof(struct ixgbe_buffer) * size);
	pool->index = 0;
	pool->size = size;

	struct ixgbe_packet_data* data = tn_mem_allocate(sizeof(struct ixgbe_packet_data) * size);
	for (size_t n = 0; n < size; n++) {
		pool->buffers[n] = tn_mem_allocate(sizeof(struct ixgbe_buffer));
		pool->buffers[n]->data = &(data[n]);
		pool->buffers[n]->phys_addr = tn_mem_virt_to_phys(pool->buffers[n]->data);
		// length remains uninitialized, it'll be set by the driver as needed
	}

	return pool;
}

static inline struct ixgbe_buffer* ixgbe_buffer_pool_take(struct ixgbe_buffer_pool* pool)
{
	if (pool->index == pool->size) {
		return NULL;
	}

	struct ixgbe_buffer* buffer = pool->buffers[pool->index];
	pool->index = pool->index + 1;
	return buffer;
}

static inline bool ixgbe_buffer_pool_give(struct ixgbe_buffer_pool* pool, struct ixgbe_buffer* buffer)
{
	if (pool->index == 0) {
		return false;
	}

	pool->index = pool->index - 1;
	pool->buffers[pool->index] = buffer;
	return true;
}
