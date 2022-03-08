#pragma once

#include <stdbool.h>
#include <stddef.h>
#include <stdint.h>

#include "env/memory.h"

#include "device.h"

// This implementation uses optimistic logic in `give` so that when ported to safe languages without ranged integers compilers are allowed to elide bounds checks.
// The cost is an extra decrement operation if `give` fails, which is not expected to happen since that means giving more buffers than one has taken.
// Of course, having `index` be in the range `0 .. size` would be better, but not all languages have cool features :-)


struct ixgbe_buffer
{
	volatile struct ixgbe_packet_data* data;
	uintptr_t phys_addr;
	uint16_t length;
};


struct ixgbe_buffer_pool
{
	struct ixgbe_buffer* restrict* buffers;
	size_t size;
	size_t index;
};


static inline struct ixgbe_buffer_pool* ixgbe_buffer_pool_allocate(size_t size)
{
	struct ixgbe_buffer_pool* pool = tn_mem_allocate(sizeof(struct ixgbe_buffer_pool));
	pool->buffers = tn_mem_allocate(sizeof(struct ixgbe_buffer) * size);
	pool->size = size;
	pool->index = size - 1; // == full

	struct ixgbe_packet_data* data = tn_mem_allocate(sizeof(struct ixgbe_packet_data) * size);
	for (size_t n = 0; n < size; n++) {
		pool->buffers[n] = tn_mem_allocate(sizeof(struct ixgbe_buffer));
		pool->buffers[n]->data = &(data[n]);
		pool->buffers[n]->phys_addr = tn_mem_virt_to_phys((void*) pool->buffers[n]->data);
		// length remains uninitialized, it'll be set by the driver as needed
	}

	return pool;
}

static inline bool ixgbe_buffer_pool_give(struct ixgbe_buffer_pool* pool, struct ixgbe_buffer* buffer)
{
	pool->index++;
	if (pool->index < pool->size) {
		pool->buffers[pool->index] = buffer;
		return true;
	}

	pool->index--;
	return false;
}

static inline struct ixgbe_buffer* ixgbe_buffer_pool_take(struct ixgbe_buffer_pool* pool)
{
	if (pool->index < pool->size) {
		struct ixgbe_buffer* buffer = pool->buffers[pool->index];
		pool->index--;
		return buffer;
	}

	return NULL;
}
