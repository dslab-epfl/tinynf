#pragma once

#include <stdbool.h>
#include <stdint.h>
#include <stdnoreturn.h>

#include "os/memory.h"
#include "os/pci.h"


struct ixgbe_device;
struct ixgbe_pipe;

// Returns the new length of the packet, and sets send_list[N] = true iff the packet should be sent on queue N
// (queues are in the order they were added)
typedef uint64_t ixgbe_packet_handler(uint8_t* packet, uint64_t packet_length, bool* send_list);

uint64_t ixgbe_get_ring_size(void);
uint64_t ixgbe_get_packet_size_max(void);

bool ixgbe_device_init(struct tn_pci_device pci_device, struct ixgbe_device** out_device);
bool ixgbe_device_set_promiscuous(const struct ixgbe_device* device);

bool ixgbe_pipe_init(struct tn_memory_block buffer, struct ixgbe_pipe** out_pipe);
bool ixgbe_pipe_set_receive(struct ixgbe_pipe* pipe, const struct ixgbe_device* device, uint64_t queue_index);
bool ixgbe_pipe_add_send(struct ixgbe_pipe* pipe, const struct ixgbe_device* device, uint64_t queue_index);
noreturn void ixgbe_pipe_run(struct ixgbe_pipe* pipe, ixgbe_packet_handler* handler);
