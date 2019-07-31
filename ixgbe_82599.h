#pragma once

#include <stdbool.h>
#include <stdint.h>

#include "os/pci.h"


struct ixgbe_device;
struct ixgbe_pipe;

uint64_t ixgbe_get_ring_size(void);
uint64_t ixgbe_get_packet_size_max(void);

bool ixgbe_device_init(const struct tn_pci_device pci_device, struct ixgbe_device** out_device);
bool ixgbe_device_set_promiscuous(const struct ixgbe_device* device);

bool ixgbe_pipe_init(uintptr_t buffer_phys_addr, struct ixgbe_pipe** out_pipe);
bool ixgbe_pipe_set_receive(struct ixgbe_pipe* pipe, const struct ixgbe_device* device, uint64_t queue_index);
bool ixgbe_pipe_set_send(struct ixgbe_pipe* pipe, const struct ixgbe_device* device, uint64_t queue_index);

void ixgbe_receive(struct ixgbe_pipe* pipe, uint64_t* out_packet_length, uint64_t* out_packet_index);
void ixgbe_send(struct ixgbe_pipe* pipe, uint64_t packet_length);
