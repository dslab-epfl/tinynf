#pragma once

#include <stdbool.h>
#include <stdint.h>

#include "os/pci.h"


extern const uint32_t IXGBE_RING_SIZE;
extern const uint32_t IXGBE_PACKET_SIZE_MAX;

struct ixgbe_device;
struct ixgbe_queue;

bool ixgbe_device_get(struct tn_pci_device pci_device, struct ixgbe_device** out_device);
bool ixgbe_device_init(const struct ixgbe_device* device);
bool ixgbe_device_set_promiscuous(const struct ixgbe_device* device);

bool ixgbe_device_init_receive_queue(const struct ixgbe_device* device, uint8_t queue_index, uintptr_t buffer_phys_addr, struct ixgbe_queue** out_queue);
bool ixgbe_device_init_send_queue(const struct ixgbe_device* device, uint8_t queue_index, uintptr_t buffer_phys_addr, struct ixgbe_queue** out_queue);

uint16_t ixgbe_receive(struct ixgbe_queue* queue);
void ixgbe_send(struct ixgbe_queue* queue, uint16_t packet_length);

// TODO REMOVE
void ixgbe_sanity_check(uintptr_t addr);
void ixgbe_stats_reset(const uintptr_t addr);
void ixgbe_stats_probe(const uintptr_t addr);
