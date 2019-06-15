#pragma once

#include <stdbool.h>
#include <stdint.h>


extern const uint16_t IXGBE_RING_SIZE;
extern const uint16_t IXGBE_PACKET_SIZE_MAX;


bool ixgbe_device_init(uintptr_t addr);

bool ixgbe_device_set_promiscuous(uintptr_t addr);

// Initializes the given receive queue for the device at the given address,
// using the given ring address/size and buffer for packets.
// The ring size must be a multiple of 8.
bool ixgbe_device_init_receive(uintptr_t addr, uint8_t queue, uintptr_t ring_addr, uintptr_t buffer_addr);

bool ixgbe_device_init_send(uintptr_t addr, uint8_t queue, uintptr_t ring_addr, uintptr_t buffer_addr);

// TODO REMOVE
void ixgbe_sanity_check(uintptr_t addr);
void ixgbe_stats_reset(const uintptr_t addr);
void ixgbe_stats_probe(const uintptr_t addr);
