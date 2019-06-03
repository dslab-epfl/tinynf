#pragma once

#include <stdbool.h>
#include <stdint.h>


// Section 8.2.3.8.3 Receive Descriptor Length: "Validated lengths up to 128 K (8 K descriptors)."
const uint16_t IXGBE_RECEIVE_RING_SIZE_MAX = 8 * 1024;

// Section 8.2.3.8.7 Split Receive Control Registers: "Receive Buffer Size for Packet Buffer. Value can be from 1 KB to 16 KB"
const uint16_t IXGBE_RECEIVE_PACKET_SIZE_MAX = 16 * 1024;


bool ixgbe_device_init(uintptr_t addr);

// Initializes the given receive queue for the device at the given address,
// using the given ring address/size and buffer for packets.
// The ring size must be a multiple of 8.
bool ixgbe_device_init_receive(uintptr_t addr, uint8_t queue, uintptr_t ring_addr, uint16_t ring_size, uintptr_t buffer_addr);

bool ixgbe_device_init_send(uintptr_t addr, uint8_t queue);
