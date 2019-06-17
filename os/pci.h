#pragma once

#include <stdint.h>


// Gets the address at which the given device (referred to by its BDF) is memory-mapped,
// ensuring it refers to a block of at least min_length bytes,
// or returns 0 on error.
uintptr_t tn_pci_get_device_address(uint8_t bus, uint8_t device, uint8_t function, uint64_t min_length);

// Reads the given register of the given device (referred to by its BDF).
uint32_t tn_pci_read(uint8_t bus, uint8_t device, uint8_t function, uint8_t reg);
