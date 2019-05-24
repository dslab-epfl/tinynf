#include <stdint.h>


// Gets the address at which the given device (referred to by its BDF) is memory-mapped,
// ensuring it refers to a block of at least min_length bytes,
// or returns 0 on error.
uint64_t tn_pci_get_device(uint8_t bus, uint8_t device, uint8_t function, uint64_t min_length);

// Reads the given register of the device at the given memory-mapped address.
// This unconventional way to refer to a device is because we want to use
// the memory-mapped address as the main ID to be fast in the common case;
// this operation is slow, and should not be on the fast path.
uint32_t tn_pci_read(uint64_t device_addr, uint8_t reg);
