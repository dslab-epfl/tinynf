// PCI configuration space reads and writes
// https://en.wikipedia.org/wiki/PCI_configuration_space

#pragma once

#include <stdint.h>


struct tn_pci_address {
	uint8_t bus;
	uint8_t device;
	uint8_t function;
	uint8_t _padding[5];
};


// Reads the given register of the device at the given address and return its value.
uint32_t tn_pci_read(struct tn_pci_address address, uint8_t reg);

// Writes the given value to the given register of the device at the given address
void tn_pci_write(struct tn_pci_address address, uint8_t reg, uint32_t value);
