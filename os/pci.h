#pragma once

#include <stdbool.h>
#include <stdint.h>


struct tn_pci_device {
	uint8_t bus;
	uint8_t device;
	uint8_t function;
	uint8_t _padding[5];
};


// Reads the given register of the given device.
uint32_t tn_pci_read(struct tn_pci_device device, uint8_t reg);

// Writes the given value to the given register of the given device
void tn_pci_write(struct tn_pci_device device, uint8_t reg, uint32_t value);
