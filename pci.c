#include "pci.h"
#include "filesystem.h"

#include <inttypes.h>
#include <stdbool.h>
#include <stddef.h>
#include <stdlib.h>
#include <sys/io.h>


// Physical addresses at which we can talk to PCI via geographical addressing
#define PCI_CONFIG_ADDR 0xCF8
#define PCI_CONFIG_DATA 0xCFC

// We store known PCI devices so that we can implement the tn_pci_read function since it refers to devices by their memory-mapped address.
struct tn_pci_device {
	uint8_t bus;
	uint8_t device;
	uint8_t function;
	// We assume that a correct memory address is never 0
	uint64_t address;
};
// 16 known devices should be more than enough
struct tn_pci_device tn_pci_known_devices[16];
bool tn_pci_got_ioperm;


uint64_t tn_pci_get_device(uint8_t bus, uint8_t device, uint8_t function, uint64_t min_length)
{
	// Make sure we can talk to the devices
	if (!tn_pci_got_ioperm) {
		if (ioperm(PCI_CONFIG_ADDR, 1, 1) < 0 || ioperm(PCI_CONFIG_DATA, 1, 1) < 0) {
			return 0;
		}
		tn_pci_got_ioperm = true;
	}

	// Find which slot we'll save the memory-mapped address in
	struct tn_pci_device* dev = NULL;
	for (size_t n = 0; n < sizeof(tn_pci_known_devices)/sizeof(struct tn_pci_device); n++) {
		if (tn_pci_known_devices[n].address == 0) {
			dev = &tn_pci_known_devices[n];
		}
	}
	if (dev == NULL) {
		// No more space!
		return 0;
	}

	char* dev_resource_line = tn_fs_readline("/sys/bus/pci/devices/0000:%02"PRIx8":%02"PRIx8".%"PRIx8"/resource", bus, device, function);
	if (dev_resource_line == NULL) {
		goto error;
	}

	// We expect 3 64-bit hex numbers (2 chars prefix, 16 chars number), 2 spaces, 1 newline, 1 NULL char == 58
	// e.g. 0x00003800ffa80000 0x00003800ffafffff 0x000000000014220c
	if (dev_resource_line[56] != '\n') {
		// Somehow we didn't read exactly the line format we were expecting
		goto error;
	}

	uint64_t dev_addr = strtoull(dev_resource_line, NULL, 16);
	// Offset to 2nd number: 18-char number + 1 space
	uint64_t dev_addr_end = strtoull(dev_resource_line + 18 + 1, NULL, 16);
	// Offset to 3rd number: 2 * (18-char number + 1 space)
	uint64_t dev_resource_flags = strtoull(dev_resource_line + 2 * (18 + 1), NULL, 16);

	if (dev_addr_end - dev_addr <= min_length) {
		// Not enough memory given what was expected
		goto error;
	}

	if ((dev_resource_flags & 0x200) == 0) {
		// For some reason the first line is not a memory one; just abort...
		goto error;
	}

	free(dev_resource_line);

	// Store the device info
	dev->bus = bus;
	dev->device = device;
	dev->function = function;
	dev->address = dev_addr;

	return dev_addr;

error:
	free(dev_resource_line);
	return 0;
}

uint32_t tn_pci_read(uint64_t device_addr, uint8_t reg)
{
	struct tn_pci_device* dev = NULL;
	for (size_t n = 0; n < sizeof(tn_pci_known_devices)/sizeof(struct tn_pci_device); n++) {
		if (tn_pci_known_devices[n].address == device_addr) {
			dev = &tn_pci_known_devices[n];
		}
	}
	if (dev == NULL) {
		// Device not found. Return all-1s, which is what PCI would return in that case.
		return 0xFFFFFFFF;
	}

	uint32_t value = 0x80000000 | (dev->bus << 16) | (dev->device << 11) | (dev->function << 8) | reg;
	outl(value, PCI_CONFIG_ADDR);
	return inl(PCI_CONFIG_DATA);
}
