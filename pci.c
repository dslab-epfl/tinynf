#include "pci.h"
#include "filesystem.h"

#include <inttypes.h>
#include <stdbool.h>
#include <stddef.h>
#include <stdlib.h>
#include <unistd.h>

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
	uintptr_t address;
};
// 16 known devices should be more than enough
struct tn_pci_device tn_pci_known_devices[16];
bool tn_pci_got_ioperm;


// TODO uniformize naming
uintptr_t tn_pci_get_device_address(const uint8_t bus, const uint8_t device, const uint8_t function, const uint64_t min_length)
{
	uintptr_t dev_addr = 0;
	const char* dev_resource_line = NULL;

	// Make sure we can talk to the devices
	// Note that we need access to port 0x80 in order to use the _p version of inl/outl
	// Also note that since reading an int32 is 4 bytes, we need to access 4 consecutive ports for PCI config/data.
	if (!tn_pci_got_ioperm) {
		if (ioperm(0x80, 1, 1) < 0 || ioperm(PCI_CONFIG_ADDR, 4, 1) < 0 || ioperm(PCI_CONFIG_DATA, 4, 1) < 0) {
			goto error;
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
		goto error;
	}

	// Read the first line of the PCI /resource file, as a sanity check + indication of the length of the resource
	dev_resource_line = tn_fs_readline("/sys/bus/pci/devices/0000:%02"PRIx8":%02"PRIx8".%"PRIx8"/resource", bus, device, function);
	if (dev_resource_line == NULL) {
		goto error;
	}
	// We expect 3 64-bit hex numbers (2 chars prefix, 16 chars number), 2 spaces, 1 newline, 1 NULL char == 58
	// e.g. 0x00003800ffa80000 0x00003800ffafffff 0x000000000014220c
	if (dev_resource_line[56] != '\n') {
		// Somehow we didn't read exactly the line format we were expecting
		goto error;
	}
	const uint64_t dev_phys_addr = strtoull(dev_resource_line, NULL, 16);
	// Offset to 2nd number: 18-char number + 1 space
	const uint64_t dev_phys_addr_end = strtoull(dev_resource_line + 18 + 1, NULL, 16);
	const uint64_t dev_phys_length = (dev_phys_addr_end - dev_phys_addr + 1);
	if (dev_phys_length < min_length) {
		// Not enough memory given what was expected
		goto error;
	}
	// Offset to 3rd number: 2 * (18-char number + 1 space)
	const uint64_t dev_resource_flags = strtoull(dev_resource_line + 2 * (18 + 1), NULL, 16);
	if ((dev_resource_flags & 0x200) == 0) {
		// For some reason the first line is not a memory one; just abort...
		goto error;
	}

	// Now map the /resource0 file so we can access it
	dev_addr = tn_fs_mmap("/sys/bus/pci/devices/0000:%02"PRIx8":%02"PRIx8".%"PRIx8"/resource0", bus, device, function);
	if (dev_addr == (uintptr_t) -1) {
		goto error;
	}

	// Store the device info
	dev->bus = bus;
	dev->device = device;
	dev->function = function;
	dev->address = dev_addr;

error:
	free((void*) dev_resource_line);
	return dev_addr;
}

uint32_t tn_pci_read(const uintptr_t device_address, const uint8_t reg)
{
	const struct tn_pci_device* dev = NULL;
	for (size_t n = 0; n < sizeof(tn_pci_known_devices)/sizeof(struct tn_pci_device); n++) {
		if (tn_pci_known_devices[n].address == device_address) {
			dev = &tn_pci_known_devices[n];
		}
	}
	if (dev == NULL) {
		// Device not found. Return all-1s, which is what PCI would return in that case.
		return 0xFFFFFFFF;
	}

	const uint32_t value = 0x80000000 | ((uint32_t)dev->bus << 16) | ((uint32_t)dev->device << 11) | ((uint32_t)dev->function << 8) | reg;
	outl_p(value, PCI_CONFIG_ADDR);
	return inl_p(PCI_CONFIG_DATA);
}
