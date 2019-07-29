#include "os/pci.h"

#include "os/linux/filesystem.h"
#include "util/log.h"

#include <inttypes.h>
#include <stdbool.h>
#include <stddef.h>
#include <stdlib.h>
#include <unistd.h>

#include <sys/io.h>

// Physical addresses at which we can talk to PCI via geographical addressing
#define PCI_CONFIG_ADDR 0xCF8
#define PCI_CONFIG_DATA 0xCFC


bool tn_pci_get_device_node(const struct tn_pci_device device, node_t* out_node)
{
	const char* node_str = tn_fs_readline("/sys/bus/pci/devices/0000:%02"PRIx8":%02"PRIx8".%"PRIx8"/numa_node", device.bus, device.device, device.function);
	if (node_str == NULL) {
		TN_DEBUG("Could not read PCI numa node");
		return false;
	}

	const char node_chr = node_str[0];
	const char node_delim = node_str[1];

	// TODO helper method to free const pointers, and to access memory in general
	free((void*)(uintptr_t)node_str);

	if (node_delim != '\n') {
		TN_DEBUG("Long NUMA node, not supported");
		return false;
	}
	if (node_chr < '0' || node_chr > '9') {
		TN_DEBUG("Unknown NUMA node encoding");
		return false;
	}

	*out_node = (node_t) (node_chr - '0');
	return true;
}

bool tn_pci_mmap_device(const struct tn_pci_device device, const uint64_t min_length, uintptr_t* out_addr)
{
	uintptr_t dev_addr = (uintptr_t) -1;
	const char* dev_resource_line = NULL;

	// Make sure we can talk to the devices
	// Note that we need access to port 0x80 in order to use the _p version of inl/outl
	// Also note that since reading an int32 is 4 bytes, we need to access 4 consecutive ports for PCI config/data.
	static bool tn_pci_got_ioperm = false;
	if (!tn_pci_got_ioperm) {
		if (ioperm(0x80, 1, 1) < 0 || ioperm(PCI_CONFIG_ADDR, 4, 1) < 0 || ioperm(PCI_CONFIG_DATA, 4, 1) < 0) {
			TN_DEBUG("PCI ioperms failed");
			goto end;
		}
		tn_pci_got_ioperm = true;
	}

	// Read the first line of the PCI /resource file, as a sanity check + indication of the length of the resource
	dev_resource_line = tn_fs_readline("/sys/bus/pci/devices/0000:%02"PRIx8":%02"PRIx8".%"PRIx8"/resource", device.bus, device.device, device.function);
	if (dev_resource_line == NULL) {
		TN_DEBUG("Could not read PCI resource line");
		goto end;
	}
	// We expect 3 64-bit hex numbers (2 chars prefix, 16 chars number), 2 spaces, 1 newline, 1 NULL char == 58
	// e.g. 0x00003800ffa80000 0x00003800ffafffff 0x000000000014220c
	if (dev_resource_line[56] != '\n') {
		TN_DEBUG("Unexpected PCI resource line format");
		goto end;
	}
	const uint64_t dev_phys_addr = strtoull(dev_resource_line, NULL, 16);
	// Offset to 2nd number: 18-char number + 1 space
	const uint64_t dev_phys_addr_end = strtoull(dev_resource_line + 18 + 1, NULL, 16);
	const uint64_t dev_phys_length = (dev_phys_addr_end - dev_phys_addr + 1);
	if (dev_phys_length < min_length) {
		TN_DEBUG("Not enough PCI memory, expected at least %" PRIu64 " but got %" PRIu64, min_length, dev_phys_length);
		goto end;
	}
	// Offset to 3rd number: 2 * (18-char number + 1 space)
	const uint64_t dev_resource_flags = strtoull(dev_resource_line + 2 * (18 + 1), NULL, 16);
	if ((dev_resource_flags & 0x200) == 0) {
		TN_DEBUG("First PCI line is not memory");
		goto end;
	}

	// Now map the /resource0 file so we can access it
	dev_addr = tn_fs_mmap("/sys/bus/pci/devices/0000:%02"PRIx8":%02"PRIx8".%"PRIx8"/resource0", device.bus, device.device, device.function);

end:
	// This odd casting is required to free a const pointer without warnings
	free((void*)(uintptr_t)dev_resource_line);
	if (dev_addr == (uintptr_t) -1) {
		TN_DEBUG("PCI mmap failed");
		return false;
	}

	TN_INFO("PCI device %02" PRIx8 ":%02" PRIx8 ".%" PRIx8 " mapped to 0x%016" PRIxPTR, device.bus, device.device, device.function, dev_addr);
	*out_addr = dev_addr;
	return true;
}

uint32_t tn_pci_read(const struct tn_pci_device device, const uint8_t reg)
{
	const uint32_t addr = 0x80000000 | ((uint32_t)device.bus << 16) | ((uint32_t)device.device << 11) | ((uint32_t)device.function << 8) | reg;
	outl_p(addr, PCI_CONFIG_ADDR);
	const uint32_t result = inl_p(PCI_CONFIG_DATA);
	TN_DEBUG("PCI read: 0x%08" PRIx32 " -> 0x%08" PRIx32, addr, result);
	return result;
}
