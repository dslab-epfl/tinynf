#include "os/pci.h"

#include "os/linux/filesystem.h"
#include "os/linux/numa.h"
#include "util/log.h"

#include <inttypes.h>
#include <stdlib.h>

#include <sys/io.h>

// Physical addresses at which we can talk to PCI via geographical addressing
#define PCI_CONFIG_ADDR 0xCF8
#define PCI_CONFIG_DATA 0xCFC

static bool get_ioport_access(void)
{
	// Make sure we can talk to the devices
	// We access port 0x80 to wait after an outl, since it's the POST port so safe to do anything with (it's what glibc uses in the _p versions of outl/inl)
	// Also note that since reading an int32 is 4 bytes, we need to access 4 consecutive ports for PCI config/data.
	static bool got_ioperm = false;
	if (!got_ioperm) {
		if (ioperm(0x80, 1, 1) < 0 || ioperm(PCI_CONFIG_ADDR, 4, 1) < 0 || ioperm(PCI_CONFIG_DATA, 4, 1) < 0) {
			TN_DEBUG("PCI ioperms failed");
		} else {
			got_ioperm = true;
		}
	}
	return got_ioperm;
}

static bool get_device_node(const struct tn_pci_device device, uint64_t* out_node)
{
	char* node_str;
	if (!tn_fs_readline(&node_str, "/sys/bus/pci/devices/0000:%02"PRIx8":%02"PRIx8".%"PRIx8"/numa_node", device.bus, device.device, device.function)) {
		TN_DEBUG("Could not read PCI numa node");
		return false;
	}

	const char node_chr = node_str[0];
	const char node_delim = node_str[1];
	free(node_str);

	if (node_delim != '\n') {
		TN_DEBUG("Long NUMA node, not supported");
		return false;
	}
	if (node_chr < '0' || node_chr > '9') {
		TN_DEBUG("Unknown NUMA node encoding");
		return false;
	}

	*out_node = (uint64_t) (node_chr - '0');
	return true;
}

bool tn_pci_mmap_device(const struct tn_pci_device device, const uint64_t min_length, uintptr_t* out_addr)
{
	char* dev_resource_line = NULL;

	// Make sure the device is on the same NUMA node as the CPU
	uint64_t device_node;
	if (!get_device_node(device, &device_node)) {
		TN_DEBUG("Could not get PCI device node");
		goto error;
	}
	if (!tn_numa_is_current_node(device_node)) {
		TN_DEBUG("PCI device is on wrong node");
		goto error;
	}

	// Read the first line of the PCI /resource file, as a sanity check + indication of the length of the resource
	if (!tn_fs_readline(&dev_resource_line, "/sys/bus/pci/devices/0000:%02"PRIx8":%02"PRIx8".%"PRIx8"/resource", device.bus, device.device, device.function)) {
		TN_DEBUG("Could not read PCI resource line");
		goto error;
	}
	// We expect 3 64-bit hex numbers (2 chars prefix, 16 chars number), 2 spaces, 1 newline, 1 NULL char == 58
	// e.g. 0x00003800ffa80000 0x00003800ffafffff 0x000000000014220c
	if (dev_resource_line[56] != '\n') {
		TN_DEBUG("Unexpected PCI resource line format");
		goto error;
	}
	const uint64_t dev_phys_addr = strtoull(dev_resource_line, NULL, 16);
	// Offset to 2nd number: 18-char number + 1 space
	const uint64_t dev_phys_addr_end = strtoull(dev_resource_line + 18 + 1, NULL, 16);
	const uint64_t dev_phys_length = (dev_phys_addr_end - dev_phys_addr + 1);
	if (dev_phys_length < min_length) {
		TN_DEBUG("Not enough PCI memory, expected at least %" PRIu64 " but got %" PRIu64, min_length, dev_phys_length);
		goto error;
	}
	// Offset to 3rd number: 2 * (18-char number + 1 space)
	const uint64_t dev_resource_flags = strtoull(dev_resource_line + 2 * (18 + 1), NULL, 16);
	if ((dev_resource_flags & 0x200) == 0) {
		TN_DEBUG("First PCI line is not memory");
		goto error;
	}

	// Now map the /resource0 file so we can access it
	uintptr_t dev_addr;
	if (!tn_fs_mmap(&dev_addr, "/sys/bus/pci/devices/0000:%02"PRIx8":%02"PRIx8".%"PRIx8"/resource0", device.bus, device.device, device.function)) {
		TN_DEBUG("Could not mmap PCI resource");
		goto error;
	}

	free(dev_resource_line);
	TN_INFO("PCI device %02" PRIx8 ":%02" PRIx8 ".%" PRIx8 " mapped to 0x%016" PRIxPTR, device.bus, device.device, device.function, dev_addr);
	*out_addr = dev_addr;
	return true;

error:
	free(dev_resource_line);
	return false;
}

static uint32_t get_pci_reg_addr(const struct tn_pci_device device, const uint8_t reg)
{
	return 0x80000000u | ((uint32_t)device.bus << 16) | ((uint32_t)device.device << 11) | ((uint32_t)device.function << 8) | reg;
}

static void pci_address(const uint32_t addr)
{
	outl(addr, PCI_CONFIG_ADDR);
	// Wait til the outl is done
	outb(0, 0x80);
}

uint32_t tn_pci_read(const struct tn_pci_device device, const uint8_t reg)
{
	if (!get_ioport_access()) {
		return 0xFFFFFFFFu; // same as reading unknown reg
	}

	const uint32_t addr = get_pci_reg_addr(device, reg);
	pci_address(addr);
	const uint32_t result = inl(PCI_CONFIG_DATA);
	TN_DEBUG("PCI read: 0x%08" PRIx32 " -> 0x%08" PRIx32, addr, result);
	return result;
}

void tn_pci_write(const struct tn_pci_device device, const uint8_t reg, const uint32_t value)
{
	if (!get_ioport_access()) {
		return;
	}

	const uint32_t addr = get_pci_reg_addr(device, reg);
	pci_address(addr);
	outl(value, PCI_CONFIG_DATA);
	TN_DEBUG("PCI write: 0x%08" PRIx32 " := 0x%08" PRIx32, addr, value);
}
