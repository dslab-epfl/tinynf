#include "../pci.h"

#include "filesystem.h"
#include "numa.h"
#include "util/log.h"

#include <inttypes.h>
#include <stdbool.h>
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

// From https://www.kernel.org/doc/Documentation/ABI/testing/sysfs-bus-pci
static bool get_device_node(const struct tn_pci_device device, uint64_t* out_node)
{
	char* node_str;
	if (!tn_fs_readline(&node_str, "/sys/bus/pci/devices/0000:%02" PRIx8 ":%02" PRIx8 ".%" PRIx8 "/numa_node", device.bus, device.device, device.function)) {
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
	uint64_t device_node;
	if (!get_ioport_access() || !get_device_node(device, &device_node) || !tn_numa_is_current_node(device_node)) {
		return 0xFFFFFFFFu; // same as reading unknown reg
	}

	const uint32_t addr = get_pci_reg_addr(device, reg);
	pci_address(addr);
	const uint32_t result = inl(PCI_CONFIG_DATA);
	TN_VERBOSE("PCI read: 0x%08" PRIx32 " -> 0x%08" PRIx32, addr, result);
	return result;
}

void tn_pci_write(const struct tn_pci_device device, const uint8_t reg, const uint32_t value)
{
	uint64_t device_node;
	if (!get_ioport_access() || !get_device_node(device, &device_node) || !tn_numa_is_current_node(device_node)) {
		return;
	}

	const uint32_t addr = get_pci_reg_addr(device, reg);
	pci_address(addr);
	outl(value, PCI_CONFIG_DATA);
	TN_VERBOSE("PCI write: 0x%08" PRIx32 " := 0x%08" PRIx32, addr, value);
}
