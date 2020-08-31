// Access PCI configuration space using port-mapped I/O: https://sysplay.github.io/books/LinuxDrivers/book/Content/Part08.html
// Note that Linux requires programs to call `ioperm` before accessing ports.
// To hide this, we pretend that reads and writes fail if we can't get permission.

#include "env/pci.h"

#include "filesystem.h"
#include "numa.h"
#include "util/log.h"

#include <inttypes.h>
#include <stdbool.h>

#include <sys/io.h>


// Physical addresses at which we can talk to PCI via geographical addressing
#define PCI_CONFIG_ADDR 0xCF8
#define PCI_CONFIG_DATA 0xCFC


static bool get_ioport_access(void)
{
	// Make sure we can talk to the devices
	// We access port 0x80 to wait after an outl, since it's the POST port so safe to do anything with (it's what glibc uses in the _p versions of outl/inl)
	// Also note that since reading an int32 is 4 bytes, we need to access 4 consecutive ports for PCI config/data.
	if (ioperm(0x80, 1, 1) < 0 || ioperm(PCI_CONFIG_ADDR, 4, 1) < 0 || ioperm(PCI_CONFIG_DATA, 4, 1) < 0) {
		TN_DEBUG("PCI ioperms failed");
		return false;
	}
	return true;
}

// From https://www.kernel.org/doc/Documentation/ABI/testing/sysfs-bus-pci
static bool get_device_node(const struct tn_pci_address address, uint64_t* out_node)
{
	char node_str[3] = {0};
	if (!tn_fs_readline(node_str, sizeof(node_str)/sizeof(char), "/sys/bus/pci/devices/0000:%02" PRIx8 ":%02" PRIx8 ".%" PRIx8 "/numa_node", address.bus, address.device, address.function)) {
		TN_DEBUG("Could not read PCI numa node");
		return false;
	}
	if (node_str[1] != '\n') {
		TN_DEBUG("Long NUMA node, not supported");
		return false;
	}

	const char node_chr = node_str[0];
	if (node_chr < '0' || node_chr > '9') {
		TN_DEBUG("Unknown NUMA node encoding");
		return false;
	}

	*out_node = (uint64_t) (node_chr - '0');
	return true;
}

static uint32_t get_pci_reg_addr(const struct tn_pci_address address, const uint16_t reg)
{
	// This looks odd but is the correct way to address extended registers; bus addresses are 8 bits so the top 8 bits are free thus the bottom 4 of that are for extended regs
	return 0x80000000u | (((uint32_t) (reg & 0xF00u)) << 16) | ((uint32_t) address.bus << 16) | ((uint32_t) address.device << 11) | ((uint32_t) address.function << 8) | (reg & 0xFFu);
}

static void pci_target(const struct tn_pci_address address, const uint16_t reg)
{
	const uint32_t reg_addr = get_pci_reg_addr(address, reg);
	outl(reg_addr, PCI_CONFIG_ADDR);
	// Wait til the outl is done
	outb(0, 0x80);
}

uint32_t tn_pci_read(const struct tn_pci_address address, const uint16_t reg)
{
	// Note that non-existent registers read as all-1s, so that's what we return if there's an error

	if (reg >= 4096) {
		return 0xFFFFFFFFu; // invalid register
	}

	uint64_t device_node;
	if (!get_ioport_access() || !get_device_node(address, &device_node) || !tn_numa_is_current_node(device_node)) {
		return 0xFFFFFFFFu;
	}

	pci_target(address, reg);
	return inl(PCI_CONFIG_DATA);
}

void tn_pci_write(const struct tn_pci_address address, const uint16_t reg, const uint32_t value)
{
	if (reg >= 4096) {
		return; // invalid register
	}

	uint64_t device_node;
	if (!get_ioport_access() || !get_device_node(address, &device_node) || !tn_numa_is_current_node(device_node)) {
		return;
	}

	pci_target(address, reg);
	outl(value, PCI_CONFIG_DATA);
}
