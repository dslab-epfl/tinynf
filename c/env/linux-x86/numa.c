// This implementation does *not* depend on libnuma, so that programs don't need an extra library to link with, allowing for easier static linking.
// Instead, we perform system calls directly.

#include "numa.h"

#include "filesystem.h"
#include "util/log.h"

#include <inttypes.h>
#include <sys/syscall.h>
#include <unistd.h>

bool tn_numa_is_current_node(uint64_t node)
{
	// http://man7.org/linux/man-pages/man2/getcpu.2.html mentions only EFAULT, which can't happen here, but let's check the return value just in case.
	// "The third argument to this system call is nowadays unused, and should be specified as NULL unless portability to Linux 2.6.23 or earlier is required"
	// "When either cpu or node is NULL nothing is written to the respective pointer."
	unsigned this_node;
	if (syscall(SYS_getcpu, NULL, &this_node, NULL) != 0) {
		return false;
	}
	return this_node == node;
}

bool tn_numa_get_addr_node(void* addr, uint64_t* out_node)
{
	// "If flags specifies both MPOL_F_NODE and MPOL_F_ADDR, get_mempolicy() will return the node ID of the node on which the address addr is allocated into the location pointed to by mode."
	// MPOL_F_NODE is 1, MPOL_F_ADDR is 2
	// http://man7.org/linux/man-pages/man2/get_mempolicy.2.html
	int node;
	if (syscall(SYS_get_mempolicy, &node, NULL, 0, addr, 1 | 2) == 0) {
		*out_node = (uint64_t) node;
		return true;
	}

	return false;
}

// From https://www.kernel.org/doc/Documentation/ABI/testing/sysfs-bus-pci
bool tn_numa_get_device_node(const struct tn_pci_address address, uint64_t* out_node)
{
	char node_str[3] = {0};
	if (!tn_fs_readline(node_str, sizeof(node_str) / sizeof(char), "/sys/bus/pci/devices/0000:%02" PRIx8 ":%02" PRIx8 ".%" PRIx8 "/numa_node", address.bus,
			    address.device, address.function)) {
		TN_DEBUG("Could not read PCI numa node");
		return false;
	}
	if (node_str[1] != '\n') {
		TN_DEBUG("Long NUMA node, not supported");
		return false;
	}
	if (node_str[0] < '0' || node_str[0] > '9') {
		TN_DEBUG("Unknown NUMA node encoding");
		return false;
	}

	*out_node = (uint64_t) (node_str[0] - '0');
	return true;
}
