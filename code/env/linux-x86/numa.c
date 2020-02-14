// This implementation does *not* depend on libnuma, so that programs don't need an extra library to link with, allowing for easier static linking.
// Instead, we perform system calls directly.

#include "numa.h"

#include <unistd.h>

#include <sys/syscall.h>


bool tn_numa_is_current_node(uint64_t node)
{
	// http://man7.org/linux/man-pages/man2/getcpu.2.html mentions only EFAULT, which can't happen here, but let's check the return value just in case.
	// "The third argument to this system call is nowadays unused, and should be specified as NULL unless portability to Linux 2.6.23 or earlier is required"
	// "When either cpu or node is NULL nothing is written to the respective pointer."
	unsigned this_node = (unsigned) -1; // sentinel value
	if (syscall(SYS_getcpu, NULL, &this_node, NULL) != 0) {
		return false;
	}
	return this_node == node;
}

bool tn_numa_get_addr_node(uintptr_t addr, uint64_t* out_node)
{
	// "If flags specifies both MPOL_F_NODE and MPOL_F_ADDR, get_mempolicy() will return the node ID of the node on which the address addr is allocated into the location pointed to by mode."
	// MPOL_F_NODE is 1, MPOL_F_ADDR is 2
	// http://man7.org/linux/man-pages/man2/get_mempolicy.2.html
	int node = -1;
	if (syscall(SYS_get_mempolicy, &node, NULL, 0, (void*) addr, 1 | 2) == 0) {
		*out_node = (uint64_t) node;
		return true;
	}

	return false;
}
