#include "numa.h"

#include <numaif.h>
#include <stddef.h>
#include <unistd.h>

#include <sys/syscall.h>


bool tn_numa_is_current_node(uint64_t node)
{
	// http://man7.org/linux/man-pages/man2/getcpu.2.html mentions only EFAULT, which can't happen here, but let's check the return value just in case.
	// "The third argument to this system call is nowadays unused, and should be specified as NULL unless portability to Linux 2.6.23 or earlier is required"
	// "When either cpu or node is NULL nothing is written to the respective pointer."
	unsigned unused;
	unsigned this_node = (unsigned) -1; // sentinel value
	if (syscall(SYS_getcpu, &unused, &this_node, NULL) != 0) {
		return false;
	}
	return this_node == node;
}

bool tn_numa_get_addr_node(uintptr_t addr, uint64_t* out_node)
{
	// NOTE: To not depend on libnuma, the call can be replaced by `syscall(239, &node, NULL, 0, (void*) addr, 3)`
	// "If flags specifies both MPOL_F_NODE and MPOL_F_ADDR, get_mempolicy() will return the node ID of the node on which the address addr is allocated into the location pointed to by mode."
	// http://man7.org/linux/man-pages/man2/get_mempolicy.2.html
	int node = -1;
	if (get_mempolicy(&node, NULL, 0, (void*) addr, MPOL_F_NODE | MPOL_F_ADDR) == 0) {
		*out_node = (uint64_t) node;
		return true;
	}

	return false;
}
