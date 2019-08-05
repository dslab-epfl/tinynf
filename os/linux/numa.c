#include "os/linux/numa.h"

#include <inttypes.h>
#include <sched.h>
#include <stdio.h>
#include <unistd.h>

#include <linux/version.h>


bool tn_numa_is_current_node(uint64_t node)
{
	// From http://man7.org/linux/man-pages/man3/sched_getcpu.3.html
	// "Errors: ENOSYS This kernel does not implement getcpu(2)."
	// No other errors are listed.
	// From http://man7.org/linux/man-pages/man2/getcpu.2.html
	// "getcpu() was added in kernel 2.6.19 for x86-64 and i386"
#if LINUX_VERSION_CODE >= KERNEL_VERSION(2,6,19)
#ifdef __x86_64__
	int cpu = sched_getcpu();
#else
#error This code assumes x86-64
#endif
#else
#error This code assumes Linux >= 2.6.19
#endif

	char buffer[128];
	snprintf(buffer, sizeof(buffer)/sizeof(char), "/sys/devices/system/cpu/cpu%d/node%"PRIu64, cpu, node);
	return access(buffer, F_OK) == 0;
}

bool tn_numa_get_addr_node(uintptr_t addr, uint64_t* out_node)
{
	// Hacky, because we don't want to depend on libnuma.
	// 239 is the syscall for get_mempolicy
	// 3 is a combination of the MPOL_F_NODE and MPOL_F_ADDR flags
	// "If flags specifies both MPOL_F_NODE and MPOL_F_ADDR, get_mempolicy() will return the node ID of the node on which the address addr is allocated into the location pointed to by mode."
	// http://man7.org/linux/man-pages/man2/get_mempolicy.2.html
	int node = -1;
	if (syscall(239, &node, NULL, 0, (void*) addr, 3) == 0) {
		*out_node = (uint64_t) node;
		return true;
	}

	return false;
}
