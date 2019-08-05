#include "os/linux/numa.h"

#include "util/log.h"

#include <sched.h>
#include <stdbool.h>
#include <unistd.h>

#include <linux/version.h>


uint64_t tn_numa_get_current_node()
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
#error This code assumes Linux 2.6.19
#endif

	uint64_t index = 0;
	while (true) {
		// First make sure the node exists
		char buffer[128];
		snprintf(buffer, sizeof(buffer)/sizeof(char), "/sys/devices/system/node/node%"PRIu64, index);
		if (access(buffer, F_OK) == -1) {
			TN_INFO("Couldn't find a NUMA node for the current CPU, assuming single node");
			return 0;
		}

		// Then check if the current CPU is on it
		snprintf(buffer, sizeof(buffer)/sizeof(char), "/sys/devices/system/cpu/cpu%d/node%"PRIu64, cpu, index);
		if (access(buffer, F_OK) == 0) {
			return index;
		}

		index = (uint64_t) (index + 1u);
	}

	// Unreachable
}

uint64_t tn_numa_get_addr_node(uintptr_t addr)
{
	int node = -1;
	if(syscall(239, &node, NULL, 0, (void*) addr, 3) != 0) {
		TN_INFO("wtf?");
	}
	return (uint64_t) node;
}
