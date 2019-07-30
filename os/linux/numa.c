#include "os/linux/numa.h"

#include "util/log.h"

#include <numa.h>
#include <sched.h>

#include <linux/version.h>


uint64_t tn_numa_get_current_node()
{
	if (numa_available() == -1) {
		TN_DEBUG("libnuma not available, assuming single NUMA node");
		return 0;
	}

	// From http://man7.org/linux/man-pages/man3/sched_getcpu.3.html
	// "Errors: ENOSYS This kernel does not implement getcpu(2)."
	// No other errors are listed.
	// From http://man7.org/linux/man-pages/man2/getcpu.2.html
	// "getcpu() was added in kernel 2.6.19 for x86-64 and i386"
#if LINUX_VERSION_CODE >= KERNEL_VERSION(2,6,19)
#ifdef __x86_64__
	int cpu = sched_getcpu();

	// Note that according to the numa doc, numa_node_of_cpu only fails "if the user supplies an invalid cpu", so we don't need to handle that here
	return (uint64_t) numa_node_of_cpu(cpu);
#else
#error This code assumes x86-64
#endif
#else
#error This code assumes Linux 2.6.19
#endif
}
