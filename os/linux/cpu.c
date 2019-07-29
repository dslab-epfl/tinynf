#include "os/cpu.h"

#include <numa.h>
#include <sched.h>


bool tn_cpu_get_current_node(node_t* out_node)
{
	if (numa_available() == -1) {
		return false;
	}

	int cpu = sched_getcpu();
	if (cpu == -1) {
		return false;
	}

	// Note that according to the numa doc, numa_node_of_cpu only fails "if the user supplies an invalid cpu", so we don't need to handle that here
	*out_node = (node_t) numa_node_of_cpu(cpu);
	return true;
}
