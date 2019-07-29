#include "os/cpu.h"

#include "os/stub/symbol.h"


bool tn_cpu_get_current_node(node_t* out_node)
{
	if (symbol_bool("cpu_get_current_node")) {
		symbol_make(out_node, sizeof(node_t));
		return true;
	}

	return false;
}
