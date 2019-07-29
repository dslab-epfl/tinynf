#include "os/pci.h"

#include "os/stub/symbol.h"


bool tn_pci_get_device_node(const struct tn_pci_device device, node_t* out_node)
{
	if (symbol_bool("pci_get_device_node")) {
		symbol_make(out_node, sizeof(node_t));
	}

	return false;
}

bool tn_pci_mmap_device(const struct tn_pci_device device, const uint64_t min_length, uintptr_t* out_addr)
{
	if (symbol_bool("")) {
		???
	}
}

uint32_t tn_pci_read(const struct tn_pci_device device, const uint8_t reg)
{
	???
}
