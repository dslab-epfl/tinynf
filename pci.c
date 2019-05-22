#include "pci.h"
#include "filesystem.h"

#include <stdlib.h>


uint64_t tn_pci_get_device(char* address, uint64_t min_length)
{
	char* dev_resource_line = tn_fs_readline("/sys/bus/pci/devices/%s/resource", address);
	if (dev_resource_line == NULL) {
		goto error;
	}

	// We expect 3 64-bit hex numbers (2 chars prefix, 16 chars number), 2 spaces, 1 newline, 1 NULL char == 58
	// e.g. 0x00003800ffa80000 0x00003800ffafffff 0x000000000014220c
	if (dev_resource_line[56] != '\n') {
		// Somehow we didn't read exactly the line format we were expecting
		goto error;
	}

	uint64_t dev_phys_addr = strtoull(dev_resource_line, NULL, 16);
	// Offset to 2nd number: 18-char number + 1 space
	uint64_t dev_end_addr = strtoull(dev_resource_line + 18 + 1, NULL, 16);
	// Offset to 3rd number: 2 * (18-char number + 1 space)
	uint64_t dev_resource_flags = strtoull(dev_resource_line + 2 * (18 + 1), NULL, 16);

	if (dev_end_addr - dev_phys_addr <= min_length) {
		// Not enough memory given what was expected
		goto error;
	}

	if ((dev_resource_flags & 0x200) == 0) {
		// For some reason the first line is not a memory one; just abort...
		goto error;
	}

	free(dev_resource_line);
	return dev_phys_addr;

error:
	free(dev_resource_line);
	return 0;
}
