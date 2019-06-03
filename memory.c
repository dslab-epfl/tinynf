#include "memory.h"

#include <fcntl.h>
#include <sys/types.h>
#include <unistd.h>

// See https://www.kernel.org/doc/Documentation/vm/pagemap.txt
uintptr_t tn_mem_virtual_to_physical_address(const uintptr_t address)
{
	const long page_size = sysconf(_SC_PAGESIZE);
	if (page_size == -1) {
		return (uintptr_t) -1;
	}

	const uintptr_t virtual_address = address;
	const uintptr_t page = virtual_address / page_size;

	const int map_fd = open("/proc/self/pagemap", O_RDONLY);
	if (map_fd < 0) {
		return (uintptr_t) -1;
	}

	const uint64_t map_offset = page * sizeof(uint64_t);
	if (lseek(map_fd, map_offset, SEEK_SET) == (off_t) -1) {
		close(map_fd);
		return (uintptr_t) -1;
	}

	uint64_t metadata;
	const ssize_t read_result = read(map_fd, &metadata, sizeof(uint64_t));
	close(map_fd);
	if (read_result != sizeof(uint64_t)) {
		return (uintptr_t) -1;
	}

	// We want the PFN, but it's only meaningful if the page is present; bit 63 indicates whether it is
	if ((metadata & 0x8000000000000000ULL) == 0) {
		return (uintptr_t) -1;
	}
	// PFN = bits 0-54
	const uint64_t pfn = metadata & 0x7FFFFFFFFFFFFFULL;
	if (pfn == 0) {
		// Page is unmapped
		return (uintptr_t) -1;
	}

	const uintptr_t address_offset = virtual_address % page_size;
	return pfn * page_size + address_offset;
}
