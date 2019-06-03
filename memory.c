#include "memory.h"

#include <fcntl.h>
#include <sys/types.h>
#include <unistd.h>


// From https://stackoverflow.com/a/5761398/3311770
// ASSUMPTION: We use uint64_t because if off_t happened to have a bigger max, we wouldn't care
// ASSUMPTION: We are on an implementation that will not generate a signal
static uint64_t max_off_t(void)
{
	int64_t x;
	for (x = INTMAX_MAX; (off_t) x != x; x = x/2) {}
	return (uint64_t) x; // cast is safe because division by 2 cannot cause x to be negative.
}

// See https://www.kernel.org/doc/Documentation/vm/pagemap.txt
uintptr_t tn_mem_virtual_to_physical_address(const uintptr_t address)
{
	// sysconf is documented to return -1 on error; let's check all negative cases along the way, to make sure the conversion to unsigned is sound
	const long page_size_long = sysconf(_SC_PAGESIZE);
	if (page_size_long < 0) {
		return (uintptr_t) -1;
	}
	const uintptr_t page_size = (uintptr_t) page_size_long;

	const uintptr_t virtual_address = address;
	const uintptr_t page = virtual_address / page_size;

	const int map_fd = open("/proc/self/pagemap", O_RDONLY);
	if (map_fd < 0) {
		return (uintptr_t) -1;
	}

	const uintptr_t map_offset = page * sizeof(uint64_t);
	if (map_offset > max_off_t()) {
		close(map_fd);
		return (uintptr_t) -1;
	}
	if (lseek(map_fd, (off_t) map_offset, SEEK_SET) == (off_t) -1) {
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
	if ((metadata & 0x8000000000000000) == 0) {
		return (uintptr_t) -1;
	}
	// PFN = bits 0-54
	const uint64_t pfn = metadata & 0x7FFFFFFFFFFFFF;
	if (pfn == 0) {
		// Page is unmapped
		return (uintptr_t) -1;
	}

	const uintptr_t address_offset = virtual_address % page_size;
	return pfn * page_size + address_offset;
}
