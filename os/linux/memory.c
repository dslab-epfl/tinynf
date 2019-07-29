#include "os/memory.h"

#include "util/log.h"

#include <fcntl.h>
#include <numa.h>
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

// Gets the page size, or returns 0 on error
static uintptr_t get_page_size(void)
{
	static uintptr_t cached_page_size = 0;
	if (cached_page_size == 0) {
		// sysconf is documented to return -1 on error; let's check all negative cases along the way, to make sure the conversion to unsigned is sound
		const long page_size_long = sysconf(_SC_PAGESIZE);
		if (page_size_long > 0) {
			cached_page_size = (uintptr_t) page_size_long;
		}
	}

	return cached_page_size;
}

// See https://www.kernel.org/doc/Documentation/vm/pagemap.txt
bool tn_mem_get_phys_addr(const uintptr_t addr, uintptr_t* out_phys_addr)
{
	const uintptr_t page_size = get_page_size();
	if (page_size == 0) {
		TN_INFO("Could not retrieve the page size");
		return false;
	}

	const uintptr_t page = addr / page_size;
	const uintptr_t map_offset = page * sizeof(uint64_t);
	if (map_offset > max_off_t()) {
		TN_INFO("Map offset is larger than maximum off_t");
		return false;
	}

	const int map_fd = open("/proc/self/pagemap", O_RDONLY);
	if (map_fd < 0) {
		TN_INFO("Could not open the pagemap");
		return false;
	}

	if (lseek(map_fd, (off_t) map_offset, SEEK_SET) == (off_t) -1) {
		TN_INFO("Could not seek the pagemap");
		close(map_fd);
		return false;
	}

	uint64_t metadata;
	const ssize_t read_result = read(map_fd, &metadata, sizeof(uint64_t));
	close(map_fd);
	if (read_result != sizeof(uint64_t)) {
		TN_INFO("Could not read the pagemap");
		return false;
	}

	// We want the PFN, but it's only meaningful if the page is present; bit 63 indicates whether it is
	if ((metadata & 0x8000000000000000) == 0) {
		TN_INFO("Page not present");
		return false;
	}
	// PFN = bits 0-54
	const uint64_t pfn = metadata & 0x7FFFFFFFFFFFFF;
	if (pfn == 0) {
		TN_INFO("Page not mapped");
		return false;
	}

	const uintptr_t addr_offset = addr % page_size;
	*out_phys_addr = pfn * page_size + addr_offset;
	return true;
}

bool tn_mem_get_node(const uintptr_t addr, node_t* out_node)
{
	const uintptr_t page_size = get_page_size();
	if (page_size == 0) {
		TN_INFO("Could not retrieve the page size");
		return false;
	}

	void* aligned_addr = (void*) (addr - (addr % page_size));
	int status[1];
	if (numa_move_pages(0, 1, &aligned_addr, NULL, status, 0) != 0) {
		TN_INFO("Could not get NUMA page info");
		return false;
	}

	if (status[0] < 0) {
		TN_INFO("NUMA page info failed");
		return false;
	}

	*out_node = (node_t) status[0];
	return true;
}
