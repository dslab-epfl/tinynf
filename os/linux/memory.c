#include "os/memory.h"

#include "util/log.h"

#include <fcntl.h>
#include <numa.h>
#include <sys/types.h>
#include <unistd.h>

#include <sys/mman.h>

#include <linux/mman.h>


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
static bool get_phys_addr(const uintptr_t addr, uintptr_t* out_phys_addr)
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

static bool get_node(const uintptr_t addr, node_t* out_node)
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

// NOTE: This implementation assumes that the Linux kernel will not move hugepages,
//       i.e. that their physical address remains constant.
//       If this assumption were to be broken, this code would need to change.
//       Locking a page is not sufficient - it guarantees the page won't be swapped out,
//       not that it won't be moved.
bool tn_mem_allocate(size_t size, node_t node, struct tn_memory_block* out_block)
{
	// We only support 2MB hugepages
	const int HUGEPAGE_SIZE_POWER = 10 + 10 + 1;
	const size_t HUGEPAGE_SIZE = 1U << HUGEPAGE_SIZE_POWER;

	// OK if size is smaller, we'll just return too much memory
	if (size > HUGEPAGE_SIZE) {
		return false;
	}

	// http://man7.org/linux/man-pages//man2/munmap.2.html
	const void* page = mmap(
		// No specific address
		NULL,
		// Size of the mapping
		HUGEPAGE_SIZE,
		// R/W page
		PROT_READ | PROT_WRITE,
		// Hugepage, not backed by a file; note that without MAP_SHARED the call fails
		// MAP_POPULATE means the page table will be populated already (without the need for a page fault later),
		// which is required if the calling code tries to get the physical address of the page without accessing it first.
		MAP_HUGETLB | (HUGEPAGE_SIZE_POWER << MAP_HUGE_SHIFT) | MAP_ANONYMOUS | MAP_SHARED | MAP_POPULATE,
		// Required on MAP_ANONYMOUS
		-1,
		// Required on MAP_ANONYMOUS
		0
	);
	if (page == MAP_FAILED) {
		return false;
	}

	uintptr_t virt_addr = (uintptr_t) page;

	node_t actual_node;
	if (!get_node(virt_addr, &actual_node)) {
		return false;
	}

	// HACK: We're hoping that `node` is the current node, and that the Linux kernel will allocate memory on that node - in practice this seems to work
	if (actual_node != node) {
		return false;
	}

	uintptr_t phys_addr;
	if (!get_phys_addr(virt_addr, &phys_addr)) {
		return false;
	}

	out_block->virt_addr = virt_addr;
	out_block->phys_addr = phys_addr;
	return true;
}
