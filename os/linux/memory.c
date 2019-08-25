#include "os/memory.h"

#include "os/linux/numa.h"
#include "util/log.h"

#include <fcntl.h>
#include <unistd.h>
#include <stddef.h>

#include <sys/mman.h>
#include <linux/mman.h>

// We only support 2MB hugepages
#define HUGEPAGE_SIZE_POWER (10 + 10 + 1)
#define HUGEPAGE_SIZE (1u << HUGEPAGE_SIZE_POWER)


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
		TN_INFO("Could not retrieve the page size"); // TODO adopt a policy for log levels and stick to it
		return false;
	}

	const uintptr_t page = addr / page_size;
	const uintptr_t map_offset = page * sizeof(uint64_t);
	if (map_offset != (uintptr_t) (off_t) map_offset) {
		TN_INFO("Map offset does not fit in off_t");
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

// NOTE: This implementation assumes that the Linux kernel will not move hugepages,
//       i.e. that their physical address remains constant.
//       If this assumption were to be broken, this code would need to change.
//       Locking a page is not sufficient - it guarantees the page won't be swapped out,
//       not that it won't be moved.
bool tn_mem_allocate(const uint64_t size, struct tn_memory_block* out_block)
{
	// OK if size is smaller, we'll just return too much memory
	if (size > HUGEPAGE_SIZE) {
		return false;
	}

	// http://man7.org/linux/man-pages//man2/munmap.2.html
	void* page = mmap(
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

	// HACK: We're hoping that the Linux kernel will allocate memory on our node - in practice this seems to work
	uint64_t node;
	if (!tn_numa_get_addr_node(virt_addr, &node)) {
		goto error;
	}
	if (!tn_numa_is_current_node(node)) {
		goto error;
	}

	uintptr_t phys_addr;
	if (!get_phys_addr(virt_addr, &phys_addr)) {
		goto error;
	}

	out_block->virt_addr = virt_addr;
	out_block->phys_addr = phys_addr;
	return true;

error:
	munmap(page, HUGEPAGE_SIZE);
	return false;
}

void tn_mem_free(struct tn_memory_block block)
{
	munmap((void*) block.virt_addr, HUGEPAGE_SIZE);
}

bool tn_mem_map(uintptr_t address, uint64_t size, uintptr_t* mapped_address)
{
	if (size > SIZE_MAX) {
		return false;
	}
	if (address != (uintptr_t) (off_t) address) {
		return false;
	}

	int mem_fd = open("/dev/mem", O_SYNC | O_RDWR);
	if (mem_fd == -1) {
		return false;
	}

	void* mapped = mmap(
		// No specific address
		NULL,
		// Size of the mapping (cast OK because we checked above)
		(size_t) size,
		// R/W page
		PROT_READ | PROT_WRITE,
		// Only for the current process
		MAP_PRIVATE,
		// /dev/mem
		mem_fd,
		// Offset is the address (cast OK because we checked above)
		(off_t) address
	);
	if (mapped == MAP_FAILED) {
		return false;
	}

	*mapped_address = (uintptr_t) mapped;
	return true;
}
