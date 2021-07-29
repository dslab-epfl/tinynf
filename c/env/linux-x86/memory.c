// The only way to have pinned pages on Linux is to use huge pages: https://www.kernel.org/doc/Documentation/vm/hugetlbpage.txt
// Note that Linux's `mlock` system call is not sufficient to pin; it only guarantees the pages will not be swapped out, not that the physical address won't change.
// While Linux doesn't actually guarantee that huge pages are pinned, in practice its implementation pins them.
// This file makes heavy use of the `mmap`/`munmap` calls for memory-mapped files: https://en.wikipedia.org/wiki/Mmap

#include "env/memory.h"

#include "numa.h"
#include "util/log.h"

#include <fcntl.h>
#include <unistd.h>

#include <sys/mman.h>

// We only support 2MB hugepages
#define HUGEPAGE_SIZE_POWER (10 + 10 + 10)
#define HUGEPAGE_SIZE (1u << HUGEPAGE_SIZE_POWER)

// glibc defines it but musl doesn't
#ifndef MAP_HUGE_SHIFT
#define MAP_HUGE_SHIFT 26
#endif


static bool page_allocated;
static uint8_t* page_addr;
static size_t page_used_len;


// Gets the page size, or returns 0 on error
static uintptr_t get_page_size(void)
{
	// sysconf is documented to return -1 on error; let's check all negative cases along the way, to make sure the conversion to unsigned is sound
	const long page_size_long = sysconf(_SC_PAGESIZE);
	if (page_size_long > 0) {
		return (uintptr_t) page_size_long;
	}
	return 0;
}

bool tn_mem_allocate(size_t size, void** out_addr)
{
	if (!page_allocated) {
		page_addr = mmap(
			// No specific address
			NULL,
			// Size of the mapping
			HUGEPAGE_SIZE,
			// R/W page
			PROT_READ | PROT_WRITE,
			// Hugepage, not backed by a file (and thus zero-initialized); note that without MAP_SHARED the call fails
			// MAP_POPULATE means the page table will be populated already (without the need for a page fault later),
			// which is required if the calling code tries to get the physical address of the page without accessing it first.
			MAP_HUGETLB | (HUGEPAGE_SIZE_POWER << MAP_HUGE_SHIFT) | MAP_ANONYMOUS | MAP_SHARED | MAP_POPULATE,
			// Required on MAP_ANONYMOUS
			-1,
			// Required on MAP_ANONYMOUS
			0
		);
		if (page_addr == MAP_FAILED) {
			TN_DEBUG("Allocate mmap failed");
			return false;
		}
		uint64_t node;
		if (!tn_numa_get_addr_node(page_addr, &node)) {
			TN_DEBUG("Could not get memory's NUMA node");
			return false;
		}
		if (!tn_numa_is_current_node(node)) {
			TN_DEBUG("Allocated memory is not in our NUMA node");
			return false;
		}
		page_allocated = true;
		page_used_len = 0;
	}

	// Weird but valid; return a likely-invalid address for debugging convenience
	if (size == 0) {
		*out_addr = page_addr + HUGEPAGE_SIZE;
		return true;
	}

	// Return and align to an integral number of cache lines
	size = size + (64 - (size % 64));

	// Align as required by the contract
	const size_t align_diff = (size_t) (page_addr + page_used_len) % size;
	if (align_diff != 0) {
		page_used_len = page_used_len + (size - align_diff);
	}

	if (HUGEPAGE_SIZE - page_used_len < size) {
		TN_DEBUG("Not enough space left to allocate");
		return false;
	}

	*out_addr = page_addr + page_used_len;
	page_used_len = page_used_len + size;
	return true;
}

bool tn_mem_phys_to_virt(const uint64_t addr, const size_t size, void** out_virt_addr)
{
	if (addr != (uint64_t) (off_t) addr) {
		TN_DEBUG("Cannot phys-to-virt an addr that does not roundtrip to off_t");
		return false;
	}

	int mem_fd = open("/dev/mem", O_SYNC | O_RDWR);
	if (mem_fd == -1) {
		TN_DEBUG("Could not open /dev/mem");
		return false;
	}

	void* mapped = mmap(
		// No specific address
		NULL,
		// Size of the mapping
		size,
		// R/W page
		PROT_READ | PROT_WRITE,
		// Send updates to the underlying "file"
		MAP_SHARED,
		// /dev/mem
		mem_fd,
		// Offset is the address (cast OK because we checked above)
		(off_t) addr
	);

	// nothing we can do if this fails, since we didn't write don't even bother checking
	close(mem_fd);

	if (mapped == MAP_FAILED) {
		TN_DEBUG("Phys-to-virt mmap failed");
		return false;
	}

	*out_virt_addr = mapped;
	return true;
}

// See https://www.kernel.org/doc/Documentation/vm/pagemap.txt
bool tn_mem_virt_to_phys(void* const addr, uintptr_t* out_phys_addr)
{
	const uintptr_t page_size = get_page_size();
	if (page_size == 0) {
		TN_DEBUG("Could not retrieve the page size");
		return false;
	}

	const uintptr_t page = (uintptr_t) addr / page_size;
	const uintptr_t map_offset = page * sizeof(uint64_t);
	if (map_offset != (uintptr_t) (off_t) map_offset) {
		TN_DEBUG("Cannot virt-to-phys with an offset that does not roundtrip to off_t");
		return false;
	}

	const int map_fd = open("/proc/self/pagemap", O_RDONLY);
	if (map_fd < 0) {
		TN_DEBUG("Could not open the pagemap");
		return false;
	}

	if (lseek(map_fd, (off_t) map_offset, SEEK_SET) == (off_t) -1) {
		TN_DEBUG("Could not seek the pagemap");
		close(map_fd);
		return false;
	}

	uint64_t metadata;
	const ssize_t read_result = read(map_fd, &metadata, sizeof(uint64_t));
	close(map_fd);
	if (read_result != sizeof(uint64_t)) {
		TN_DEBUG("Could not read the pagemap");
		return false;
	}

	// We want the PFN, but it's only meaningful if the page is present; bit 63 indicates whether it is
	if ((metadata & 0x8000000000000000) == 0) {
		TN_DEBUG("Page not present");
		return false;
	}
	// PFN = bits 0-54
	const uint64_t pfn = metadata & 0x7FFFFFFFFFFFFF;
	if (pfn == 0) {
		TN_DEBUG("Page not mapped");
		return false;
	}

	const uintptr_t addr_offset = (uintptr_t) addr % page_size;
	*out_phys_addr = pfn * page_size + addr_offset;
	return true;
}
