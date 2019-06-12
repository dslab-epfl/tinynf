#include "os/hugepage.h"

#include <sys/mman.h>

#include <linux/mman.h>

// NOTE: This implementation assumes that the Linux kernel will not move hugepages,
//       i.e. that their physical address remains constant.
//       If this assumption were to be broken, this code would need to change.
//       Locking a page is not sufficient - it guarantees the page won't be swapped out,
//       not that it won't be moved.

uintptr_t tn_hp_allocate(const size_t size)
{
	// We only support 2MB hugepages
	const int HUGEPAGE_SIZE_POWER = 10 + 10 + 1;
	const size_t HUGEPAGE_SIZE = 1U << HUGEPAGE_SIZE_POWER;

	if (size != HUGEPAGE_SIZE) {
		return (uintptr_t) -1;
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
		return (uintptr_t) -1;
	}

	return (uintptr_t) page;
}
