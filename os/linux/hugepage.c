#include "os/hugepage.h"

#include <sys/mman.h>

#include <linux/mman.h>

#include "os/memory.h"

// NOTE: This implementation assumes that the Linux kernel will not move hugepages,
//       i.e. that their physical address remains constant.
//       If this assumption were to be broken, this code would need to change.
//       Locking a page is not sufficient - it guarantees the page won't be swapped out,
//       not that it won't be moved.
// TODO: Consider merging os/mem and os/hugepage, and just allocate hugepages for everything, for simplicity

bool tn_hp_allocate(size_t size, node_t node, uintptr_t* out_addr)
{
	// We only support 2MB hugepages
	const int HUGEPAGE_SIZE_POWER = 10 + 10 + 1;
	const size_t HUGEPAGE_SIZE = 1U << HUGEPAGE_SIZE_POWER;

	if (size < HUGEPAGE_SIZE) {
		size = HUGEPAGE_SIZE;
	} else if (size > HUGEPAGE_SIZE) {
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

	node_t actual_node;
	if (!tn_mem_get_node((uintptr_t) page, &actual_node)) {
		return false;
	}

	// We're hoping that `node` is the current node, and that the Linux kernel will allocate memory on that node - in practice this seems to work
	if (actual_node != node) {
		return false;
	}

	*out_addr = (uintptr_t) page;
	return true;
}
