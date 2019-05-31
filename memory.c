#include "memory.h"


uint64_t tn_mem_virtual_to_physical_address(void* address)
{
	uint64_t virtual_address = (uint64_t) address;
	// TODO translate the following
	
        /* standard page size */
        page_size = getpagesize();

        fd = open("/proc/self/pagemap", O_RDONLY);
        if (fd < 0) {
                RTE_LOG(ERR, EAL, "%s(): cannot open /proc/self/pagemap: %s\n",
                        __func__, strerror(errno));
                return RTE_BAD_IOVA;
        }

        virt_pfn = (unsigned long)virtaddr / page_size;
        offset = sizeof(uint64_t) * virt_pfn;
        if (lseek(fd, offset, SEEK_SET) == (off_t) -1) {
                RTE_LOG(ERR, EAL, "%s(): seek error in /proc/self/pagemap: %s\n",
                                __func__, strerror(errno));
                close(fd);
                return RTE_BAD_IOVA;
        }

        retval = read(fd, &page, PFN_MASK_SIZE);
        close(fd);
        if (retval < 0) {
                RTE_LOG(ERR, EAL, "%s(): cannot read /proc/self/pagemap: %s\n",
                                __func__, strerror(errno));
                return RTE_BAD_IOVA;
        } else if (retval != PFN_MASK_SIZE) {
                RTE_LOG(ERR, EAL, "%s(): read %d bytes from /proc/self/pagemap "
                                "but expected %d:\n",
                                __func__, retval, PFN_MASK_SIZE);
                return RTE_BAD_IOVA;
        }

        /*
         * the pfn (page frame number) are bits 0-54 (see
         * pagemap.txt in linux Documentation)
         */
        if ((page & 0x7fffffffffffffULL) == 0)
                return RTE_BAD_IOVA;

        physaddr = ((page & 0x7fffffffffffffULL) * page_size)
                + ((unsigned long)virtaddr % page_size);

        return physaddr;
	
}
