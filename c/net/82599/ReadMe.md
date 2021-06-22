# Warning

If you are playing with this code or re-implementing it, **be very careful** when setting NIC registers that deal with addresses, such as RDBAL/RDBAH.

These registers need _physical_ addresses, i.e., not the virtual ones your program sees, but the actual address in physical memory, which is mapped into a different address for your program by the operating system and hardware.

If you mess up the physical address, and make it point to somewhere other than what you intended, the NIC will happily read and write data from there... which could, for instance, corrupt another program in memory, or even the operating system itself.
