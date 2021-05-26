#include <stdbool.h>
#include <stdint.h>

#include <sys/io.h>


bool port_out_32(uint32_t port, uint64_t value)
{
	if (ioperm(port, 4, 1) < 0 || ioperm(0x80, 1, 1) < 0) {
		return false;
	}
	outl(value, port);
	outb(0, 0x80); // wait for the outl to complete
	return true;
}

uint32_t port_in_32(uint32_t port)
{
	if (ioperm(port, 4, 1) < 0) {
		return (uint32_t) -1; // same as if absent
	}
	return inl(port);
}
