#include <stdint.h>
#include <sys/io.h>

uint32_t port_out_32(uint16_t port, uint32_t value)
{
	if (ioperm(port, 4, 1) < 0 || ioperm(0x80, 1, 1) < 0) {
		return 0;
	}
	outl(value, port);
	outb(0, 0x80); // wait for the outl to complete
	return 1;
}

uint32_t port_in_32(uint16_t port)
{
	if (ioperm(port, 4, 1) < 0) {
		return (uint32_t) -1; // same as if absent
	}
	return inl(port);
}
