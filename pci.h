#include <stdint.h>


// Gets the address at which the given device is memory-mapped,
// ensuring it refers to a block of at least min_length bytes,
// or returns 0 on error.
uint64_t tn_pci_get_device(char* address, uint64_t min_length);
