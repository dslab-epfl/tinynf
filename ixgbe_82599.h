#include <stdbool.h>

bool ixgbe_device_init(void* addr);

bool ixgbe_device_init_receive(void* addr, uint8_t queue);

bool ixgbe_device_init_send(void* addr, uint8_t queue);
