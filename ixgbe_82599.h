#pragma once

#include <stdbool.h>
#include <stdint.h>

bool ixgbe_device_init(uintptr_t addr);

bool ixgbe_device_init_receive(uintptr_t addr, uint8_t queue);

bool ixgbe_device_init_send(uintptr_t addr, uint8_t queue);
