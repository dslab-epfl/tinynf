#pragma once

#include <stdint.h>

#include "nf.h"

#define CONFIG_FNAME_LEN 512

struct nf_config {
  // LAN (i.e. internal) device
  uint16_t lan_device;

  // WAN device, i.e. external
  uint16_t wan_device;

  // Policer rate in B/s
  uint64_t rate;

  // Policer burst size in B
  uint64_t burst;

  // Size of the dynamic filtering table
  uint32_t dyn_capacity;
};
