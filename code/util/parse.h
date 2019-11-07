#pragma once

#include "env/pci.h"

#include <stdbool.h>
#include <stdint.h>


bool tn_util_parse_pci(uint64_t count, char** values, struct tn_pci_device* out_devices);
