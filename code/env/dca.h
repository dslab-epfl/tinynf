#pragma once

#include <stdbool.h>
#include <stdint.h>


// Checks whether DCA support is enabled.
bool tn_dca_is_enabled(void);

// Gets the APIC ID for DCA.
uint8_t tn_dca_get_id(void);
