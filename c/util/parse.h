// Parsing utilities.
// Useful mostly for the last method, which parses a PCI address from a string.

#pragma once

#include "env/pci.h"

#include <stdbool.h>
#include <stdint.h>

static bool tn_util_parse_hex_digit(char h, uint8_t* out_d)
{
	if (h >= 'a' && h <= 'f') {
		*out_d = (uint8_t) (10 + h - 'a');
		return true;
	}
	if (h >= 'A' && h <= 'F') {
		*out_d = (uint8_t) (10 + h - 'A');
		return true;
	}
	if (h >= '0' && h <= '9') {
		*out_d = (uint8_t) (h - '0');
		return true;
	}

	return false;
}

static bool tn_util_parse_hex8(char** ref_value, char end, uint8_t* out_result)
{
	uint8_t digit0;
	if (!tn_util_parse_hex_digit(**ref_value, &digit0)) {
		return false;
	}

	*ref_value = *ref_value + 1;

	if (**ref_value == end) {
		*ref_value = *ref_value + 1;
		*out_result = digit0;
		return true;
	}

	uint8_t digit1;
	if (!tn_util_parse_hex_digit(**ref_value, &digit1)) {
		return false;
	}

	*ref_value = *ref_value + 1;

	if (**ref_value == end) {
		*ref_value = *ref_value + 1;
		*out_result = digit0 * 16u + digit1;
		return true;
	}

	return false;
}

// Parses PCI addresses in Bus:Device.Function format; out_devices must be pre-allocated
static bool tn_util_parse_pci(uint64_t count, char** values, struct tn_pci_address* out_addresses)
{
	for (uint64_t n = 0; n < count; n++) {
		uint8_t bus;
		if (!tn_util_parse_hex8(&(values[n]), ':', &bus)) {
			return false;
		}

		uint8_t device;
		if (!tn_util_parse_hex8(&(values[n]), '.', &device)) {
			return false;
		}

		uint8_t function;
		if (!tn_util_parse_hex8(&(values[n]), '\0', &function)) {
			return false;
		}

		out_addresses[n] = (struct tn_pci_address){.bus = bus, .device = device, .function = function};
	}

	return true;
}
