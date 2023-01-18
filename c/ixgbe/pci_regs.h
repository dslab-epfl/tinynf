#pragma once

#include "env/bits.h"
#include "env/pci.h"
#include "util/log.h"

#include <stdbool.h>
#include <stdint.h>

// Section 9.3.2 PCIe Configuration Space Summary: "0x10 Base Address Register 0" (32 bit), "0x14 Base Address Register 1" (32 bit)
// Section 9.3.6.1 Memory and IO Base Address Registers: BAR 0 is 64-bits, thus it's 0-low and 0-high, not 0 and 1
#define PCIREG_BAR0_LOW 0x10u
#define PCIREG_BAR0_HIGH 0x14u

// Section 9.3.3.3 Command Register (16 bit)
// Section 9.3.3.4 Status Register (16 bit, unused)
#define PCIREG_COMMAND 0x04u
#define PCIREG_COMMAND_MEMORY_ACCESS_ENABLE BIT(1)
#define PCIREG_COMMAND_BUS_MASTER_ENABLE BIT(2)
#define PCIREG_COMMAND_INTERRUPT_DISABLE BIT(10)

// Section 9.3.10.6 Device Status Register (16 bit)
// Section 9.3.10.7 Link Capabilities Register (16 bit, unused)
#define PCIREG_DEVICESTATUS 0xAAu
#define PCIREG_DEVICESTATUS_TRANSACTIONPENDING BIT(5)

// Section 9.3.3.1 Vendor ID Register (16 bit)
// Section 9.3.3.2 Device ID Register (16 bit)
#define PCIREG_ID 0x00u

// Section 9.3.7.1.4 Power Management Control / Status Register (16 bit)
// Section 9.3.7.1.5 PMCSR_BSE Bridge Support Extensions Register (8 bit, hardwired to 0)
// Section 9.3.7.1.6 Data Register (8 bit, unused)
#define PCIREG_PMCSR 0x44u
#define PCIREG_PMCSR_POWER_STATE BITS(0, 1)

// Get the value of PCI register 'reg' on the device at address 'addr'
static inline uint32_t pcireg_read(struct tn_pci_address addr, uint8_t reg)
{
	uint32_t value = tn_pci_read(addr, reg);
	TN_VERBOSE("IXGBE PCI read: 0x%02" PRIx8 " -> 0x%08" PRIx32, reg, value);
	return value;
}

// Check if the field 'field' of register 'reg' on the device at address 'addr' is cleared (i.e., reads as all 0s)
static inline bool pcireg_is_field_cleared(struct tn_pci_address addr, uint8_t reg, uint32_t field)
{
	return (pcireg_read(addr, reg) & field) == 0;
}

// Set (i.e., write all 1s) the field 'field' of register 'reg' on the device at address 'addr'
static inline void pcireg_set_field(struct tn_pci_address addr, uint8_t reg, uint32_t field)
{
	uint32_t old_value = pcireg_read(addr, reg);
	uint32_t new_value = old_value | field;
	tn_pci_write(addr, reg, new_value);
	TN_VERBOSE("IXGBE PCI write: 0x%02" PRIx8 " := 0x%08" PRIx32, reg, new_value);
}
