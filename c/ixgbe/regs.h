#pragma once

#include "env/bits.h"
#include "env/endian.h"
#include "util/log.h"

#include <stdbool.h>
#include <stdint.h>

// Section 8.2.3.1.1 Device Control Register
#define REG_CTRL (0x00000u / 4u)
#define REG_CTRL_MASTER_DISABLE BIT(2)
#define REG_CTRL_RST BIT(26)

// Section 8.2.3.1.3 Extended Device Control Register
#define REG_CTRLEXT (0x00018u / 4u)
#define REG_CTRLEXT_NSDIS BIT(16)

// Section 8.2.3.11.1 Rx DCA Control Register
#define REG_DCARXCTRL(n) ((n) <= 63u ? (0x0100Cu / 4u + 0x10u * (n)) : (0x0D00Cu / 4u + 0x10u * ((n) -64u)))
// This bit is reserved, has no name, but must be used anyway
#define REG_DCARXCTRL_UNKNOWN BIT(12)

// Section 8.2.3.11.2 Tx DCA Control Registers
#define REG_DCATXCTRL(n) (0x0600Cu / 4u + 0x10u * (n))
#define REG_DCATXCTRL_TX_DESC_WB_RO_EN BIT(11)

// Section 8.2.3.9.2 DMA Tx Control
#define REG_DMATXCTL (0x04A80u / 4u)
#define REG_DMATXCTL_TE BIT(0)

// Section 8.2.3.9.1 DMA Tx TCP Max Allow Size Requests
#define REG_DTXMXSZRQ (0x08100u / 4u)
#define REG_DTXMXSZRQ_MAX_BYTES_NUM_REQ BITS(0, 11)

// Section 8.2.3.2.1 EEPROM/Flash Control Register
#define REG_EEC (0x10010u / 4u)
#define REG_EEC_EE_PRES BIT(8)
#define REG_EEC_AUTO_RD BIT(9)

// Section 8.2.3.5.9 Extended Interrupt Mask Clear Registers
#define REG_EIMC(n) (n == 0 ? (0x00888u / 4u) : (0x00AB0u / 4u + (n - 1u)))

// Section 8.2.3.3.7 Flow Control Configuration
#define REG_FCCFG (0x03D00u / 4u)
#define REG_FCCFG_TFCE BITS(3, 4)

// Section 8.2.3.3.4 Flow Control Receive Threshold High
#define REG_FCRTH(n) (0x03260u / 4u + (n))
#define REG_FCRTH_RTH BITS(5, 18)

// Section 8.2.3.7.1 Filter Control Register (FCTRL)
#define REG_FCTRL (0x05080u / 4u)
#define REG_FCTRL_MPE BIT(8)
#define REG_FCTRL_UPE BIT(9)

// Section 8.2.3.7.19 Five tuple Queue Filter
#define REG_FTQF(n) (0x0E600u / 4u + (n))
#define REG_FTQF_QUEUE_ENABLE BIT(31)

// Section 8.2.3.4.10 Firmware Semaphore Register
#define REG_FWSM (0x10148u / 4u)
#define REG_FWSM_EXT_ERR_IND BITS(19, 24)

// Section 8.2.3.4.12 PCIe Control Extended Register
#define REG_GCREXT (0x11050u / 4u)
#define REG_GCREXT_BUFFERS_CLEAR_FUNC BIT(30)

// Section 8.2.3.22.8 MAC Core Control 0 Register
#define REG_HLREG0 (0x04240u / 4u)
#define REG_HLREG0_LPBK BIT(15)

// Section 8.2.3.22.34 MAC Flow Control Register
#define REG_MFLCN (0x04294u / 4u)
#define REG_MFLCN_RFCE BIT(3)

// Section 8.2.3.7.10 MAC Pool Select Array
#define REG_MPSAR(n) (0x0A600u / 4u + (n))

// Section 8.2.3.7.7 Multicast Table Array
#define REG_MTA(n) (0x05200u / 4u + (n))

// Section 8.2.3.27.17 PF Unicast Table Array
#define REG_PFUTA(n) (0x0F400u / 4u + (n))

// Section 8.2.3.27.15 PF VM VLAN Pool Filter
#define REG_PFVLVF(n) (0x0F100u / 4u + (n))

// Section 8.2.3.27.16 PF VM VLAN Pool Filter Bitmap
#define REG_PFVLVFB(n) (0x0F200u / 4u + (n))

// Section 8.2.3.8.2 Receive Descriptor Base Address High
#define REG_RDBAH(n) ((n) <= 63u ? (0x01004u / 4u + 0x10u * (n)) : (0x0D004u / 4u + 0x10u * ((n) -64u)))

// Section 8.2.3.8.1 Receive Descriptor Base Address Low
#define REG_RDBAL(n) ((n) <= 63u ? (0x01000u / 4u + 0x10u * (n)) : (0x0D000u / 4u + 0x10u * ((n) -64u)))

// Section 8.2.3.8.3 Receive Descriptor Length
#define REG_RDLEN(n) ((n) <= 63u ? (0x01008u / 4u + 0x10u * (n)) : (0x0D008u / 4u + 0x10u * ((n) -64u)))

// Section 8.2.3.8.8 Receive DMA Control Register
// INTERPRETATION-MISSING: Bit 0, which is not mentioned in the table, is reserved
#define REG_RDRXCTL (0x02F00u / 4u)
#define REG_RDRXCTL_CRC_STRIP BIT(1)
#define REG_RDRXCTL_DMAIDONE BIT(3)
#define REG_RDRXCTL_RSCFRSTSIZE BITS(17, 21)
#define REG_RDRXCTL_RSCACKC BIT(25)
#define REG_RDRXCTL_FCOE_WRFIX BIT(26)

// Section 8.2.3.8.5 Receive Descriptor Tail
#define REG_RDT(n) ((n) <= 63u ? (0x01018u / 4u + 0x10u * (n)) : (0x0D018u / 4u + 0x10u * ((n) -64u)))

// Section 8.2.3.10.2 DCB Transmit Descriptor Plane Control and Status
#define REG_RTTDCS (0x04900u / 4u)
#define REG_RTTDCS_ARBDIS BIT(6)

// Section 8.2.3.10.13 DCB Transmit Descriptor Plane Queue Select
#define REG_RTTDQSEL (0x04904u / 4u)

// Section 8.2.3.10.14 DCB Transmit Descriptor Plane T1 Config
#define REG_RTTDT1C (0x04908u / 4u)

// Section 8.2.3.8.10 Receive Control Register
#define REG_RXCTRL (0x03000u / 4u)
#define REG_RXCTRL_RXEN BIT(0)

// Section 8.2.3.8.6 Receive Descriptor Control
#define REG_RXDCTL(n) ((n) <= 63u ? (0x01028u / 4u + 0x10u * (n)) : (0x0D028u / 4u + 0x10u * ((n) -64u)))
#define REG_RXDCTL_ENABLE BIT(25)

// Section 8.2.3.8.9 Receive Packet Buffer Size
#define REG_RXPBSIZE(n) (0x03C00u / 4u + (n))

// Section 8.2.3.12.5 Security Rx Control
#define REG_SECRXCTRL (0x08D00u / 4u)
#define REG_SECRXCTRL_RX_DIS BIT(1)

// Section 8.2.3.12.6 Security Rx Status
#define REG_SECRXSTAT (0x08D04u / 4u)
#define REG_SECRXSTAT_SECRX_RDY BIT(0)

// Section 8.2.3.8.7 Split Receive Control Registers
#define REG_SRRCTL(n) ((n) <= 63u ? (0x01014u / 4u + 0x10u * (n)) : (0x0D014u / 4u + 0x10u * ((n) -64u)))
#define REG_SRRCTL_BSIZEPACKET BITS(0, 4)
#define REG_SRRCTL_DROP_EN BIT(28)

// Section 8.2.3.1.2 Device Status Register
#define REG_STATUS (0x00008u / 4u)
#define REG_STATUS_PCIE_MASTER_ENABLE_STATUS BIT(19)

// Section 8.2.3.9.6 Transmit Descriptor Base Address High
#define REG_TDBAH(n) (0x06004u / 4u + 0x10u * (n))

// Section 8.2.3.9.5 Transmit Descriptor Base Address Low
#define REG_TDBAL(n) (0x06000u / 4u + 0x10u * (n))

// Section 8.2.3.9.7 Transmit Descriptor Length
#define REG_TDLEN(n) (0x06008u / 4u + 0x10u * (n))

// Section 8.2.3.9.9 Transmit Descriptor Tail
#define REG_TDT(n) (0x06018u / 4u + 0x10u * (n))

// Section 8.2.3.9.11 Tx Descriptor Completion Write Back Address High
#define REG_TDWBAH(n) (0x0603Cu / 4u + 0x10u * (n))

// Section 8.2.3.9.11 Tx Descriptor Completion Write Back Address Low
#define REG_TDWBAL(n) (0x06038u / 4u + 0x10u * (n))

// Section 8.2.3.9.10 Transmit Descriptor Control
#define REG_TXDCTL(n) (0x06028u / 4u + 0x10u * (n))
#define REG_TXDCTL_PTHRESH BITS(0, 6)
#define REG_TXDCTL_HTHRESH BITS(8, 14)
#define REG_TXDCTL_ENABLE BIT(25)

// Section 8.2.3.9.13 Transmit Packet Buffer Size
#define REG_TXPBSIZE(n) (0x0CC00u / 4u + (n))

// Section 8.2.3.9.16 Tx Packet Buffer Threshold
#define REG_TXPBTHRESH(n) (0x04950u / 4u + (n))
#define REG_TXPBTHRESH_THRESH BITS(0, 9)

// Gets the value of the given register address 'reg_addr'; this is the sum of a NIC address and a register offset
static inline uint32_t reg_read_raw(volatile uint32_t* reg_addr)
{
	return tn_le_to_cpu32(*reg_addr);
}

// Get the value of register 'reg' on NIC at address 'addr'
static inline uint32_t reg_read(volatile uint32_t* addr, uint32_t reg)
{
	uint32_t result = reg_read_raw(addr + reg);
	TN_VERBOSE("read (addr %p): 0x%08" PRIx32 " -> 0x%08" PRIx32, (void*) addr, reg, result);
	return result;
}
// Get the value of field 'field' of register 'reg' on NIC at address 'addr'
static inline uint32_t reg_read_field(volatile uint32_t* addr, uint32_t reg, uint32_t field)
{
	uint32_t value = reg_read(addr, reg);
	uint32_t shift = find_first_set(field);
	return (value >> shift) & (field >> shift);
}

// Write 'value' to the given register address 'reg_addr'; this is the sum of a NIC address and a register offset
static inline void reg_write_raw(volatile uint32_t* reg_addr, uint32_t value)
{
	*reg_addr = tn_cpu_to_le32(value);
}

// Write 'value' to register 'reg' on NIC at address 'addr'
static inline void reg_write(volatile uint32_t* addr, uint32_t reg, uint32_t value)
{
	reg_write_raw(addr + reg, value);
	TN_VERBOSE("write (addr %p): 0x%08" PRIx32 " := 0x%08" PRIx32, (void*) addr, reg, value);
}
// Write 'value' to the field 'field' of register 'reg' on NIC at address 'addr'
static inline void reg_write_field(volatile uint32_t* addr, uint32_t reg, uint32_t field, uint32_t field_value)
{
	uint32_t old_value = reg_read(addr, reg);
	uint32_t shift = find_first_set(field);
	uint32_t new_value = (old_value & ~field) | (field_value << shift);
	reg_write(addr, reg, new_value);
}

// Clear (i.e., write all 0s) register 'reg' on NIC at address 'addr'
static inline void reg_clear(volatile uint32_t* addr, uint32_t reg)
{
	reg_write(addr, reg, 0);
}
// Clear (i.e., write all 0s) the field 'field' of register 'reg' on NIC at address 'addr'
static inline void reg_clear_field(volatile uint32_t* addr, uint32_t reg, uint32_t field)
{
	reg_write_field(addr, reg, field, 0);
}

// Set (i.e., write all 1s) the field 'field' of register 'reg' on NIC at address 'addr'
static inline void reg_set_field(volatile uint32_t* addr, uint32_t reg, uint32_t field)
{
	uint32_t old_value = reg_read(addr, reg);
	uint32_t new_value = old_value | field;
	reg_write(addr, reg, new_value);
}

// Check if the field 'field' of register 'reg' on NIC at address 'addr' is cleared (i.e., reads as all 0s)
static inline bool reg_is_field_cleared(volatile uint32_t* addr, uint32_t reg, uint32_t field)
{
	return reg_read_field(addr, reg, field) == 0;
}
