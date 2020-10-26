// All references in this file are to the Mellanox ConnectX-5 Datasheet unless otherwise noted.
// It can be found at TODO

#include "net/network.h"

#include "env/endian.h"
#include "env/memory.h"
#include "env/time.h"
#include "util/log.h"

#ifndef __cplusplus
// Don't include <assert.h> since that's not allowed in freestanding implementations
#define static_assert _Static_assert
#endif

// The PCIREG_ values are register indexes.
// The REG_ values are register indexes, some of which take as argument an index.
// The sub-values are fields, which can be one or multiple bits.
// The following two macros make defining fields easier; note that bit indices start at 0.
#define BIT(n) (1u << (n))
#define BITS(start, end) (((end) == 31 ? 0u : (0xFFFFFFFFu << ((end) + 1))) ^ (0xFFFFFFFFu << (start)))
// This is for bits when we need 64-bit numbers
#define BITL(n) (1ull << (n))

#define PCIREG_ID 0x00u
// https://en.wikipedia.org/wiki/PCI_configuration_space#/media/File:Pci-config-space.svg
// PCIe Configuration Space Summary: "0x10 Base Address Register 0" (32 bit), "0x14 Base Address Register 1" (32 bit)
#define PCIREG_BAR0_LOW 0x10u
#define PCIREG_BAR0_HIGH 0x14u

// Driver constants

#define PCI_ID_HIGH 0x1017u
#define PCI_ID_LOW 0x15b3u

#define FW_REV_MINOR 0x1000
#define FW_REV_MAJOR 0x1A00
#define CMD_INTERFACE_REVISION 0xAC0F
#define FW_REV_SUBMINOR 0x0500


// ---------
// Utilities
// ---------

// Like if(...) but polls with a timeout, and executes the body only if the condition is still true after the timeout
// This is basically a way to emulate anonymous lambda functions in C (for 'condition')
static bool timed_out;
#define IF_AFTER_TIMEOUT(timeout_in_us, condition) \
		timed_out = true; \
		tn_sleep_us((timeout_in_us) % 10); \
		for (uint8_t i = 0; i < 10; i++) { \
			if (!(condition)) { \
				timed_out = false; \
				break; \
			} \
			tn_sleep_us((timeout_in_us) / 10); \
		} \
		if (timed_out)

// https://en.wikipedia.org/wiki/Find_first_set
static uint32_t find_first_set(uint32_t value)
{
  if (value == 0) {
    return 0;
  }
  uint32_t n = 0;
  while (((value >> n) & 1) == 0)
  {
    n = n + 1;
  }
  return n;
}

// ---------------------
// Operations on the NIC
// ---------------------

// Get the value of register 'reg' on NIC at address 'addr'
static uint32_t reg_read(void* addr, uint32_t reg)
{
  uint32_t val_le = *((volatile uint32_t*)((uint8_t*) addr + reg));
  uint32_t result = tn_le_to_cpu32(val_le);
  TN_VERBOSE("IXGBE read (addr %p): 0x%08" PRIx32 " -> 0x%08" PRIx32, addr, reg, result);
  return result;
}
// Get the value of field 'field' (from the REG_... macros) of register 'reg' on NIC at address 'addr'
static uint32_t reg_read_field(void* addr, uint32_t reg, uint32_t field)
{
  uint32_t value = reg_read(addr, reg);
  uint32_t shift = find_first_set(field);
  return (value >> shift) & (field >> shift);
}

// Write 'value' to the given register address 'reg_addr'; this is the sum of a NIC address and a register offset
static void reg_write_raw(volatile uint32_t* reg_addr, uint32_t value)
{
  *reg_addr = tn_cpu_to_le32(value);
}

// Write 'value' to register 'reg' on NIC at address 'addr'
static void reg_write(void* addr, uint32_t reg, uint32_t value)
{
  reg_write_raw((volatile uint32_t*) ((uint8_t*)addr + reg), value);
  TN_VERBOSE("IXGBE write (addr %p): 0x%08" PRIx32 " := 0x%08" PRIx32, addr, reg, value);
}
// Write 'value' to the field 'field' (from the REG_... #defines) of register 'reg' on NIC at address 'addr'
static void reg_write_field(void* addr, uint32_t reg, uint32_t field, uint32_t field_value)
{
  uint32_t old_value = reg_read(addr, reg);
  uint32_t shift = find_first_set(field);
  uint32_t new_value = (old_value & ~field) | (field_value << shift);
  reg_write(addr, reg, new_value);
}

// Clear (i.e., write all 0s) register 'reg' on NIC at address 'addr'
static void reg_clear(void* addr, uint32_t reg)
{
  reg_write(addr, reg, 0);
}
// Clear (i.e., write all 0s) the field 'field' (from the REG_... #defines) of register 'reg' on NIC at address 'addr'
static void reg_clear_field(void* addr, uint32_t reg, uint32_t field)
{
  reg_write_field(addr, reg, field, 0);
}

// Set (i.e., write all 1s) the field 'field' (from the REG_... #defines) of register 'reg' on NIC at address 'addr'
static void reg_set_field(void* addr, uint32_t reg, uint32_t field)
{
  uint32_t old_value = reg_read(addr, reg);
  uint32_t new_value = old_value | field;
  reg_write(addr, reg, new_value);
}

// Check if the field 'field' (from the REG_... #defines) of register 'reg' on NIC at address 'addr' is cleared (i.e., reads as all 0s)
static bool reg_is_field_cleared(void* addr, uint32_t reg, uint32_t field)
{
  return reg_read_field(addr, reg, field) == 0;
}

// Get the value of PCI register 'reg' on the device at address 'addr'
static uint32_t pcireg_read(struct tn_pci_address addr, uint8_t reg)
{
  uint32_t value = tn_pci_read(addr, reg);
  TN_VERBOSE("IXGBE PCI read: 0x%02" PRIx8 " -> 0x%08" PRIx32, reg, value);
  return value;
}

// Check if the field 'field' (from the PCIREG_... #defines) of register 'reg' on the device at address 'addr' is cleared (i.e., reads as all 0s)
static bool pcireg_is_field_cleared(struct tn_pci_address addr, uint8_t reg, uint32_t field)
{
  return (pcireg_read(addr, reg) & field) == 0;
}

// Set (i.e., write all 1s) the field 'field' (from the PCIREG_... #defines) of register 'reg' on the device at address 'addr'
static void pcireg_set_field(struct tn_pci_address addr, uint8_t reg, uint32_t field)
{
  uint32_t old_value = pcireg_read(addr, reg);
  uint32_t new_value = old_value | field;
  tn_pci_write(addr, reg, new_value);
  TN_VERBOSE("IXGBE PCI write: 0x%02" PRIx8 " := 0x%08" PRIx32, reg, new_value);
}

// -----------------
// Device definition
// -----------------

struct tn_net_device
{
    void* addr;
    bool rx_enabled;
    uint8_t _padding[7];
};


// -------------------------------------
// Section 7.2 HCA Driver Start-up
// -------------------------------------

/*
  * Read the initialization segment from offset 0 of the HCA BAR, to retrieve the versions
  of the firmware and the command interface. The driver must match the command inter-
  face revision number. The format of the initialization segment is in Table 12, “Initializa-
  tion Segment,” on page 168
  * Write the physical location of the command queues to the initialization segment. If using
  32-bit writes, write the most significant word first. The nic_interface field is part of the
  least significant word and must be set to zero (Full NIC/HCA driver), as are the log_cm-
  dq_size and log_cmdq_stride fields.
  * Read the initializing field from the initialization segment. Repeat until it is cleared
  (INIT_SEGMENT.initializing become 0).
  * Execute ENABLE_HCA command.
  * Execute QUERY_ISSI command. See “ISSI - Interface Step Sequence ID” on page 182.
  * Execute SET_ISSI command.
  * Execute QUERY_PAGES to understand the HCA need for boot pages.
  * Execute MANAGE_PAGES to provide the HCA with all required boot pages, The
  driver is allowed to give the sum of boot pages and num_init_pages.
  * Execute QUERY_HCA_CAP to retrieve the device capabilities limits.
  * Execute SET_HCA_CAP to modify system capabilities.
  * Execute QUERY_PAGES to understand the HCA need for initial pages for executing
  commands. If init_pages is 0, no need to do the MANAGE_PAGES stage.
  * Execute MANAGE_PAGES to provide the HCA with all require init-pages. This can be
  done by multiple MANAGE_PAGES commands.
  * Execute INIT_HCA command to initialize the HCA.
  * Execute SET_DRIVER_VERSION command (only in case HCA_CAP.driver_version==1). See Section 23.3.18, “SET_DRIVER_VERSION,” on page 1319.
  * Execute the “CREATE_EQ – Create EQ” on page 1356 command to create EQ. Map
  PAGE_REQUEST event to it.
  * Execute QUERY_VPORT_STATE command to get vport state.
  * For Ethernet, execute QUERY_VPORT_CONTEXT command to get permanent MAC
  address. (See Section 14.1.5, “Virtual NIC Start-Up,” on page 643).
  * Execute MODIFY_VPORT_CONTEXT command to set current MAC address. (See
  Section 14.1.5, “Virtual NIC Start-Up,” on page 643).
  * Map QP0 and QP1 to a receive WQ with the appropriate transport type. Prior to execut-
  ing this command, software must create QPs to be used for Special QPs. Execute
  SET_MAD_DEMUX to choose which MADs will be forward to SW and which will be
  handled by the device.
  * Set L2 addresses (mac_vlan), see Section 23.18, “L2 Table Commands,” on page 1499
 */

bool tn_net_device_init(const struct tn_pci_address pci_address, struct tn_net_device** out_device) {
  // The NIC supports 64-bit addresses, so pointers can't be larger
  static_assert(UINTPTR_MAX <= UINT64_MAX, "uintptr_t must fit in an uint64_t");

  // First make sure the PCI device is really an Mellanox ConnectX-5 Network Connection
  uint32_t pci_id = pcireg_read(pci_address, PCIREG_ID);

  if (pci_id != ((PCI_ID_HIGH << 16) | PCI_ID_LOW)) {
    TN_DEBUG("PCI device is not what was expected pci_id %x", pci_id);
    return false;
  }

//  // The bus master may not be enabled; enable it just in case.
//  pcireg_set_field(pci_address, PCIREG_COMMAND, PCIREG_COMMAND_BUS_MASTER_ENABLE);
//  // Same for memory reads, i.e. actually using the BARs.
//  pcireg_set_field(pci_address, PCIREG_COMMAND, PCIREG_COMMAND_MEMORY_ACCESS_ENABLE);
//  // Finally, since we don't want interrupts and certainly not legacy ones, make sure they're disabled
//  pcireg_set_field(pci_address, PCIREG_COMMAND, PCIREG_COMMAND_INTERRUPT_DISABLE);


  uint32_t pci_bar0low = pcireg_read(pci_address, PCIREG_BAR0_LOW);
  // Sanity check: a 64-bit BAR must have bit 2 of low as 1 and bit 1 of low as 0 as per Table 9-4 Base Address Registers' Fields
  if ((pci_bar0low & BIT(2)) == 0 || (pci_bar0low & BIT(1)) != 0) {
    TN_DEBUG("BAR0 is not a 64-bit BAR");
    return false;
  }
  uint32_t pci_bar0high = pcireg_read(pci_address, PCIREG_BAR0_HIGH);
  // No need to detect the size, since we know exactly which device we're dealing with. (This also means no writes to BARs, one less chance to mess everything up)

  struct tn_net_device device = { 0 };
  // Section 9.3.6.1 Memory and IO Base Address Registers:
  // As indicated in Table 9-4, the low 4 bits are read-only and not part of the address
  uintptr_t dev_phys_addr = (((uint64_t) pci_bar0high) << 32) | (pci_bar0low & ~BITS(0,3));
  // Section 8.1 Address Regions: "Region Size" of "Internal registers memories and Flash (memory BAR)" is "128 KB + Flash_Size"
  // Thus we can ask for 128KB, since we don't know the flash size (and don't need it thus no need to actually check it)
  if (!tn_mem_phys_to_virt(dev_phys_addr, 128 * 1024, &device.addr)) {
    return false;
  }

  TN_VERBOSE("Device %02" PRIx8 ":%02" PRIx8 ".%" PRIx8 " mapped to %p", pci_address.bus, pci_address.device, pci_address.function, device.addr);

  /**
   * Step 1.
   * Read the initialization segment from offset 0 of the HCA BAR,
   * to retrieve the versions of the firmware and the command interface.
   * The driver must match the command interface revision number.
   * The format of the initialization segment is in Table 12, “Initialization Segment,” on page 168
   * */
  uint32_t fw_rev = reg_read(device.addr, 0x00);
  uint32_t cmd_rev_fw_rev_subminor = reg_read(device.addr, 0x04);
  uint16_t fw_rev_minor = fw_rev >> 16;
  uint16_t fw_rev_major = (uint16_t) fw_rev & 0x0000FFFF;
  uint16_t cmd_int_rev = cmd_rev_fw_rev_subminor >> 16;
  uint16_t fw_rev_subminor = (uint16_t) cmd_rev_fw_rev_subminor & 0x0000FFFF;

//  TN_DEBUG("fw_rev %x", fw_rev);
//  TN_DEBUG("cmd_rev_fw_rev_subminor %x", cmd_rev_fw_rev_subminor);
//  TN_DEBUG("fw_rev_minor %x", fw_rev_minor);
//  TN_DEBUG("fw_rev_major %x", fw_rev_major);
//  TN_DEBUG("cmd_int_rev %x", cmd_int_rev);
//  TN_DEBUG("fw_rev_subminor %x", fw_rev_subminor);

  if (fw_rev_minor != FW_REV_MINOR) {
    TN_DEBUG("Firmware revision minor is %x, expected value is %x", fw_rev_minor, FW_REV_MINOR);
    return false;
  }

  if (fw_rev_major != FW_REV_MAJOR) {
    TN_DEBUG("Firmware revision is major %x expected value is %x", fw_rev_major, FW_REV_MAJOR);
    return false;
  }

  if (cmd_int_rev != CMD_INTERFACE_REVISION) {
    TN_DEBUG("Firmware revision is %x expected value is %x", cmd_int_rev, CMD_INTERFACE_REVISION);
    return false;
  }

  if (fw_rev_subminor != FW_REV_SUBMINOR) {
    TN_DEBUG("Firmware revision is %x expected value is %x", fw_rev_subminor, FW_REV_SUBMINOR);
    return false;
  }

  /**
   * Step 2.
   *  Write the physical location of the command queues to the initialization segment.
   *  If using 32-bit writes, write the most significant word first.
   *  The nic_interface field is part of the least significant word
   *  and must be set to zero (Full NIC/HCA driver), as are the log_cmdq_size and log_cmdq_stride fields
   * */
  // TODO


  /**
   * Step 3.
   * Read the initializing field from the initialization segment.
   * Repeat until it is cleared (INIT_SEGMENT.initializing become 0).
   * */
  // TODO

  /**
   * Step 4.
   * Execute ENABLE_HCA command.
   * */
   // TODO

  return true;
}

bool tn_net_device_set_promiscuous(struct tn_net_device* const device)
{
  // TODO
  return true;
}


bool tn_net_agent_init(struct tn_net_agent** out_agent)
{
  // TODO
  return true;
}

bool tn_net_agent_set_input(struct tn_net_agent* const agent, struct tn_net_device* const device)
{
  // TODO
  return true;
}

bool tn_net_agent_add_output(struct tn_net_agent* const agent, struct tn_net_device* const device)
{
  // TODO
  return true;
}

bool tn_net_agent_receive(struct tn_net_agent* agent, uint8_t** out_packet, uint16_t* out_packet_length)
{
  // TODO
  return true;
}

void tn_net_run(uint64_t agents_count, struct tn_net_agent** agents, tn_net_packet_handler** handlers, void** states)
{
  // TODO
}
