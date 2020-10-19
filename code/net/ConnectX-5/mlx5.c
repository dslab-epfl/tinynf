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

#define PCIREG_ID 0x00u

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

// Get the value of PCI register 'reg' on the device at address 'addr'
static uint32_t pcireg_read(struct tn_pci_address addr, uint8_t reg)
{
  uint32_t value = tn_pci_read(addr, reg);
  TN_VERBOSE("IXGBE PCI read: 0x%02" PRIx8 " -> 0x%08" PRIx32, reg, value);
  return value;
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
  uint32_t tmp1 = pcireg_read(pci_address, 0x01);
  uint32_t tmp2 = pcireg_read(pci_address, 0x02);
  uint32_t tmp3 = pcireg_read(pci_address, 0x03);
  uint32_t tmp4 = pcireg_read(pci_address, 0x04);


  TN_DEBUG(" pci_id, tmp1, tmp2, tmp3, tmp4  = %x %x %x %x %x", pci_id, tmp1, tmp2, tmp3, tmp4);
  if (pci_id != ((0x1017u << 16) | 0x15b3u)) {
    TN_DEBUG("PCI device is not what was expected pci_id %x", pci_id);
    return false;
  }

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
