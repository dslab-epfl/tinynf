// All references in this file are to the Mellanox ConnectX-5 Datasheet unless otherwise noted.
// It can be found at TODO

#include "net/network.h"

#include "env/endian.h"
#include "env/memory.h"
#include "env/time.h"
#include "util/log.h"
#include <string.h>

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

#define PCIREG_COMMAND 0x04u
#define PCIREG_COMMAND_MEMORY_ACCESS_ENABLE BIT(1)
#define PCIREG_COMMAND_BUS_MASTER_ENABLE BIT(2)
#define PCIREG_COMMAND_INTERRUPT_DISABLE BIT(10)

// Driver constants
#define PCI_ID_HIGH 0x1017u // Device ID: https://pci-ids.ucw.cz/read/PC/15b3/1017
#define PCI_ID_LOW 0x15b3u  // Vendor ID: Table 1245

// These values were read from the card when the driver was written
#define REG_FW_REV_MINOR_VAL 0x1000
#define REG_FW_REV_MAJOR_VAL 0x1A00
#define REG_CMD_INTERFACE_REVISION_VAL 0xAC0F
#define REG_FW_REV_SUBMINOR_VAL 0x0500

// Table 12 Initialization Segment
#define REG_FW_REV 0x00
#define REG_FW_REV_MINOR BITS(16,31)
#define REG_FW_REV_MAJOR BITS(0,15)
#define REG_FW_REV2 0x04
#define REG_FW_REV2_CMD_INTERFACE_REVISION BITS(16,31)
#define REG_FW_REV2_SUBMINOR BITS(0,15)

#define CMDQ_SIZE 4096 // 8.24.1 HCA Command Queue size
#define REG_CMDQ_PHY_ADDR_LOW BITS(12,31)
#define REG_NIC_INTERFACE BITS(8,10)
#define REG_LOG_CMDQ_SIZE BITS(4,7)
#define REG_LOG_CMDQ_STRIDE BITS(0,3)
#define REG_COMMAND_DOORBELL_VECTOR_OFFSET 0X18

#define INITIALIZING_TIMEOUT 2 // in seconds, FW_INIT_TIMEOUT_MILI value from official driver sources for linux
#define ENABLE_HCA_DELAY 10 // in seconds, experimentally determined

#define REG_INITIALIZING_OFFSET 0x1FC
#define REG_INITIALIZING BIT(31)

// Command opcodes - Table 1153
#define OPCODE_QUERY_HCA_CAP 0x100
#define OPCODE_INIT_HCA 0x102
#define OPCODE_ENABLE_HCA 0x104
#define OPCODE_QUERY_PAGES 0x107
#define OPCODE_MANAGE_PAGES 0x108
#define OPCODE_SET_HCA_CAP 0x109
#define OPCODE_QUERY_ISSI 0x10A
#define OPCODE_SET_ISSI 0x10B
#define OPCODE_SET_DRIVER_VERSION 0x10D
#define OPCODE_QUERY_VPORT_STATE 0x750



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

uint32_t le_to_be_32(uint32_t val) {
  return ((val>>24)&0xff) | // move byte 3 to byte 0
         ((val<<8)&0xff0000) | // move byte 1 to byte 2
         ((val>>8)&0xff00) | // move byte 2 to byte 1
         ((val<<24)&0xff000000); // byte 0 to byte 3
}

// ---------------------
// Operations on the NIC
// ---------------------

// Get the value of register 'reg' on NIC at address 'addr'
static uint32_t reg_read(void* addr, uint32_t reg)
{
  uint32_t val_le = *((volatile uint32_t*)((uint8_t*) addr + reg));
  uint32_t result = le_to_be_32(val_le);
  TN_VERBOSE("MLX5 read (addr %p): 0x%08" PRIx32 " -> 0x%08" PRIx32, addr, reg, result);
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
  *reg_addr = le_to_be_32(value);
}

// Write 'value' to register 'reg' on NIC at address 'addr'
static void reg_write(void* addr, uint32_t reg, uint32_t value)
{
  reg_write_raw((volatile uint32_t*) ((uint8_t*)addr + reg), value);
  TN_VERBOSE("MLX5 write (addr %p): 0x%08" PRIx32 " := 0x%08" PRIx32, addr, reg, value);
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
  TN_VERBOSE("MLX5 PCI read: 0x%02" PRIx8 " -> 0x%08" PRIx32, reg, value);
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
  TN_VERBOSE("MLX5 PCI write: 0x%02" PRIx8 " := 0x%08" PRIx32, reg, new_value);
}

// -----------------
// Device definition
// -----------------

struct tn_net_device
{
    void* addr; // virtual address , adress 0 - init seg
    bool rx_enabled; // intel related stuff
    uint8_t _padding[7]; // bollean in structure
};

struct __attribute__((packed, aligned(4))) CommandQueueEntry {
  uint8_t type;
  uint8_t _padding_type[3];

  uint32_t input_length;

  uint32_t input_mailbox_pointer_high;

  uint8_t input_mailbox_pointer_low[3];
  uint8_t _padding_mailbox_pointer;

  // 0x10
  uint32_t command_input_inline_data[4];
  uint32_t command_output_inline_data[4];
  uint32_t output_mailbox_pointer_high;

  uint8_t _padding;
  uint8_t output_mailbox_pointer_low[3];
  uint32_t output_length;
  // 0x3C
  uint8_t status; // includes the ownership bit
  uint8_t signature;
  uint8_t _padding2;
  uint8_t token;
};

struct __attribute__((packed, aligned(4))) Enable_HCA {
    uint16_t opcode : 16;
    uint16_t _padding : 16;
    uint16_t _padding2 : 16;
    uint16_t op_mod : 16;
    uint16_t embedded_cpu_function : 1;
    uint16_t _padding3 : 15;
    uint16_t function_id : 16;
};

struct __attribute__((packed, aligned(4))) Query_Issi {
    uint16_t opcode : 16;
    uint16_t _padding : 16;
    uint16_t _padding2 : 16;
    uint16_t op_mod : 16;
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

  // TODO Check if connectx5 have these settings by default:

  // Section 7.1:
  // The driver should ensure that the Bus Master bit in the Command Register is set in the PCI
  // configuration header
  pcireg_set_field(pci_address, PCIREG_COMMAND, PCIREG_COMMAND_BUS_MASTER_ENABLE);
//  // Same for memory reads, i.e. actually using the BARs.
  pcireg_set_field(pci_address, PCIREG_COMMAND, PCIREG_COMMAND_MEMORY_ACCESS_ENABLE);
//  // Finally, since we don't want interrupts and certainly not legacy ones, make sure they're disabled
  pcireg_set_field(pci_address, PCIREG_COMMAND, PCIREG_COMMAND_INTERRUPT_DISABLE);


  uint32_t pci_bar0low = pcireg_read(pci_address, PCIREG_BAR0_LOW);
  // Sanity check: a 64-bit BAR must have bit 2 of low as 1 and bit 1 of low as 0 as per Table 9-4 Base Address Registers' Fields
  if ((pci_bar0low & BIT(2)) == 0 || (pci_bar0low & BIT(1)) != 0) {
    TN_DEBUG("BAR0 is not a 64-bit BAR");
    return false;
  }
  uint32_t pci_bar0high = pcireg_read(pci_address, PCIREG_BAR0_HIGH);
  // No need to detect the size, since we know exactly which device we're dealing with. (This also means no writes to BARs, one less chance to mess everything up)
  // BARs ==  actual pointer

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
  TN_VERBOSE("### Init - step 1");

  uint16_t fw_rev_minor = reg_read_field(device.addr, REG_FW_REV, REG_FW_REV_MINOR);
  uint16_t fw_rev_major = reg_read_field(device.addr, REG_FW_REV, REG_FW_REV_MAJOR);
  uint16_t cmd_int_rev = reg_read_field(device.addr, REG_FW_REV2, REG_FW_REV2_CMD_INTERFACE_REVISION);
  uint16_t fw_rev_subminor = reg_read_field(device.addr, REG_FW_REV2, REG_FW_REV2_SUBMINOR);

//  if (fw_rev_minor != REG_FW_REV_MINOR_VAL) {
//    TN_DEBUG("Firmware revision minor is %x, expected value is %x", fw_rev_minor, REG_FW_REV_MINOR_VAL);
//    return false;
//  }
//
//  if (fw_rev_major != REG_FW_REV_MAJOR_VAL) {
//    TN_DEBUG("Firmware revision is major %x expected value is %x", fw_rev_major, REG_FW_REV_MAJOR_VAL);
//    return false;
//  }
//
//  if (cmd_int_rev != REG_CMD_INTERFACE_REVISION_VAL) {
//    TN_DEBUG("Firmware revision is %x expected value is %x", cmd_int_rev, REG_CMD_INTERFACE_REVISION_VAL);
//    return false;
//  }
//
//  if (fw_rev_subminor != REG_FW_REV_SUBMINOR_VAL) {
//    TN_DEBUG("Firmware revision is %x expected value is %x", fw_rev_subminor, REG_FW_REV_SUBMINOR_VAL);
//    return false;
//  }

  /**
   * Step 2.
   *  Write the physical location of the command queues to the initialization segment.
   *  If using 32-bit writes, write the most significant word first.
   *  The nic_interface field is part of the least significant word
   *  and must be set to zero (Full NIC/HCA driver), as are the log_cmdq_size and log_cmdq_stride fields
   * */
  TN_VERBOSE("### Init - step 2");

  void* command_queues_virt_addr;
  uintptr_t command_queues_phys_addr;

  if (!tn_mem_allocate(CMDQ_SIZE, &command_queues_virt_addr)) {
    TN_DEBUG("Could not allocate memory for command queues");
    return false;
  }

  if (!tn_mem_virt_to_phys(command_queues_virt_addr, &command_queues_phys_addr)) {
    TN_DEBUG("Could not get a command_queues's physical address");
    return false;
  }

  TN_DEBUG("command_queues_phys_addr = %p", command_queues_phys_addr);

  // Since CMDQ_PHY_ADDR_LOW is not 32 bits but 20, the lower 12 bits
  // of the command_queues_phys_addr should be 0
  if ((command_queues_phys_addr & BITS(0, 12)) != 0) {
    TN_DEBUG("Invalid command queue address. The physical address has not the lower 12 bits set to 0!");
    return false;
  }


  // Equivalent to `iowrite32be(cmd_h, &dev->iseg->cmdq_addr_h);`
  reg_write(device.addr, 0x10, (uint32_t)(command_queues_phys_addr>>32));
  // shift the command_queues_phys_addr to write only the top 20 bits of the bottom 32 bits

  // Equivalent to `iowrite32be(cmd_l, &dev->iseg->cmdq_addr_l_sz);`

  reg_clear(device.addr, 0x14); // insteaf of the below lines
  reg_write(device.addr, 0x14, ((uint32_t) (command_queues_phys_addr & 0x00000000FFFFFFFF)));

//  reg_clear_field(device.addr, 0x14, REG_NIC_INTERFACE); // Full driver mode
//  reg_clear_field(device.addr, 0x14, REG_LOG_CMDQ_SIZE);
//  reg_clear_field(device.addr, 0x14, REG_LOG_CMDQ_STRIDE);

  TN_DEBUG("Check if the values were written correctly on initialization segment");
  reg_read(device.addr, 0x10);
  reg_read(device.addr, 0x14);

  /**
   * Step 3.
   * Read the initializing field from the initialization segment.
   * Repeat until it is cleared (INIT_SEGMENT.initializing become 0).
   * */
  TN_VERBOSE("### Init - step 3");

  IF_AFTER_TIMEOUT(INITIALIZING_TIMEOUT * 1000 * 1000,
         !reg_is_field_cleared(device.addr, REG_INITIALIZING_OFFSET, REG_INITIALIZING)) {
    TN_DEBUG("INIT_SEGMENT.initializing did not clear, cannot complete init setup");
    return false;
  }

//  uint32_t test_endianess = 0x12345678;
//
//  memcpy(&command_queues_virt_addr, &test_endianess, sizeof(test_endianess));
//  uint8_t aux3[4] = { 0 };
//  memcpy(&aux3, &command_queues_virt_addr, 4);
//  for (int i = 0; i < 4; ++i) {
//    TN_DEBUG("test endianess command queue byte[%d] = %x", i, aux3[i]);
//  }


  /**
   * Step 4.
   * Execute ENABLE_HCA command.
   * */
  TN_VERBOSE("### Init - step 4");

  uint8_t commandQueueEntryEnableHCA[64] = {0};
  commandQueueEntryEnableHCA[0] = 0x07; // type --  Table 247
  commandQueueEntryEnableHCA[7] = 12; // Length of ENABLE_HCA

  // writing the OPCODE_ENABLE_HCA (0x104) at command_input_inline_data field
  commandQueueEntryEnableHCA[16] = 1;
  commandQueueEntryEnableHCA[17] = 4;
//  struct CommandQueueEntry commandQueueEntryEnableHCA = { 0 };
//
//  commandQueueEntryEnableHCA.type = 0x07;  // Table 247
//  commandQueueEntryEnableHCA.input_length = 12;  // Length of ENABLE_HCA

  commandQueueEntryEnableHCA[63] = 1; //Table 247.  SW should set the ownership bit to 1 when posting the command
//  commandQueueEntryEnableHCA.status = 1;  //Table 247.  SW should set to 1 when posting the command
//
//  struct Enable_HCA enableHca = { 0 };
//  enableHca.opcode = OPCODE_ENABLE_HCA;
//
//  memcpy(&commandQueueEntryEnableHCA.command_input_inline_data, &enableHca, sizeof(enableHca));
//
//  // Check what was written in the command_input_inline_data
//  for (int i = 0; i < 4; ++i) {
//    TN_DEBUG("command_input_inline_data[%d]  = %x", i, commandQueueEntryEnableHCA.command_input_inline_data[i]);
//  }

  // Writing the command entry to the command queue
  TN_DEBUG("sizeof(commandQueueEntryEnableHCA) = %ld", sizeof(commandQueueEntryEnableHCA));
  memcpy(&command_queues_virt_addr, &commandQueueEntryEnableHCA, sizeof(commandQueueEntryEnableHCA));

  //TN_DEBUG("Attempt 1.8 INITIALIZATION [0x14] = %x ", reg_read(device.addr, 0x14));
  // Check what was written to the command queue
  uint8_t aux[64] = { 0 };
  memcpy(&aux, &command_queues_virt_addr, sizeof(commandQueueEntryEnableHCA));
  for (int i = 0; i < 64; ++i) {
    TN_DEBUG("Command queue byte[%d] = %x", i, aux[i]);
  }

  // Set the corresponding bit (0 for Enable_HCA as this is the first command in the queue)
  // from command_doorbell_vector to 1
  reg_write(device.addr, 0x18, 1); // - SEG fault
  // TN_DEBUG("Attempt 2 INITIALIZATION [0x14] = %x ", reg_read(device.addr, 0x14));

  IF_AFTER_TIMEOUT(ENABLE_HCA_DELAY * 1000 * 1000,
                   !reg_is_field_cleared(&command_queues_virt_addr, 0x3C, BIT(24))) {
    TN_DEBUG("command_queues_virt_addr.ownership did not clear, ENABLE_HCA did not finished");
    return false;
  }

  // Read output
  memcpy(&aux, &command_queues_virt_addr, sizeof(commandQueueEntryEnableHCA));
  for (int i = 32; i < 16+32; ++i) {
    TN_DEBUG(" -- command_output_inline_data[%d]  = %x", i, aux[i]);
  }

  for (int i = 60; i < 64; ++i) {
    TN_DEBUG(" -- command_output_inline_data[%d]  = %x", i, aux[i]);
  }

  /**
  * Step 5.
  *  Execute QUERY_ISSI command.
  * */
//  struct CommandQueueEntry commandQueueEntryQuerryIssi = { 0 };
//  commandQueueEntryQuerryIssi.type = 0x07;  // Table 247
//  commandQueueEntryQuerryIssi.input_length = 8;  // Length of QUERY_ISSI
//  commandQueueEntryQuerryIssi.status = 1;  //Table 247.  SW should set to 1 when posting the command
//
//  struct Query_Issi queryIssi = { 0 };
//  queryIssi.opcode = OPCODE_QUERY_ISSI;
//
//  int stride = 64; // TODO read this
//
//  memcpy(&commandQueueEntryQuerryIssi.command_input_inline_data + sizeof(commandQueueEntryEnableHCA) + stride, &queryIssi, sizeof(queryIssi));

  //  QUERY_ISSI command returns with BAD_OPCODE, this indicates that the supported_issi is only 0,
  //  and there is no need to perform SET_ISSI.


  /**
  * Step 6.
  *  Execute SET_ISSI command.
  * */
  // TODO

//  set the actual_issi informing the device on which ISSI to run, using
//  SET_ISSI command
// so the actual_issi which software should set for the device must be = min (sw issi, max supported_issi).

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
