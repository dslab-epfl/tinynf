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
//#define BITL(n) (1ull << (n))

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
#define PAGE_SIZE 4096 // 23.3.2  MANAGE_PAGES
#define MAILBOX_BLOCK_SIZE 576 // Table 249 :
//#define REG_CMDQ_PHY_ADDR_LOW BITS(12,31)
//#define REG_NIC_INTERFACE BITS(8,10)
//#define REG_LOG_CMDQ_SIZE BITS(4,7)
//#define REG_LOG_CMDQ_STRIDE BITS(0,3)
#define REG_COMMAND_DOORBELL_VECTOR_OFFSET 0x18

#define INITIALIZING_TIMEOUT 2 // in seconds, FW_INIT_TIMEOUT_MILI value from official driver sources for linux
#define ENABLE_HCA_DELAY 10 // in seconds, experimentally determined

#define REG_INITIALIZING_OFFSET 0x1FC
#define REG_INITIALIZING BIT(31)

// Command Queue Entry offsets - Table 246
#define CMD_Q_E_TYPE_OFFSET 0x00
#define CMD_Q_E_INPUT_LENGTH_OFFSET 0x04
#define CMD_Q_E_INPUT_MAILBOX_PTR_HIGH_OFFSET 0x08
#define CMD_Q_E_INPUT_MAILBOX_PTR_LOW_OFFSET 0x0C
#define CMD_Q_E_CMD_INPUT_INLINE_DATA_OFFSET 0x10
#define CMD_Q_E_CMD_OUTPUT_INLINE_DATA_OFFSET 0x20
#define CMD_Q_E_OUTPUT_MAILBOX_PTR_HIGH_OFFSET 0x30
#define CMD_Q_E_OUTPUT_MAILBOX_PTR_LOW_OFFSET 0x34
#define CMD_Q_E_OUTPUT_LENGTH_OFFSET 0x38
#define CMD_Q_E_STATUS_OFFSET 0x3C
//#define CMD_Q_E_SIGNATURE_OFFSET 0x3C
#define CMD_Q_E_SIZE 0x40

// QUERY_HCA_CAP op_modes
#define GEN_DEV_CAP 0x0

// QUERY_PAGES op_modes
#define BOOT_PAGES 0x1
#define INIT_PAGES 0x2
#define REGULAR_PAGES 0x3

// MANAGES_PAGES op_modes
#define ALLOCATION_FAIL 0x0
#define ALLOCATION_SUCCESS 0x1
#define HCA_RETURN_PAGES 0x2

// Table Table 247 - Command delivery status
#define SUCCESS_STATUS 0x00
#define SIGNATURE_ERR_STATUS 0x01
#define TOKEN_ERR_STATUS 0x02
#define BAD_BLOCK_NUMBER_STATUS 0x03
#define BAD_OUTPUT_POINTER_STATUS 0x04
#define BAD_INPUT_POINTER_STATUS 0x05
#define INTERNAL_ERR_STATUS 0x06
#define INPUT_LEN_ERR_STATUS 0x07
#define OUTPUT_LEN_ERR_STATUS 0x08
#define RESERVED_NOT_ZERO_STATUS 0x09
#define BAD_COMMAND_TYPE_STATUS 0x10

#define CMD_EXECUTION_TIMEOUT_ERR 1
#define CMD_DELIVERY_STATUS_ERR 2
#define CMD_OUTPUT_STATUS_ERR 3

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
//0x1234 --> 0x3412

uint32_t le_to_be_32(uint32_t val) {
  return ((val>>24)&0xff) | // move byte 3 to byte 0
         ((val<<8)&0xff0000) | // move byte 1 to byte 2
         ((val>>8)&0xff00) | // move byte 2 to byte 1
         ((val<<24)&0xff000000); // byte 0 to byte 3
}

uint16_t le_to_be_16(uint16_t val) {
  return (( val << 8 ) | ( val >> 8));
}

void buffer_write_16b_be(void* address, uint32_t offset, uint16_t value) {
  ((volatile uint16_t *) address)[2 * offset/4] = le_to_be_16(value);
}

uint16_t buffer_read_16b_be(void* address, uint32_t offset) {
  return le_to_be_16(((volatile uint16_t *) address)[2 * offset/4]);
}

void buffer_write_be(void* address, uint32_t offset, uint32_t value) {
  ((volatile uint32_t *) address)[offset/4] = le_to_be_32(value);
}

uint32_t buffer_read_be(void* address, uint32_t offset) {
  return le_to_be_32(((volatile uint32_t *) address)[offset/4]);
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

enum {
    MLX5_CMD_STAT_OK			= 0x0,
    MLX5_CMD_STAT_INT_ERR			= 0x1,
    MLX5_CMD_STAT_BAD_OP_ERR		= 0x2,
    MLX5_CMD_STAT_BAD_PARAM_ERR		= 0x3,
    MLX5_CMD_STAT_BAD_SYS_STATE_ERR		= 0x4,
    MLX5_CMD_STAT_BAD_RES_ERR		= 0x5,
    MLX5_CMD_STAT_RES_BUSY			= 0x6,
    MLX5_CMD_STAT_LIM_ERR			= 0x8,
    MLX5_CMD_STAT_BAD_RES_STATE_ERR		= 0x9,
    MLX5_CMD_STAT_IX_ERR			= 0xa,
    MLX5_CMD_STAT_NO_RES_ERR		= 0xf,
    MLX5_CMD_STAT_BAD_INP_LEN_ERR		= 0x50,
    MLX5_CMD_STAT_BAD_OUTP_LEN_ERR		= 0x51,
    MLX5_CMD_STAT_BAD_QP_STATE_ERR		= 0x10,
    MLX5_CMD_STAT_BAD_PKT_ERR		= 0x30,
    MLX5_CMD_STAT_BAD_SIZE_OUTS_CQES_ERR	= 0x40,
};

static const char *cmd_status_str(uint8_t status)
{
  switch (status) {
    case MLX5_CMD_STAT_OK:
      return "OK";
    case MLX5_CMD_STAT_INT_ERR:
      return "internal error";
    case MLX5_CMD_STAT_BAD_OP_ERR:
      return "bad operation";
    case MLX5_CMD_STAT_BAD_PARAM_ERR:
      return "Parameter not supported, parameter out of range, reserved not equal 0";
    case MLX5_CMD_STAT_BAD_SYS_STATE_ERR:
      return "System was not enabled or bad system state";
    case MLX5_CMD_STAT_BAD_RES_ERR:
      return "bad resource";
    case MLX5_CMD_STAT_RES_BUSY:
      return "resource busy";
    case MLX5_CMD_STAT_LIM_ERR:
      return "limits exceeded";
    case MLX5_CMD_STAT_BAD_RES_STATE_ERR:
      return "bad resource state: Resource is not in the appropriate state or ownership";
    case MLX5_CMD_STAT_IX_ERR:
      return "bad index";
    case MLX5_CMD_STAT_NO_RES_ERR:
      return "no resources";
    case MLX5_CMD_STAT_BAD_INP_LEN_ERR:
      return "bad input length";
    case MLX5_CMD_STAT_BAD_OUTP_LEN_ERR:
      return "bad output length";
    case MLX5_CMD_STAT_BAD_QP_STATE_ERR:
      return "bad QP state";
    case MLX5_CMD_STAT_BAD_PKT_ERR:
      return "bad packet (discarded)";
    case MLX5_CMD_STAT_BAD_SIZE_OUTS_CQES_ERR:
      return "bad size too many outstanding CQEs";
    default:
      return "unknown status";
  }
}

static inline const char *command_delivery_status_str (uint8_t status)
{
  switch (status) {
    case SUCCESS_STATUS:
      return "SUCCESS - no errors";
    case SIGNATURE_ERR_STATUS:
      return "SIGNATURE_ERR";
    case TOKEN_ERR_STATUS:
      return "TOKEN_ERR";
    case BAD_BLOCK_NUMBER_STATUS:
      return "BAD_BLOCK_NUMBER";
    case BAD_OUTPUT_POINTER_STATUS:
      return "BAD_OUTPUT_POINTER - pointer not aligned to mailbox size";
    case BAD_INPUT_POINTER_STATUS:
      return "BAD_INPUT_POINTER - pointer not aligned to mailbox size";
    case INTERNAL_ERR_STATUS:
      return "INTERNAL_ERR";
    case INPUT_LEN_ERR_STATUS:
      return "INPUT_LEN_ERR - input length less than 0x8";
    case OUTPUT_LEN_ERR_STATUS:
      return "OUTPUT_LEN_ERR- output length less than 0x8";
    case RESERVED_NOT_ZERO_STATUS:
      return "RESERVED_NOT_ZERO";
    case BAD_COMMAND_TYPE_STATUS:
      return "BAD_COMMAND_TYPE";
    default:
      return "Unrecognized status";
  }
}

// Cleans only the first command entry
void clean_buffer(void* buffer, int size_in_bytes) {
  for (uint32_t i = 0; i < size_in_bytes/sizeof(uint32_t); ++i) {
    ((volatile uint32_t *) (buffer))[i] = 0;
  }
}

void dump_command_entry_values(void* command_queues_virt_addr) {
  TN_DEBUG("Command entry after command execution");
  for (uint32_t i = 0; i < CMD_Q_E_SIZE/sizeof(uint32_t); ++i) {
    if (i < CMD_Q_E_OUTPUT_MAILBOX_PTR_HIGH_OFFSET/4 && i >= CMD_Q_E_CMD_OUTPUT_INLINE_DATA_OFFSET/4) {
      TN_DEBUG("cmd output - command_queues_virt_addr[%d] 0x%08X", i, ((volatile uint32_t *) command_queues_virt_addr)[i]);
    } else {
      TN_DEBUG("command_queues_virt_addr[%d] 0x%08X", i, ((volatile uint32_t *) command_queues_virt_addr)[i]);
    }
  }
}

void dump_output_mailbox(void* output_mailbox) {
  TN_DEBUG("output_mailbox content ");
  for (uint32_t i = 0; i < MAILBOX_BLOCK_SIZE/sizeof(uint32_t); ++i) {
    TN_DEBUG("output_mailbox[%d] 0x%08X", i, ((volatile uint32_t *) output_mailbox)[i]);
  }
}


int cmd_exec_enable_hca(void* command_queues_virt_addr, uint32_t command_index, void* device_addr) {

  TN_VERBOSE("### Init - step 4: Execute ENABLE_HCA");

  // Type of transport that carries the command: 0x7: PCIe_cmd_if_transport - Table 247
  buffer_write_be(command_queues_virt_addr, CMD_Q_E_TYPE_OFFSET, 0x07000000);
  // input_length for ENABLE_HCA length is 12 bytes: Table 1255
  buffer_write_be(command_queues_virt_addr, CMD_Q_E_INPUT_LENGTH_OFFSET, 0x0C);
  // OPCODE_ENABLE_HCA - Table 1153
  buffer_write_16b_be(command_queues_virt_addr, CMD_Q_E_CMD_INPUT_INLINE_DATA_OFFSET, 0x0104);
  // output_length - Table 1153
  buffer_write_be(command_queues_virt_addr, CMD_Q_E_OUTPUT_LENGTH_OFFSET, 0x0C);
  // SW should set to 1 when posting the command. HW will change to zero to move ownership bit to SW. - Table 247
  buffer_write_be(command_queues_virt_addr, CMD_Q_E_STATUS_OFFSET, 0x01);

  // Set the corresponding bit (0 for Enable_HCA as this is the first command in the queue) from command_doorbell_vector to 1
  reg_write(device_addr, REG_COMMAND_DOORBELL_VECTOR_OFFSET, 1 << command_index);

  IF_AFTER_TIMEOUT(ENABLE_HCA_DELAY * 1000 * 1000,
                   (((volatile uint32_t *) command_queues_virt_addr)[15] & BIT(0))) {
    TN_DEBUG("command_queues_virt_addr.ownership did not clear, ENABLE_HCA did not finished");
    return CMD_EXECUTION_TIMEOUT_ERR;
  }

  // Read Command delivery status
  uint8_t status = (uint8_t) ((buffer_read_be(command_queues_virt_addr, CMD_Q_E_STATUS_OFFSET) & 0x000000FF) >> 1);
  if (status != 0x0) {
    TN_DEBUG("ENABLE_HCA command delivery status is 0x%02X, %s", status, command_delivery_status_str(status));
    return CMD_DELIVERY_STATUS_ERR;
  }

  // Read output status (output length is 12)
  uint8_t output_status = (uint8_t) ((buffer_read_be(command_queues_virt_addr, CMD_Q_E_CMD_OUTPUT_INLINE_DATA_OFFSET) & 0xFF000000) >> 24);
  if (output_status != 0x0) {
    TN_DEBUG("ENABLE_HCA output status is 0x%02X, %s", output_status, cmd_status_str(output_status));
    dump_command_entry_values(command_queues_virt_addr);
    return CMD_OUTPUT_STATUS_ERR;
  }

  // If DEBUG_MODE is ON, print the command entry values
  dump_command_entry_values(command_queues_virt_addr);

  // Set memory values to 0 for the first command entry in command queue
  clean_buffer(command_queues_virt_addr, CMD_Q_E_SIZE);

  return 0;
}

int cmd_exec_query_issi(void* command_queues_virt_addr, uint32_t command_index, void* device_addr,
                        void* output_mailbox_head_virt_addr, uintptr_t output_mailbox_head_phys_addr,
                        uint32_t* current_issi, uint32_t* minimum_issi) {
  TN_VERBOSE("### Init - step 5: Execute QUERY_ISSI");

  // Type of transport that carries the command: 0x7: PCIe_cmd_if_transport - Table 247
  buffer_write_be(command_queues_virt_addr, CMD_Q_E_TYPE_OFFSET, 0x07000000);
  // input_length for QUERY_ISSI length is 12 bytes: Table 1255
  buffer_write_be(command_queues_virt_addr, CMD_Q_E_INPUT_LENGTH_OFFSET, 0x0C);
  // OPCODE_QUERY_ISSI - Table 1153
  buffer_write_16b_be(command_queues_virt_addr, CMD_Q_E_CMD_INPUT_INLINE_DATA_OFFSET, 0x010A);
  // set the output_mailbox_pointer high
  buffer_write_be(command_queues_virt_addr, CMD_Q_E_OUTPUT_MAILBOX_PTR_HIGH_OFFSET,
                  (uint32_t)(output_mailbox_head_phys_addr >> 32));
  // set the output_mailbox_pointer low
  buffer_write_be(command_queues_virt_addr, CMD_Q_E_OUTPUT_MAILBOX_PTR_LOW_OFFSET,
                  (uint32_t)(output_mailbox_head_phys_addr & 0x00000000FFFFFFFF));
  // output_length - Table 1153
  buffer_write_be(command_queues_virt_addr, CMD_Q_E_OUTPUT_LENGTH_OFFSET, 0x70);
  // SW should set to 1 when posting the command. HW will change to zero to move ownership bit to SW. - Table 247
  buffer_write_be(command_queues_virt_addr, CMD_Q_E_STATUS_OFFSET, 0x01);
  //  If QUERY_ISSI command returns with BAD_OPCODE, this indicates that the supported_issi is only 0,
  //  and there is no need to perform SET_ISSI.
  // Set the corresponding bit (0 for QUERY_ISSI as this is the first command in the queue) from command_doorbell_vector to 1
  reg_write(device_addr, REG_COMMAND_DOORBELL_VECTOR_OFFSET, 1 << command_index);

  IF_AFTER_TIMEOUT(ENABLE_HCA_DELAY * 1000 * 1000,
                   (((volatile uint32_t *) command_queues_virt_addr)[CMD_Q_E_STATUS_OFFSET] & BIT(0))) {
    TN_DEBUG("command_queues_virt_addr.ownership did not clear, QUERY_ISSI did not finished");
    return CMD_EXECUTION_TIMEOUT_ERR;;
  }

  // Read Command delivery status
  uint8_t status = (uint8_t) ((buffer_read_be(command_queues_virt_addr, CMD_Q_E_STATUS_OFFSET) & 0x000000FF) >> 1);
  if (status != 0x0) {
    TN_DEBUG("QUERY_ISSI command delivery status is 0x%02X, %s", status, command_delivery_status_str(status));
    return CMD_DELIVERY_STATUS_ERR;
  }

  // TODO: if QUERY_ISSI command returns with BAD_OPCODE, this indicates that the supported_issi is only 0, and there is no need to perform SET_ISSI.
  // Read output status (output length is 12)
  uint8_t output_status = (uint8_t) ((buffer_read_be(command_queues_virt_addr, CMD_Q_E_CMD_OUTPUT_INLINE_DATA_OFFSET) & 0xFF000000) >> 24);
  if (output_status != 0x0) {
    TN_DEBUG("QUERY_ISSI output status is 0x%02X, %s", output_status, cmd_status_str(output_status));
    return CMD_OUTPUT_STATUS_ERR;
  }

  // Table 1265
  *current_issi = ((volatile uint32_t *) command_queues_virt_addr)[(CMD_Q_E_CMD_OUTPUT_INLINE_DATA_OFFSET+0x08)/4];
  TN_VERBOSE("current_issi = %d", *current_issi);
  // If DEBUG_MODE is ON, print the command entry values
  dump_command_entry_values(command_queues_virt_addr);

  // Compute the minimum_ISSI: See details in Table 1266
  // Starting from 4, since the first 16 bytes (4 rows ) are reserved
  for (int i = 4; i < 144; ++i) {
    if (((volatile uint32_t *) (output_mailbox_head_virt_addr))[i] != 0) {
      TN_VERBOSE("supported_issi[%d] = %x", i-0x04, ((volatile uint32_t *) (output_mailbox_head_virt_addr))[i]);
      TN_DEBUG("find first = %d", find_first_set(((volatile uint32_t *) (output_mailbox_head_virt_addr))[i]));
      // Table 1266 : BIT N indicates if ISSI = N supported
      *minimum_issi = 32 * (i - 0x04 - 1) +  find_first_set(((volatile uint32_t *) (output_mailbox_head_virt_addr))[i]);
      TN_VERBOSE("minimum_issi = %d", *minimum_issi);
      break;
    }
  }

  // Set memory values to 0 for the first command entry in command queue
  clean_buffer(command_queues_virt_addr, CMD_Q_E_SIZE);
  clean_buffer(output_mailbox_head_virt_addr, MAILBOX_BLOCK_SIZE);

  return 0;
}

int cmd_exec_set_issi(void* command_queues_virt_addr, uint32_t command_index, void* device_addr,
                      uint32_t minimum_issi) {

  TN_VERBOSE("### Init - step 6: Execute SET_ISSI");
  // Type of transport that carries the command: 0x7: PCIe_cmd_if_transport - Table 247
  buffer_write_be(command_queues_virt_addr, CMD_Q_E_TYPE_OFFSET, 0x07000000);
  // input_length for SET_ISSI length is 12 bytes: Table 1255
  buffer_write_be(command_queues_virt_addr, CMD_Q_E_INPUT_LENGTH_OFFSET, 0x0C);
  // OPCODE_SET_ISSI - Table 1267
  buffer_write_16b_be(command_queues_virt_addr, CMD_Q_E_CMD_INPUT_INLINE_DATA_OFFSET, 0x010B);
  // Current Interface Step Sequence ID to work with. - Table 1267
  /* Disclaimer! The datasheet indicates minimum_issi value calculated above, but the device answer for the minimum_pages is
   *  SET_ISSI output status is 0x03, Parameter not supported, parameter out of range, reserved not equal 0 .
   *  using value 1 will not create a problem */
  buffer_write_be(command_queues_virt_addr, CMD_Q_E_CMD_INPUT_INLINE_DATA_OFFSET+0x08, 1); // minimum_issi
  // output_length - Table 1269
  buffer_write_be(command_queues_virt_addr, CMD_Q_E_OUTPUT_LENGTH_OFFSET, 0x0C);
  // SW should set to 1 when posting the command. HW will change to zero to move ownership bit to SW. - Table 247
  buffer_write_be(command_queues_virt_addr, CMD_Q_E_STATUS_OFFSET, 0x01);

  // Set the corresponding bit (0 for SET_ISSI as this is the first command in the queue) from command_doorbell_vector to 1
  reg_write(device_addr, REG_COMMAND_DOORBELL_VECTOR_OFFSET, 1 << command_index);

  IF_AFTER_TIMEOUT(ENABLE_HCA_DELAY * 1000 * 1000,
                   (((volatile uint32_t *) command_queues_virt_addr)[15] & BIT(0))) {
    TN_DEBUG("command_queues_virt_addr.ownership did not clear, SET_ISSI did not finished");
    return CMD_EXECUTION_TIMEOUT_ERR;
  }

  // Read Command delivery status
  uint8_t status = (uint8_t) ((buffer_read_be(command_queues_virt_addr, CMD_Q_E_STATUS_OFFSET) & 0x000000FF) >> 1);
  if (status != 0x0) {
    TN_DEBUG("SET_ISSI command delivery status is 0x%02X, %s", status, command_delivery_status_str(status));
    return CMD_DELIVERY_STATUS_ERR;
  }

  // Read output status (output length is 12)
  uint8_t output_status = (uint8_t) ((buffer_read_be(command_queues_virt_addr, CMD_Q_E_CMD_OUTPUT_INLINE_DATA_OFFSET) & 0xFF000000) >> 24);
  if (output_status != 0x0) {
    TN_DEBUG("SET_ISSI output status is 0x%02X, %s", output_status, cmd_status_str(output_status));
    return CMD_OUTPUT_STATUS_ERR;
  }

  // If DEBUG_MODE is ON, print the command entry values
  dump_command_entry_values(command_queues_virt_addr);

  // Set memory values to 0 for the first command entry in command queue
  clean_buffer(command_queues_virt_addr, CMD_Q_E_SIZE);

  return 0;
}

int cmd_exec_query_pages(void* command_queues_virt_addr, uint32_t command_index, void* device_addr, int* num_pages, int op_mod) {
  int step_nr = op_mod == BOOT_PAGES ? 7 : 11;
  TN_VERBOSE("### Init - step %d: Execute QUERY_PAGES", step_nr);
  // Type of transport that carries the command: 0x7: PCIe_cmd_if_transport - Table 247
  buffer_write_be(command_queues_virt_addr, CMD_Q_E_TYPE_OFFSET, 0x07000000);
  // input_length for QUERY_PAGES length is 12 bytes: Table 1156
  buffer_write_be(command_queues_virt_addr, CMD_Q_E_INPUT_LENGTH_OFFSET, 0x0C);
  // OPCODE_QUERY_PAGES - Table 1153
  buffer_write_16b_be(command_queues_virt_addr, CMD_Q_E_CMD_INPUT_INLINE_DATA_OFFSET, 0x0107);
  // op_mod boot_pages/init_pages
  buffer_write_be(command_queues_virt_addr, CMD_Q_E_CMD_INPUT_INLINE_DATA_OFFSET+0x04, op_mod);
  // embedded_cpu_function should be 0x00: HOST - Function on external Host

  // output_length - Table 1269
  buffer_write_be(command_queues_virt_addr, CMD_Q_E_OUTPUT_LENGTH_OFFSET, 0x10);
  // SW should set to 1 when posting the command. HW will change to zero to move ownership bit to SW. - Table 247
  buffer_write_be(command_queues_virt_addr, CMD_Q_E_STATUS_OFFSET, 0x01);

  // Set the corresponding bit (0 for QUERY_PAGES as this is the first command in the queue) from command_doorbell_vector to 1
  reg_write(device_addr, REG_COMMAND_DOORBELL_VECTOR_OFFSET, 1 << command_index);

  IF_AFTER_TIMEOUT(ENABLE_HCA_DELAY * 1000 * 1000,
                   (((volatile uint32_t *) command_queues_virt_addr)[15] & BIT(0))) {
    TN_DEBUG("command_queues_virt_addr.ownership did not clear, QUERY_PAGES did not finished");
    return CMD_EXECUTION_TIMEOUT_ERR;
  }

  // Read Command delivery status
  uint8_t status = (uint8_t) ((buffer_read_be(command_queues_virt_addr, CMD_Q_E_STATUS_OFFSET) & 0x000000FF) >> 1);
  if (status != 0x0) {
    TN_DEBUG("QUERY_PAGES command delivery status is 0x%02X, %s", status, command_delivery_status_str(status));
    return CMD_DELIVERY_STATUS_ERR;
  }

  // Read output status (output length is 12)
  uint8_t output_status = (uint8_t) ((buffer_read_be(command_queues_virt_addr, CMD_Q_E_CMD_OUTPUT_INLINE_DATA_OFFSET) & 0xFF000000) >> 24);
  if (output_status != 0x0) {
    TN_DEBUG("QUERY_PAGES output status is 0x%02X, %s", output_status, cmd_status_str(output_status));
    return CMD_OUTPUT_STATUS_ERR;
  }

  *num_pages = buffer_read_be(command_queues_virt_addr, CMD_Q_E_CMD_OUTPUT_INLINE_DATA_OFFSET + 0x0C);
  /*
   * Number of pages the device requires from the driver
   * (positive numbers means driver should provide pages.
   * Negative number means the driver should reclaim pages).
   * */
  TN_VERBOSE("QUERY_PAGES num_pages %d", *num_pages);

  if (*num_pages < 0) {
    TN_DEBUG("Number of pages the device requires from the driver is Negative");
    return false;
  }

  // If DEBUG_MODE is ON, print the command entry values
  dump_command_entry_values(command_queues_virt_addr);

  // Set memory values to 0 for the first command entry in command queue
  clean_buffer(command_queues_virt_addr, CMD_Q_E_SIZE);

  return 0;
}

int cmd_exec_manage_pages(void* command_queues_virt_addr, uint32_t command_index, void* device_addr,
                          void* input_mailbox_head_virt_addr, uintptr_t input_mailbox_head_phys_addr,
                          void* output_mailbox_head_virt_addr, uintptr_t output_mailbox_head_phys_addr, int num_pages) {
  TN_VERBOSE("### Init - step 8:Execute MANAGE_PAGES");
  void* memoryPages;
  uintptr_t memoryPagesPhysAddr;

  // Alocate - num_pages * 4096 and put boot_num_pages entries
  if (!tn_mem_allocate(num_pages * PAGE_SIZE, &memoryPages)) {
    TN_DEBUG("Could not allocate memory for memoryPages");
    return 4;
  }

  if (!tn_mem_virt_to_phys(memoryPages, &memoryPagesPhysAddr)) {
    TN_DEBUG("Could not get the memoryPages's physical address");
    return 5;
  }

  TN_DEBUG("memoryPages = %p\n memoryPagesPhysAddr = %p", memoryPages, memoryPagesPhysAddr);

  for (int i = 0; i < num_pages; i++) {
    // writing pa_h
    ((volatile uint32_t *) input_mailbox_head_virt_addr)[2 * i] =
            le_to_be_32((uint32_t)((memoryPagesPhysAddr + i * PAGE_SIZE) >> 32));
    // writing pa_l

    TN_DEBUG("input_mailbox_head_virt_addr lower for i = %d, 0x%08x ", i, (uint32_t)((memoryPagesPhysAddr + i * PAGE_SIZE) & 0x00000000FFFFF000));
    ((volatile uint32_t *) input_mailbox_head_virt_addr)[2 * i + 1] =
            le_to_be_32((uint32_t)((memoryPagesPhysAddr + i * PAGE_SIZE) & 0x00000000FFFFF000));
  }



  // check that the right values were written:
  dump_output_mailbox(input_mailbox_head_virt_addr);

  // Type of transport that carries the command: 0x7: PCIe_cmd_if_transport - Table 247
  buffer_write_be(command_queues_virt_addr, CMD_Q_E_TYPE_OFFSET, 0x07000000);
  // input_length for MANAGE_PAGES length is `16 + 8 * boot_num_pages bytes`: Table 1160
  buffer_write_be(command_queues_virt_addr, CMD_Q_E_INPUT_LENGTH_OFFSET, 16 + 8 * num_pages);
  // writing the input mailbox address
  buffer_write_be(command_queues_virt_addr, CMD_Q_E_INPUT_MAILBOX_PTR_HIGH_OFFSET,
                  (uint32_t)(input_mailbox_head_phys_addr >> 32));
  buffer_write_be(command_queues_virt_addr, CMD_Q_E_INPUT_MAILBOX_PTR_LOW_OFFSET,
                  (uint32_t)(input_mailbox_head_phys_addr & 0x00000000FFFFFFFF));
  // OPCODE_MANAGE_PAGES - Table 1153
  buffer_write_16b_be(command_queues_virt_addr, CMD_Q_E_CMD_INPUT_INLINE_DATA_OFFSET, 0x0108);
  // op_mod - 0x1: ALLOCATION_SUCCESS - SW gives pages to HCA. Input parameter and input mailbox are valid.
  buffer_write_be(command_queues_virt_addr, CMD_Q_E_CMD_INPUT_INLINE_DATA_OFFSET + 0x04, ALLOCATION_SUCCESS);
  /* embedded_cpu_function should be 0x00: HOST - Function on external Host */
  // set the output_mailbox_pointer high
  buffer_write_be(command_queues_virt_addr, CMD_Q_E_OUTPUT_MAILBOX_PTR_HIGH_OFFSET,
                  (uint32_t)(output_mailbox_head_phys_addr >> 32));
  // set the output_mailbox_pointer low
  buffer_write_be(command_queues_virt_addr, CMD_Q_E_OUTPUT_MAILBOX_PTR_LOW_OFFSET,
                  (uint32_t)(output_mailbox_head_phys_addr & 0x00000000FFFFFFFF));
  // output_length - see Table 1162
  buffer_write_be(command_queues_virt_addr, CMD_Q_E_OUTPUT_LENGTH_OFFSET, 16);
  // SW should set to 1 when posting the command. HW will change to zero to move ownership bit to SW. - Table 247
  buffer_write_be(command_queues_virt_addr, CMD_Q_E_STATUS_OFFSET, 0x01);
  // Set the corresponding bit (0 for QUERY_PAGES as this is the first command in the queue) from command_doorbell_vector to 1
  reg_write(device_addr, REG_COMMAND_DOORBELL_VECTOR_OFFSET, 1 << command_index);

  IF_AFTER_TIMEOUT(ENABLE_HCA_DELAY * 1000 * 1000,
                   (((volatile uint32_t *) command_queues_virt_addr)[15] & BIT(0))) {
    TN_DEBUG("command_queues_virt_addr.ownership did not clear, MANAGE_PAGES did not finished");
    return CMD_EXECUTION_TIMEOUT_ERR;
  }

  // Read Command delivery status
  uint8_t status = (uint8_t) ((buffer_read_be(command_queues_virt_addr, CMD_Q_E_STATUS_OFFSET) & 0x000000FF) >> 1);

  if (status != 0x0) {
    TN_DEBUG("MANAGE_PAGES command delivery status is 0x%02X, %s", status, command_delivery_status_str(status));
    return CMD_DELIVERY_STATUS_ERR;
  }

  // Read output status (output length is 12)
  uint8_t output_status = (uint8_t) ((buffer_read_be(command_queues_virt_addr, CMD_Q_E_CMD_OUTPUT_INLINE_DATA_OFFSET) & 0xFF000000) >> 24);
  if (output_status != 0x0) {
    TN_DEBUG("MANAGE_PAGES output status is 0x%02X, %s", output_status, cmd_status_str(output_status));
    return CMD_OUTPUT_STATUS_ERR;
  }

  // If DEBUG_MODE is ON, print the command entry values
  dump_command_entry_values(command_queues_virt_addr);

  // dump_output_mailbox(output_mailbox_head_virt_addr);

  // Set memory values to 0 for the first command entry in command queue
  clean_buffer(command_queues_virt_addr, CMD_Q_E_SIZE);
  clean_buffer(input_mailbox_head_virt_addr, MAILBOX_BLOCK_SIZE);
  clean_buffer(output_mailbox_head_virt_addr, MAILBOX_BLOCK_SIZE);

  return 0;
}

int cmd_exec_query_hca_cap(void* command_queues_virt_addr, uint32_t command_index, void* device_addr,
                           void* output_mailbox_head_virt_addr, uintptr_t output_mailbox_head_phys_addr,
                           uint16_t cap_type) {
  TN_VERBOSE("### Init - step 9: Execute QUERY_HCA_CAP");
  // Type of transport that carries the command: 0x7: PCIe_cmd_if_transport - Table 247
  buffer_write_be(command_queues_virt_addr, CMD_Q_E_TYPE_OFFSET, 0x07000000);
  // input_length for QUERY_HCA_CAP length is 12 bytes: Table 1166
  buffer_write_be(command_queues_virt_addr, CMD_Q_E_INPUT_LENGTH_OFFSET, 0x10);
  // OPCODE_QUERY_HCA_CAP - Table 1153
  buffer_write_16b_be(command_queues_virt_addr, CMD_Q_E_CMD_INPUT_INLINE_DATA_OFFSET, 0x0100);
  // op_mod cap_type
  buffer_write_be(command_queues_virt_addr, CMD_Q_E_CMD_INPUT_INLINE_DATA_OFFSET+0x04, cap_type);
  //((volatile uint32_t *) command_queues_virt_addr)[(CMD_Q_E_CMD_INPUT_INLINE_DATA_OFFSET+0x04)/4] = 0x00000000;
  // set the output_mailbox_pointer high
  buffer_write_be(command_queues_virt_addr, CMD_Q_E_OUTPUT_MAILBOX_PTR_HIGH_OFFSET,
                  (uint32_t)(output_mailbox_head_phys_addr >> 32));
  // set the output_mailbox_pointer low
  buffer_write_be(command_queues_virt_addr, CMD_Q_E_OUTPUT_MAILBOX_PTR_LOW_OFFSET,
                  (uint32_t)(output_mailbox_head_phys_addr & 0x00000000FFFFFFFF));

  // output_length - Table 1168
  buffer_write_be(command_queues_virt_addr, CMD_Q_E_OUTPUT_LENGTH_OFFSET, 0x100C + 0x04);
  // SW should set to 1 when posting the command. HW will change to zero to move ownership bit to SW. - Table 247
  buffer_write_be(command_queues_virt_addr, CMD_Q_E_STATUS_OFFSET, 0x01);

  // Set the corresponding bit (0 for QUERY_HCA_CAP as this is the first command in the queue) from command_doorbell_vector to 1
  reg_write(device_addr, REG_COMMAND_DOORBELL_VECTOR_OFFSET, 1 << command_index);

  IF_AFTER_TIMEOUT(ENABLE_HCA_DELAY * 1000 * 1000,
                   (((volatile uint32_t *) command_queues_virt_addr)[15] & BIT(0))) {
    TN_DEBUG("command_queues_virt_addr.ownership did not clear, QUERY_HCA_CAP did not finished");
    return CMD_EXECUTION_TIMEOUT_ERR;
  }

  // Read Command delivery status
  uint8_t status = (uint8_t) ((buffer_read_be(command_queues_virt_addr, CMD_Q_E_STATUS_OFFSET) & 0x000000FF) >> 1);
  if (status != 0x0) {
    TN_DEBUG("QUERY_HCA_CAP command delivery status is 0x%02X, %s", status, command_delivery_status_str(status));
    return CMD_DELIVERY_STATUS_ERR;
  }

  // Read output status (output length is 12)
  uint8_t output_status = (uint8_t) ((buffer_read_be(command_queues_virt_addr, CMD_Q_E_CMD_OUTPUT_INLINE_DATA_OFFSET) & 0xFF000000) >> 24);
  if (output_status != 0x0) {
    TN_DEBUG("QUERY_HCA_CAP output status is 0x%02X, %s", output_status, cmd_status_str(output_status));
    TN_DEBUG("Check health status: 0x%08x", reg_read(device_addr, 0x1010));

    // If DEBUG_MODE is ON, print the command entry values
    dump_command_entry_values(command_queues_virt_addr);


    // If DEBUG_MODE is ON, print the output mailbox
    dump_output_mailbox(output_mailbox_head_virt_addr);

    return CMD_OUTPUT_STATUS_ERR;
  }

  // If DEBUG_MODE is ON, print the output mailbox
  dump_output_mailbox(output_mailbox_head_virt_addr);

  // If DEBUG_MODE is ON, print the command entry values
  dump_command_entry_values(command_queues_virt_addr);

  // Set memory values to 0 for the first command entry in command queue
  clean_buffer(command_queues_virt_addr, CMD_Q_E_SIZE);

  return 0;
}

int cmd_exec_init_hca(void* command_queues_virt_addr, uint32_t command_index, void* device_addr,
                      void* input_mailbox_head_virt_addr, uintptr_t input_mailbox_head_phys_addr) {
  TN_VERBOSE("### Init - step 13: Execute INIT_HCA");
  // Type of transport that carries the command: 0x7: PCIe_cmd_if_transport - Table 247
  buffer_write_be(command_queues_virt_addr, CMD_Q_E_TYPE_OFFSET, 0x07000000);
  // input_length for INIT_HCA length is 12 bytes: Table 1156
  buffer_write_be(command_queues_virt_addr, CMD_Q_E_INPUT_LENGTH_OFFSET, 0x20);

  // Write 0 in sw_owner_id
  clean_buffer(input_mailbox_head_virt_addr, MAILBOX_BLOCK_SIZE);

  buffer_write_be(command_queues_virt_addr, CMD_Q_E_INPUT_MAILBOX_PTR_HIGH_OFFSET,
                  (uint32_t)(input_mailbox_head_phys_addr >> 32));
  buffer_write_be(command_queues_virt_addr, CMD_Q_E_INPUT_MAILBOX_PTR_LOW_OFFSET,
                  (uint32_t)(input_mailbox_head_phys_addr & 0x00000000FFFFFFFF));

  // OPCODE_INIT_HCA - Table 1153
  buffer_write_be(command_queues_virt_addr, CMD_Q_E_CMD_INPUT_INLINE_DATA_OFFSET, 0x01020000);
  // output_length - Table 1249
  buffer_write_be(command_queues_virt_addr, CMD_Q_E_OUTPUT_LENGTH_OFFSET, 0x08);
  // SW should set to 1 when posting the command. HW will change to zero to move ownership bit to SW. - Table 247
  buffer_write_be(command_queues_virt_addr, CMD_Q_E_STATUS_OFFSET, 0x01);

  // Set the corresponding bit (0 for INIT_HCA as this is the first command in the queue) from command_doorbell_vector to 1
  reg_write(device_addr, REG_COMMAND_DOORBELL_VECTOR_OFFSET, 1 << command_index);

  IF_AFTER_TIMEOUT(ENABLE_HCA_DELAY * 1000 * 1000,
                   (((volatile uint32_t *) command_queues_virt_addr)[15] & BIT(0))) {
    TN_DEBUG("command_queues_virt_addr.ownership did not clear, INIT_HCA did not finished");
    return CMD_EXECUTION_TIMEOUT_ERR;
  }

  // Read Command delivery status
  uint8_t status = (uint8_t) ((buffer_read_be(command_queues_virt_addr, CMD_Q_E_STATUS_OFFSET) & 0x000000FF) >> 1);
  if (status != 0x0) {
    TN_DEBUG("INIT_HCA command delivery status is 0x%02X, %s", status, command_delivery_status_str(status));
    return CMD_DELIVERY_STATUS_ERR;
  }

  // Read output status (output length is 12)
  uint8_t output_status = (uint8_t) ((buffer_read_be(command_queues_virt_addr, CMD_Q_E_CMD_OUTPUT_INLINE_DATA_OFFSET) & 0xFF000000) >> 24);
  if (output_status != 0x0) {
    TN_DEBUG("INIT_HCA output status is 0x%02X: %s", output_status, cmd_status_str(output_status));
    TN_DEBUG("Check health status: %d", reg_read(device_addr, 0x1010));
    return CMD_OUTPUT_STATUS_ERR;
  }

  // If DEBUG_MODE is ON, print the command entry values
  dump_command_entry_values(command_queues_virt_addr);

  // Set memory values to 0 for the first command entry in command queue
  clean_buffer(command_queues_virt_addr, CMD_Q_E_SIZE);
  clean_buffer(input_mailbox_head_virt_addr, MAILBOX_BLOCK_SIZE);

  return 0;
}

// -------------------------------------
// Section 7.2 HCA Driver Start-up
// -------------------------------------
bool tn_net_device_init(const struct tn_pci_address pci_address, struct tn_net_device** out_device) {
  // The NIC supports 64-bit addresses, so pointers can't be larger
  static_assert(UINTPTR_MAX <= UINT64_MAX, "uintptr_t must fit in an uint64_t");

  // First make sure the PCI device is really an Mellanox ConnectX-5 Network Connection
  uint32_t pci_id = pcireg_read(pci_address, PCIREG_ID);

  if (pci_id != ((PCI_ID_HIGH << 16) | PCI_ID_LOW)) {
    TN_DEBUG("PCI device is not what was expected pci_id %x", pci_id);
    return false;
  }

  // Section 7.1:
  // The driver should ensure that the Bus Master bit in the Command Register is set in the PCI
  // configuration header
  pcireg_set_field(pci_address, PCIREG_COMMAND, PCIREG_COMMAND_BUS_MASTER_ENABLE);
  // Same for memory reads, i.e. actually using the BARs.
  pcireg_set_field(pci_address, PCIREG_COMMAND, PCIREG_COMMAND_MEMORY_ACCESS_ENABLE);
  // Finally, since we don't want interrupts and certainly not legacy ones, make sure they're disabled
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

//  uint16_t fw_rev_minor = reg_read_field(device.addr, REG_FW_REV, REG_FW_REV_MINOR);
//  uint16_t fw_rev_major = reg_read_field(device.addr, REG_FW_REV, REG_FW_REV_MAJOR);
//  uint16_t cmd_int_rev = reg_read_field(device.addr, REG_FW_REV2, REG_FW_REV2_CMD_INTERFACE_REVISION);
//  uint16_t fw_rev_subminor = reg_read_field(device.addr, REG_FW_REV2, REG_FW_REV2_SUBMINOR);

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
   * Step 2. Write the physical location of the command queues to the initialization segment.
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

  // Write zeros in the command_queues
  for (int i = 0; i < CMDQ_SIZE; ++i) {
    ((volatile uint32_t *) command_queues_virt_addr)[i] = 0;
  }

  if (!tn_mem_virt_to_phys(command_queues_virt_addr, &command_queues_phys_addr)) {
    TN_DEBUG("Could not get a command_queues's physical address");
    return false;
  }

  // Since CMDQ_PHY_ADDR_LOW is not 32 bits but 20, the lower 12 bits
  // of the command_queues_phys_addr should be 0
  if ((command_queues_phys_addr & BITS(0, 12)) != 0) {
    TN_DEBUG("Invalid command queue address. The physical address has not the lower 12 bits set to 0!");
    return false;
  }

  // Equivalent to `iowrite32be(cmd_h, &dev->iseg->cmdq_addr_h);`
  reg_write(device.addr, 0x10, (uint32_t)(command_queues_phys_addr>>32));
  // shift the command_queues_phys_addr to write only the top 20 bits of the bottom 32 bits

  reg_clear(device.addr, 0x14); // instead of the below lines
  reg_write(device.addr, 0x14, ((uint32_t) (command_queues_phys_addr & 0x00000000FFFFFFFF)));
  // write in the nic_interface 0

//  reg_clear_field(device.addr, 0x14, REG_NIC_INTERFACE); // Full driver mode
//  reg_clear_field(device.addr, 0x14, REG_LOG_CMDQ_SIZE);
//  reg_clear_field(device.addr, 0x14, REG_LOG_CMDQ_STRIDE);

  TN_DEBUG("Check if the values were written correctly on initialization segment");
  reg_read(device.addr, 0x10);
  reg_read(device.addr, 0x14);
  TN_DEBUG("Check health status");
  reg_read(device.addr, 0x1010);

  /**
   * Step 3. Read the initializing field from the initialization segment.
   * Repeat until it is cleared (INIT_SEGMENT.initializing become 0).
   * */
  TN_VERBOSE("### Init - step 3");

  IF_AFTER_TIMEOUT(INITIALIZING_TIMEOUT * 1000 * 1000,
         !reg_is_field_cleared(device.addr, REG_INITIALIZING_OFFSET, REG_INITIALIZING)) {
    TN_DEBUG("INIT_SEGMENT.initializing did not clear, cannot complete init setup");
    return false;
  }

  uint32_t command_index = 0;
  uint32_t cmdq_addr_l_sz = reg_read(device.addr, 0x14) & 0xff;
  uint32_t log_cmdq_size = cmdq_addr_l_sz >> 4 & 0xf;
  uint32_t log_stride = cmdq_addr_l_sz & 0xf;

  TN_INFO("log_cmdq_size = %d, log_stride = %d", log_cmdq_size, log_stride);

  /**
   * Step 3.5 Prepare to execute commands: mailbox space
   * */
  TN_VERBOSE("### Init - step 3.5: Prepare to execute commands: input_mailbox_pointer, output_mailbox_pointer");

  void* input_mailbox_head_virt_addr;
  uintptr_t input_mailbox_head_phys_addr;
  void* output_mailbox_head_virt_addr;
  uintptr_t output_mailbox_head_phys_addr;
  int num_pages;

  if (!tn_mem_allocate(MAILBOX_BLOCK_SIZE, &input_mailbox_head_virt_addr)) {
    TN_DEBUG("Could not allocate memory for input mailbox block");
    return false;
  }

  if (!tn_mem_allocate(MAILBOX_BLOCK_SIZE, &output_mailbox_head_virt_addr)) {
    TN_DEBUG("Could not allocate memory for output mailbox block");
    return false;
  }

  if (!tn_mem_virt_to_phys(input_mailbox_head_virt_addr, &input_mailbox_head_phys_addr)) {
    TN_DEBUG("Could not get the input mailbox_head_phys_addr's physical address");
    return false;
  }

  if (!tn_mem_virt_to_phys(output_mailbox_head_virt_addr, &output_mailbox_head_phys_addr)) {
    TN_DEBUG("Could not get the output mailbox_head_phys_addr's physical address");
    return false;
  }

  /**
   * Step 4. Execute ENABLE_HCA command.
   * */
  if (cmd_exec_enable_hca(command_queues_virt_addr, command_index, device.addr) != 0) {
    TN_DEBUG("ENABLE_HCA failed.");
    return false;
  }

  /**
  * Step 5. Execute QUERY_ISSI command.
  * */
  uint32_t current_issi = 0;
  uint32_t minimum_issi = 0;
  if (cmd_exec_query_issi(command_queues_virt_addr, command_index, device.addr,
                          output_mailbox_head_virt_addr, output_mailbox_head_phys_addr,
                          &current_issi, &minimum_issi) != 0) {
    TN_DEBUG("QUERY_ISSI failed.");
    return false;
  }

  /**
  * Step 6. Execute SET_ISSI command.
  * */
  if (cmd_exec_set_issi(command_queues_virt_addr, command_index, device.addr, minimum_issi) != 0) {
    TN_DEBUG("SET_ISSI failed.");
    return false;
  }

  /**
  * Step 7. Execute QUERY_PAGES to understand the HCA need for boot pages.
  * */
  if (cmd_exec_query_pages(command_queues_virt_addr, command_index, device.addr, &num_pages, BOOT_PAGES) != 0) {
    TN_DEBUG("QUERY_PAGES failed.");
    return false;
  }

  /**
  * Step 8.  Execute MANAGE_PAGES to provide the HCA with all required boot pages,
  *          The driver is allowed to give the sum of boot pages and num_init_pages.
  * */
  if (cmd_exec_manage_pages(command_queues_virt_addr, command_index, device.addr,
                            input_mailbox_head_virt_addr, input_mailbox_head_phys_addr,
                            output_mailbox_head_virt_addr, output_mailbox_head_phys_addr, num_pages) != 0) {
    TN_DEBUG("MANAGE_PAGES failed.");
    return false;
  }

  TN_DEBUG("Check health status: 0x%08x", reg_read(device.addr, 0x1010));

  /**
  * Step 9. Execute QUERY_HCA_CAP to retrieve the device capabilities limits..
  * */
  // TODO
  if(cmd_exec_query_hca_cap(command_queues_virt_addr, command_index, device.addr,
                            output_mailbox_head_virt_addr, output_mailbox_head_phys_addr,
                            GEN_DEV_CAP) != 0) {
    TN_DEBUG("QUERY_HCA_CAP failed.");
    return false;
  }

  /**
  * Step 10. Execute SET_HCA_CAP to modify system capabilities.
  * */
  TN_VERBOSE("### Init - step 10: Execute SET_HCA_CAP - skip for now");

  /**
  * Step 11.
  *  Execute QUERY_PAGES to understand the HCA need for initial pages for executing
  *  commands. If init_pages is 0, no need to do the MANAGE_PAGES stage.
  * */
  if (cmd_exec_query_pages(command_queues_virt_addr, command_index, device.addr, &num_pages, INIT_PAGES) != 0) {
    TN_DEBUG("QUERY_PAGES failed.");
    return false;
  }

  if (num_pages != 0) {
      /**
      * Step 12. Execute e MANAGE_PAGES to provide the HCA with all require init-pages.
      * This can be done by multiple MANAGE_PAGES commands.
      * */
      TN_VERBOSE("### Init - step 12: Execute MANAGE_PAGES");
  }

  /**
  * Step 13. Execute INIT_HCA command to initialize the HCA
  * */
  if(cmd_exec_init_hca(command_queues_virt_addr, command_index, device.addr,
                            input_mailbox_head_virt_addr, input_mailbox_head_phys_addr) != 0) {
    TN_DEBUG("INIT_HCA failed.");
    return false;
  }

  /**
  * Step 14. Execute SET_DRIVER_VERSION command command (only in case HCA_CAP.driver_version==1).
  * See Section 23.3.18, “SET_DRIVER_VERSION,” on page 1319.
  * */

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
