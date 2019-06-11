#include "ixgbe_82599.h"

#include "os/arch.h"
#include "os/memory.h"
#include "os/pci.h"
#include "os/time.h"
#include "log.h"

// Fundamental constants

// Section 8.2.3.8.3 Receive Descriptor Length: "Validated lengths up to 128 K (8 K descriptors)."
const uint16_t IXGBE_RECEIVE_RING_SIZE_MAX = 8 * 1024;

// Section 8.2.3.8.7 Split Receive Control Registers: "Receive Buffer Size for Packet Buffer. Value can be from 1 KB to 16 KB"
const uint16_t IXGBE_RECEIVE_PACKET_SIZE_MAX = 16 * 1024;

// TODO find reference for this
#define IXGBE_RECEIVE_QUEUES_COUNT 128u
// Section 8.2.3.10.13 DCB Transmit Descriptor Plane Queue Select:
// "Field TXDQ_IDX, Bits 6:0" -> 128 pools
// TODO find a better ref...
#define IXGBE_TX_QUEUE_POOLS_COUNT 128u
// Section 7.3.1 Interrupts Registers:
//	"These registers are extended to 64 bits by an additional set of two registers.
//	 EICR has an additional two registers EICR(1)... EICR(2) and so on for the EICS, EIMS, EIMC, EIAM and EITR registers."
// TODO move this to the registers section
#define IXGBE_INTERRUPT_REGISTERS_COUNT 3u


// ---------
// Utilities
// ---------

// Overload macros for up to 5 args, see https://stackoverflow.com/a/11763277/3311770
#define GET_MACRO(_1, _2, _3, _4, _5, NAME, ...) NAME

// Bit tricks; note that we count bits starting from 0!
#define BIT(n) (1u << n)
#define BITS(start, end) ((end == 31 ? 0u : (0xFFFFFFFFu << (end + 1))) ^ (0xFFFFFFFFu << start))
#define TRAILING_ZEROES(n) __builtin_ctzll(n)

// Poll until the given condition holds, or the given timeout occurs; store whether a timeout occurred in result_name
#define WAIT_WITH_TIMEOUT(result_name, timeout_in_us, condition) \
		result_name = true; \
		tn_sleep_us(timeout_in_us % 10); \
		for (uint8_t i = 0; i < 10; i++) { \
			if (condition) { \
				result_name = false; \
				break; \
			} \
			tn_sleep_us(timeout_in_us / 10); \
		}


// ---------------------
// Operations on the NIC
// ---------------------

// To facilitate writing code that operates on queue-independent registers
const int _ = 0;

// Register primitives
static uint32_t ixgbe_reg_read(const uintptr_t addr, const uint32_t reg)
{
	uint32_t val_le = *((volatile uint32_t*)((char*)addr + reg));
	tn_read_barrier();
	uint32_t result = tn_le_to_cpu(val_le);
	TN_DEBUG("IXGBE read (addr 0x%016" PRIxPTR "): 0x%08" PRIx32 " -> 0x%08" PRIx32, addr, reg, result);
	return result;
}
static void ixgbe_reg_force_read(const uintptr_t addr, const uint32_t reg)
{
	// See https://stackoverflow.com/a/13824124/3311770
	uint32_t* ptr = (uint32_t*)((char*)addr + reg);
	__asm__ volatile ("" : "=m" (*ptr) : "r" (*ptr));
}
static void ixgbe_reg_write(const uintptr_t addr, const uint32_t reg, const uint32_t value)
{
	tn_write_barrier();
	*((volatile uint32_t*)((char*)addr + reg)) = tn_cpu_to_le(value);
	TN_DEBUG("IXGBE write (addr 0x%016" PRIxPTR "): 0x%08" PRIx32 " := 0x%08" PRIx32, addr, reg, value);
}

#define IXGBE_REG_READ3(addr, reg, idx) ixgbe_reg_read(addr, IXGBE_REG_##reg(idx))
#define IXGBE_REG_READ4(addr, reg, idx, field) ((IXGBE_REG_READ3(addr, reg, idx) & IXGBE_REG_##reg##_##field) >> TRAILING_ZEROES(IXGBE_REG_##reg##_##field))
#define IXGBE_REG_READ(...) GET_MACRO(__VA_ARGS__, _UNUSED, IXGBE_REG_READ4, IXGBE_REG_READ3, _UNUSED)(__VA_ARGS__)
#define IXGBE_REG_FORCE_READ(addr, reg, idx) ixgbe_reg_force_read(addr, IXGBE_REG_##reg(idx))
#define IXGBE_REG_WRITE4(addr, reg, idx, value) ixgbe_reg_write(addr, IXGBE_REG_##reg(idx), value)
#define IXGBE_REG_WRITE5(addr, reg, idx, field, value) ixgbe_reg_write(addr, IXGBE_REG_##reg(idx), ((IXGBE_REG_READ(addr, reg, idx) & ~IXGBE_REG_##reg##_##field) | (((value) << TRAILING_ZEROES(IXGBE_REG_##reg##_##field)) & IXGBE_REG_##reg##_##field)))
#define IXGBE_REG_WRITE(...) GET_MACRO(__VA_ARGS__, IXGBE_REG_WRITE5, IXGBE_REG_WRITE4, _UNUSED)(__VA_ARGS__)
#define IXGBE_REG_CLEARED(addr, reg, idx, field) (IXGBE_REG_READ(addr, reg, idx, field) == 0u)
#define IXGBE_REG_CLEAR3(addr, reg, idx) IXGBE_REG_WRITE(addr, reg, idx, 0U)
#define IXGBE_REG_CLEAR4(addr, reg, idx, field) IXGBE_REG_WRITE(addr, reg, idx, (IXGBE_REG_READ(addr, reg, idx) & ~IXGBE_REG_##reg##_##field))
#define IXGBE_REG_CLEAR(...) GET_MACRO(__VA_ARGS__, _UNUSED, IXGBE_REG_CLEAR4, IXGBE_REG_CLEAR3, _UNUSED)(__VA_ARGS__)
// TODO better name than "set", since set implies to a specific value? what's the opposite of clear?
#define IXGBE_REG_SET(addr, reg, idx, field) IXGBE_REG_WRITE(addr, reg, idx, (IXGBE_REG_READ(addr, reg, idx) | IXGBE_REG_##reg##_##field))

// PCI primitives (we do not write to PCI)
#define IXGBE_PCIREG_READ(addr, reg) tn_pci_read(addr, IXGBE_PCIREG_##reg)
#define IXGBE_PCIREG_CLEARED(addr, reg, field) ((IXGBE_PCIREG_READ(addr, reg) & IXGBE_PCIREG_##reg##_##field) == 0u)


// -------------------------------------------------------------
// PCI registers, in alphabetical order, along with their fields
// -------------------------------------------------------------

#define IXGBE_PCIREG_DEVICESTATUS 0xAAu
#define IXGBE_PCIREG_DEVICESTATUS_TRANSACTIONPENDING BIT(5)


// ---------------------------------------------------------
// Registers, in alphabetical order, along with their fields
// ---------------------------------------------------------

// TODO eliminate all "count" variables, and express them in terms of primitive counts instead (#pools, #MACs, ...)

// Section 8.2.3.22.19 Auto Negotiation Control Register
#define IXGBE_REG_AUTOC(_) 0x042A0
#define IXGBE_REG_AUTOC_LMS BITS(13,15)

#define IXGBE_REG_CTRL(_) 0x00000u
#define IXGBE_REG_CTRL_MASTERDISABLE BIT(2)
#define IXGBE_REG_CTRL_LRST BIT(3)

// Section 8.2.3.1.3 Extended Device Control Register
#define IXGBE_REG_CTRLEXT(_) 0x00018u
#define IXGBE_REG_CTRLEXT_NSDIS BIT(16)

// Section 8.2.3.11.1 Rx DCA Control Register
#define IXGBE_REG_DCARXCTRL(n) (n <= 63u ? (0x0100Cu + 0x40u*n) : (0x0D00Cu + 0x40u*(n-64u)))
// This bit is reserved has no name, but must be cleared by software anyway.
#define IXGBE_REG_DCARXCTRL_UNKNOWN BIT(12)

// Section 8.2.3.9.1 DMA Tx TCP Max Allow Size Requests
#define IXGBE_REG_DTXMXSZRQ(_) 0x08100u
#define IXGBE_REG_DTXMXSZRQ_MAXBYTESNUMREQ BITS(0,11)

// Section 8.2.3.2.1 EEPROM/Flash Control Register
#define IXGBE_REG_EEC(_) 0x10010u
#define IXGBE_REG_EEC_EEPRES BIT(8)
#define IXGBE_REG_EEC_AUTORD BIT(9)

#define IXGBE_REG_EIMC(n) (n == 0 ? 0x00888u : (0x00AB0u + 4u*(n-1u)))
#define IXGBE_REG_EIMC_MASK BITS(0,31)

// Section 8.2.3.3.7 Flow Control Configuration
#define IXGBE_REG_FCCFG(_) 0x03D00u
#define IXGBE_REG_FCCFG_TFCE BITS(3,4)

// Section 8.2.3.3.2 Flow Control Transmit Timer Value n
#define IXGBE_FCTTV_REGISTERS_COUNT 4u
#define IXGBE_REG_FCTTV(n) (0x03200u + 4u*n)

// Section 8.2.3.3.3 Flow Control Receive Threshold Low
#define IXGBE_FCRTL_REGISTERS_COUNT 8u
#define IXGBE_REG_FCRTL(n) (0x03220u + 4u*n)

// Section 8.2.3.3.4 Flow Control Receive Threshold High
#define IXGBE_FCRTH_REGISTERS_COUNT 8u
#define IXGBE_REG_FCRTH(n) (0x03260u + 4u*n)
#define IXGBE_REG_FCRTH_RTH BITS(5,18)

// Section 8.2.3.3.5 Flow Control Refresh Threshold Value
#define IXGBE_REG_FCRTV(_) 0x032A0u

// Section 8.2.3.7.1 Filter Control Register (FCTRL)
#define IXGBE_REG_FCTRL(_) 0x05080u
#define IXGBE_REG_FCTRL_MPE BIT(8)
#define IXGBE_REG_FCTRL_UPE BIT(9)
#define IXGBE_REG_FCTRL_BAM BIT(10)

// Section 8.2.3.7.19 Five tuple Queue Filter
#define IXGBE_FTQF_REGISTERS_COUNT 128u
#define IXGBE_REG_FTQF(n) (0x0E600u + 4u*n)
#define IXGBE_REG_FTQF_MASK BITS(25,29)
#define IXGBE_REG_FTQF_QUEUEENABLE BIT(31)

#define IXGBE_REG_FWSM(_) 0x10148u
#define IXGBE_REG_FWSM_EXTERRIND BITS(19,24)

#define IXGBE_REG_GCREXT(_) 0x11050u
#define IXGBE_REG_GCREXT_BUFFERSCLEAR BIT(30)

#define IXGBE_REG_HLREG0(_) 0x04240u
#define IXGBE_REG_HLREG0_LPBK BIT(15)

// Section 8.2.3.22.34 MAC Flow Control Register
#define IXGBE_REG_MFLCN(_) 0x04294u
#define IXGBE_REG_MFLCN_RFCE BIT(3)

// Section 8.2.3.7.10 MAC Pool Select Array
#define IXGBE_MPSAR_REGISTERS_COUNT 256u
#define IXGBE_REG_MPSAR(n) (0x0A600u + 4u*n)

// Section 8.2.3.7.7 Multicast Table Array
#define IXGBE_MTA_REGISTERS_COUNT 128
#define IXGBE_REG_MTA(n) (0x05200u + 4u*n)

// Section 8.2.3.27.17 PF Unicast Table Array
#define IXGBE_PFUTA_REGISTERS_COUNT 128u
#define IXGBE_REG_PFUTA(n) (0x0F400u + 4u*n)

// Section 8.2.3.27.15 PF VM VLAN Pool Filter
#define IXGBE_PFVLVF_REGISTERS_COUNT 64u
#define IXGBE_REG_PFVLVF(n) (0x0F100u + 4u*n)

// Section 8.2.3.27.16 PF VM VLAN Pool Filter Bitmap
#define IXGBE_PFVLVFB_REGISTERS_COUNT 128u
#define IXGBE_REG_PFVLVFB(n) (0x0F200u + 4u*n)

// Section 8.2.3.8.2 Receive Descriptor Base Address High
#define IXGBE_REG_RDBAH(n) (n <= 63u ? (0x01004u + 0x40u*n) : (0x0D004u + 0x40u*(n-64u)))

// Section 8.2.3.8.1 Receive Descriptor Base Address Low
#define IXGBE_REG_RDBAL(n) (n <= 63u ? (0x01000u + 0x40u*n) : (0x0D000u + 0x40u*(n-64u)))

// Section 8.2.3.8.3 Receive Descriptor Length
#define IXGBE_REG_RDLEN(n) (n <= 63u ? (0x01008u + 0x40u*n) : (0x0D008 + 0x40u*(n-64u)))

// Section 8.2.3.8.8 Receive DMA Control Register
#define IXGBE_REG_RDRXCTL(_) 0x02F00u
#define IXGBE_REG_RDRXCTL_DMAIDONE BIT(3)

// Section 8.2.3.8.5 Receive Descriptor Tail
#define IXGBE_REG_RDT(n) (n <= 63u ? (0x01018u + 0x40u*n) : (0x0D018u + 0x40u*(n-64u)))

// Section 8.2.3.10.6 DCB Receive Packet Plane T4 Config
#define IXGBE_RTRPT4C_REGISTERS_COUNT 8u
#define IXGBE_REG_RTRPT4C(n) (0x02140u + 4u*n)

// Section 8.2.3.10.13 DCB Transmit Descriptor Plane Queue Select
#define IXGBE_REG_RTTDQSEL(_) 0x04904u
#define IXGBE_REG_RTTDQSEL_TXDQIDX BITS(0,6)

// Section 8.2.3.10.14 DCB Transmit Descriptor Plane T1 Config
#define IXGBE_REG_RTTDT1C(_) 0x04908u

// Section 8.2.3.10.9 DCB Transmit Descriptor Plane T2 Config
#define IXGBE_RTTDT2C_REGISTERS_COUNT 8u
#define IXGBE_REG_RTTDT2C(n) (0x04910u + 4u*n)

// Section 8.2.3.10.10 DCB Transmit Packet Plane T2 Config
#define IXGBE_RTTPT2C_REGISTERS_COUNT 8U
#define IXGBE_REG_RTTPT2C(n) (0x0CD20u + 4u*n)

#define IXGBE_REG_RXCTRL(_) 0x03000u
#define IXGBE_REG_RXCTRL_RXEN BIT(0)

// Section 8.2.3.8.6 Receive Descriptor Control
#define IXGBE_REG_RXDCTL(n) (n <= 63u ? (0x01028u + 0x40u*n) : (0x0D028u + 0x40u*(n-64u)))
#define IXGBE_REG_RXDCTL_ENABLE BIT(25)

// Section 8.2.3.8.9 Receive Packe Buffer Size
#define IXGBE_RXPBSIZE_REGISTERS_COUNT 8u
#define IXGBE_REG_RXPBSIZE(n) (0x03C00u + 4u*n)

// Section 8.2.3.12.5 Security Rx Control
#define IXGBE_REG_SECRXCTRL(_) 0x08D00u
#define IXGBE_REG_SECRXCTRL_RXDIS BIT(1)

// Section 8.2.3.12.6 Security Rx Status
#define IXGBE_REG_SECRXSTAT(_) 0x08D04u
#define IXGBE_REG_SECRXSTAT_SECRXRDY BIT(0)

// Section 8.2.3.8.7 Split Receive Control Registers
#define IXGBE_REG_SRRCTL(n) (n <= 63u ? (0x01014u + 0x40u*n) : (0x0D014u + 0x40u*(n-64u)))
#define IXGBE_REG_SRRCTL_BSIZEPACKET BITS(0,4)
#define IXGBE_REG_SRRCTL_DESCTYPE BITS(25,27)
#define IXGBE_REG_SRRCTL_DROPEN BIT(28)

#define IXGBE_REG_STATUS(_) 0x00008u
#define IXGBE_REG_STATUS_MASTERENABLE BIT(19)

#define IXGBE_REG_SWFWSYNC(_) 0x10160u
#define IXGBE_REG_SWFWSYNC_SW BITS(0,4)
#define IXGBE_REG_SWFWSYNC_FW BITS(5,9)

#define IXGBE_REG_SWSM(_) 0x10140u
#define IXGBE_REG_SWSM_SMBI    BIT(0)
#define IXGBE_REG_SWSM_SWESMBI BIT(1)

#define IXGBE_TXPBSIZE_REGISTERS_COUNT 8u
#define IXGBE_REG_TXPBSIZE(n) (0x0CC00u + 4u*n)

// Section 8.2.3.9.16 Tx Packet Buffer Threshold
#define IXGBE_REG_TXPBTHRESH(n) (0x04950u + 4u*n)
#define IXGBE_REG_TXPBTHRESH_THRESH BITS(0,9)

// ----------------------------------------------------
// Section 10.5.4 Software and Firmware Synchronization
// ----------------------------------------------------

// NOTE: For simplicity, we always gain/release control of all resources
// TODO: Do we really need this part?

// "Gaining Control of Shared Resource by Software"
static void ixgbe_lock_swsm(const uintptr_t addr, bool* out_sw_malfunction, bool* out_fw_malfunction)
{
	// "Software checks that the software on the other LAN function does not use the software/firmware semaphore"

	// "- Software polls the SWSM.SMBI bit until it is read as 0b or time expires (recommended expiration is ~10 ms+ expiration time used for the SWSM.SWESMBI)."
	// "- If SWSM.SMBI is found at 0b, the semaphore is taken. Note that following this read cycle hardware auto sets the bit to 1b."
	// "- If time expired, it is assumed that the software of the other function malfunctions. Software proceeds to the next steps checking SWESMBI for firmware use."
	WAIT_WITH_TIMEOUT(*out_sw_malfunction, 10 * 1000 + 3000 * 1000, IXGBE_REG_CLEARED(addr, SWSM, _, SMBI));


	// "Software checks that the firmware does not use the software/firmware semaphore and then takes its control"

	// "- Software writes a 1b to the SWSM.SWESMBI bit"
	IXGBE_REG_SET(addr, SWSM, _, SWESMBI);

	// "- Software polls the SWSM.SWESMBI bit until it is read as 1b or time expires (recommended expiration is ~3 sec).
	//    If time has expired software assumes that the firmware malfunctioned and proceeds to the next step while ignoring the firmware bits in the SW_FW_SYNC register."
	WAIT_WITH_TIMEOUT(*out_fw_malfunction, 3000 * 1000, IXGBE_REG_CLEARED(addr, SWSM, _, SWESMBI));
}

static void ixgbe_unlock_swsm(const uintptr_t addr)
{
	IXGBE_REG_CLEAR(addr, SWSM, _, SWESMBI);
	IXGBE_REG_CLEAR(addr, SWSM, _, SMBI);
}

static bool ixgbe_lock_resources(const uintptr_t addr)
{
	uint32_t attempts = 0;

start:;
	bool sw_malfunction;
	bool fw_malfunction;
	ixgbe_lock_swsm(addr, &sw_malfunction, &fw_malfunction);

	// "Software takes control of the requested resource(s)"

	// "- Software reads the firmware and software bit(s) of the requested resource(s) in the SW_FW_SYNC register."
	uint32_t sync = IXGBE_REG_READ(addr, SWFWSYNC, _);
	// "- If time has expired in the previous steps due to a malfunction firmware,
	//    the software should clear the firmware bits in the SW_FW_SYNC register.
	//    If time has expired in the previous steps due to malfunction software of the other LAN function,
	//    software should clear the software bits in the SW_FW_SYNC register that it does not own."
	if (fw_malfunction) {
		sync &= ~IXGBE_REG_SWFWSYNC_FW;
	}
	if (sw_malfunction) {
		sync &= ~IXGBE_REG_SWFWSYNC_SW;
	}

	// "- If the software and firmware bit(s) of the requested resource(s) in the SW_FW_SYNC register are cleared, it means that these resources are accessible.
	//    In this case software sets the software bit(s) of the requested resource(s) in the SW_FW_SYNC register.
	//    Then the SW clears the SWSM.SWESMBI and SWSM.SMBI bits (releasing the SW/FW semaphore register) and can use the specific resource(s)."
	if ((sync & IXGBE_REG_SWFWSYNC_SW) == 0 && (sync & IXGBE_REG_SWFWSYNC_FW) == 0) {
		sync |= IXGBE_REG_SWFWSYNC_SW;
		IXGBE_REG_WRITE(addr, SWFWSYNC, _, sync);

		ixgbe_unlock_swsm(addr);

		return true;
	} else {
		// "- Otherwise (either firmware or software of the other LAN function owns the resource),
		//    software clears the SWSM.SWESMBI and SWSM.SMBI bits and then repeats the entire process after some delay (recommended 5-10 ms).
		//    If the resources are not released by software of the other LAN function long enough (recommended expiration time is ~1 sec) software can assume that the other software malfunctioned.
		//    In that case software should clear all software flags that it does not own and then repeat the entire process once again."
		ixgbe_unlock_swsm(addr);

		attempts++;

		if (attempts == 200U) {
			TN_INFO("Max attempts for SWSM reached");
			return false;
		}

		if (attempts == 100U) {
			IXGBE_REG_CLEAR(addr, SWFWSYNC, _, SW);
			tn_sleep_us(10 * 1000);
			goto start;
		}

		tn_sleep_us(10 * 1000);
		goto start;
	}
}

// "Releasing a Shared Resource by Software"
static void ixgbe_unlock_resources(const uintptr_t addr)
{
	// "The software takes control over the software/firmware semaphore as previously described for gaining shared resources."
	bool ignored;
	ixgbe_lock_swsm(addr, &ignored, &ignored);

	// "Software clears the bit(s) of the released resource(s) in the SW_FW_SYNC register."
	IXGBE_REG_CLEAR(addr, SWFWSYNC, _, SW);

	// "Software releases the software/firmware semaphore by clearing the SWSM.SWESMBI and SWSM.SMBI bits"
	ixgbe_unlock_swsm(addr);

	// "Software should wait a minimum delay (recommended 5-10 ms) before trying to gain the semaphore again"
	tn_sleep_us(10 * 1000);
}

// ---------------------------------------------------------
// Section 4.6.7.1.2 [Dynamic] Disabling [of Receive Queues]
// ---------------------------------------------------------

static bool ixgbe_recv_disable(const uintptr_t addr, const uint8_t queue)
{
	// "Disable the queue by clearing the RXDCTL.ENABLE bit."
	IXGBE_REG_CLEAR(addr, RXDCTL, queue, ENABLE);

	// "The 82599 clears the RXDCTL.ENABLE bit only after all pending memory accesses to the descriptor ring are done.
	//  The driver should poll this bit before releasing the memory allocated to this queue."
	// INTERPRETATION: There is no mention of what to do if the 82599 never clears the bit; 1s seems like a decent timeout
	bool timed_out;
	WAIT_WITH_TIMEOUT(timed_out, 1000 * 1000, IXGBE_REG_CLEARED(addr, RXDCTL, queue, ENABLE));
	if (timed_out) {
		TN_INFO("RXDCTL.ENABLE did not clear, cannot disable receive");
		return false;
	}

	// "Once the RXDCTL.ENABLE bit is cleared the driver should wait additional amount of time (~100 us) before releasing the memory allocated to this queue."
	tn_sleep_us(100);

	return true;
}


// --------------------------------
// Section 5.2.5.3.2 Master Disable
// --------------------------------

// See quotes inside to understand the meaning of the return value
static bool ixgbe_device_master_disable(const uintptr_t addr)
{
	// "The device driver disables any reception to the Rx queues as described in Section 4.6.7.1"
	for (uint8_t queue = 0; queue <= IXGBE_RECEIVE_QUEUES_COUNT; queue++) {
		ixgbe_recv_disable(addr, queue);
	}

	// "Then the device driver sets the PCIe Master Disable bit [in the Device Status register] when notified of a pending master disable (or D3 entry)."
	IXGBE_REG_SET(addr, CTRL, _, MASTERDISABLE);

	// "The 82599 then blocks new requests and proceeds to issue any pending requests by this function.
	//  The driver then reads the change made to the PCIe Master Disable bit and then polls the PCIe Master Enable Status bit.
	//  Once the bit is cleared, it is guaranteed that no requests are pending from this function."
	// INTERPRETATION: The next sentence refers to "a given time"; let's say 1 second should be plenty...
	bool timed_out;
	WAIT_WITH_TIMEOUT(timed_out, 1000 * 1000, IXGBE_REG_CLEARED(addr, STATUS, _, MASTERENABLE));

	// "The driver might time out if the PCIe Master Enable Status bit is not cleared within a given time."
	if (timed_out) {
		// "In these cases, the driver should check that the Transaction Pending bit (bit 5) in the Device Status register in the PCI config space is clear before proceeding.
		//  In such cases the driver might need to initiate two consecutive software resets with a larger delay than 1 us between the two of them."
		if (!IXGBE_PCIREG_CLEARED(addr, DEVICESTATUS, TRANSACTIONPENDING)) {
			// Because this is recoverable, we log it as DEBUG rather than INFO
			TN_DEBUG("DEVICESTATUS.TRANSACTIONPENDING did not clear, cannot perform master disable");
			return false;
		}

		// "In the above situation, the data path must be flushed before the software resets the 82599.
		//  The recommended method to flush the transmit data path is as follows:"
		// "- Inhibit data transmission by setting the HLREG0.LPBK bit and clearing the RXCTRL.RXEN bit.
		//    This configuration avoids transmission even if flow control or link down events are resumed."
		IXGBE_REG_SET(addr, HLREG0, _, LPBK);
		IXGBE_REG_CLEAR(addr, RXCTRL, _, RXEN);

		// "- Set the GCR_EXT.Buffers_Clear_Func bit for 20 microseconds to flush internal buffers."
		IXGBE_REG_SET(addr, GCREXT, _, BUFFERSCLEAR);
		tn_sleep_us(20);

		// "- Clear the HLREG0.LPBK bit and the GCR_EXT.Buffers_Clear_Func"
		IXGBE_REG_CLEAR(addr, HLREG0, _, LPBK);
		IXGBE_REG_CLEAR(addr, GCREXT, _, BUFFERSCLEAR);

		// "- It is now safe to issue a software reset."
	}

	return true;
}


// --------------------------
// Section 4.2.1.7 Link Reset
// --------------------------

// INTERPRETATION: The spec has a circular dependency here - resets need master disable, but master disable asks for two resets if it fails!
//                 We assume that if the master disable fails, the resets do not need to go through the master disable step.

static void ixgbe_device_reset(const uintptr_t addr)
{
	// "Prior to issuing link reset, the driver needs to execute the master disable algorithm as defined in Section 5.2.5.3.2."
	bool master_disabled = ixgbe_device_master_disable(addr);

	// "Initiated by writing the Link Reset bit of the Device Control register (CTRL.LRST)."
	IXGBE_REG_SET(addr, CTRL, _, LRST);

	// See quotes in ixgbe_device_master_disable
	if (master_disabled) {
		tn_sleep_us(2);
		IXGBE_REG_SET(addr, CTRL, _, LRST);
	}

	// Section 8.2.3.1.1 Device Control Register
	// "To ensure that a global device reset has fully completed and that the 82599 responds to subsequent accesses,
	//  programmers must wait approximately 1 ms after setting before attempting to check if the bit has cleared or to access (read or write) any other device register."
	// INTERPRETATION: It's OK to access the CTRL register itself to double-reset it as above without waiting a full second,
	//                 and thus this does not contradict the "at least 1 us" rule of the double-reset.
	tn_sleep_us(1000);
}


// ---
// ???
// ---
// (from the dpdk ixgbe driver...)

#include <stdio.h>
#include <inttypes.h>
#define IXGBE_REG_EERD(_) 0x10014
#define IXGBE_REG_EERD_START BIT(0)
#define IXGBE_REG_EERD_DONE BIT(1)
//#define IXGBE_REG_EERD_ADDR BITS(2,15)
//#define IXGBE_REG_EERD_DATA BITS(16,31)
// TODO: Make sure the EEPROm is valid, this method assumes it is
// TODO this is where the 'addr' for the uintptr_t is dubious... "hw" maybe? something else?
// TODO this method would be simpler if we could assume 0xFFFF is only ever returned on error...
static bool ixgbe_eeprom_read(const uintptr_t addr, const uint16_t eeprom_addr, uint16_t* out_value)
{
	// Section 8.2.3.2.2 EEPROM Read Register:
	// "This register is used by software to cause the 82599 to read individual words in the EEPROM.
	//  To read a word, software writes the address to the Read Address field and simultaneously writes a 1b to the Start Read field.
	//  The 82599 reads the word from the EEPROM and places it in the Read Data field, setting the Read Done field to 1b.
	//  Software can poll this register, looking for a 1b in the Read Done field and then using the value in the Read Data field."
	if (eeprom_addr >= 0x3FFFu) {
printf("NO SUCH WORD\n");
		return false; // No such word!
	}

	// NOTE: Since this has to be simultaneous, we bypass the usual API
	// TODO check if we can use it anyway (perf doesn't matter, this isn't in the inner loop)
	uint32_t eerd = ((uint32_t) eeprom_addr << 2) | IXGBE_REG_EERD_START;
	IXGBE_REG_WRITE(addr, EERD, _, eerd);
	bool eeprom_timed_out;
	WAIT_WITH_TIMEOUT(eeprom_timed_out, 1000 * 1000, (eerd = IXGBE_REG_READ(addr, EERD, _)) & IXGBE_REG_EERD_DONE);
	if (eeprom_timed_out) {
printf("EEPROM TIMED OUT\n");
		return false;
	}

	*out_value = (uint16_t) (eerd >> 16);
	return true;
}

static bool ixgbe_device_init_sfp(const uintptr_t addr)
{
	uint16_t sfp_list_offset;
	if (!ixgbe_eeprom_read(addr, 0x002Bu, &sfp_list_offset)) {
printf("NO 2B\n");
		return false;
	}
	if (sfp_list_offset == 0u || sfp_list_offset == 0xFFFFu) {
printf("BAD 2B\n");
		return false;
	}
	sfp_list_offset++;

	uint16_t sfp_id;
	if (!ixgbe_eeprom_read(addr, sfp_list_offset, &sfp_id)) {
printf("NO ID\n");
		return false;
	}

	uint16_t sfp_data_offset = 0u;
	while (sfp_id != 0xFFFFu) {
//		printf("SFP ID 0x%04"PRIx16"\n", sfp_id);
		if (sfp_id == 3u){//3u) {
			sfp_list_offset = (uint16_t) (sfp_list_offset + 1u);
			if (!ixgbe_eeprom_read(addr, sfp_list_offset, &sfp_data_offset)) {
printf("NO DATA OFF\n");
				return false;
			}
		}
		sfp_list_offset = (uint16_t) (sfp_list_offset + 2u);
		if (!ixgbe_eeprom_read(addr, sfp_list_offset, &sfp_id)) {
printf("NO ID, redux\n");
			return false;
		}
	}

	if (sfp_data_offset == 0u || sfp_data_offset == 0xFFFFu) {
printf("NO SFP DATA OFF, redux\n");
		return false;
	}

	if (!ixgbe_lock_resources(addr)) {
printf("no lock\n");
		return false;
	}

	sfp_data_offset = (uint16_t) (sfp_data_offset + 1u);

	uint16_t sfp_data;
	if (!ixgbe_eeprom_read(addr, sfp_data_offset, &sfp_data)) {
printf("no sfp data\n");
		return false;
	}
#define IXGBE_REG_CORECTL(_) 0x014F00u
	while (sfp_data != 0xFFFFu) {
//	printf("i haz read %"PRIu16"\n", sfp_data);fflush(stdout);
		IXGBE_REG_WRITE(addr, CORECTL, _, sfp_data);
		sfp_data_offset = (uint16_t) (sfp_data_offset + 1u);
		if (!ixgbe_eeprom_read(addr, sfp_data_offset, &sfp_data)) {
printf("no sfp data, redux\n");fflush(stdout);
			return false;
		}
	}
printf("sfp done! :)\n");fflush(stdout);
	ixgbe_unlock_resources(addr);

	return true;
}


// -------------------------------------
// Section 4.6.3 Initialization Sequence
// -------------------------------------

static void ixgbe_device_disable_interrupts(const uintptr_t addr)
{
	for (uint32_t n = 0; n < IXGBE_INTERRUPT_REGISTERS_COUNT; n++) {
		IXGBE_REG_CLEAR(addr, EIMC, n, MASK);
	}
}

bool ixgbe_device_init(const uintptr_t addr)
{
	// "The following sequence of commands is typically issued to the device by the software device driver in order to initialize the 82599 for normal operation.
	//  The major initialization steps are:"


	// "- Disable interrupts"
	// "- Issue global reset and perform general configuration (see Section 4.6.3.2)."

	// Section 4.6.3.1 Interrupts During Initialization:
	// 	"Most drivers disable interrupts during initialization to prevent re-entrance.
	// 	 Interrupts are disabled by writing to the EIMC registers.
	//	 Note that the interrupts also need to be disabled after issuing a global reset, so a typical driver initialization flow is:
	//	 1. Disable interrupts.
	//	 2. Issue a global reset.
	//	 3. Disable interrupts (again)."

	// Section 4.6.3.2 Global Reset and General Configuration
	//	"Device initialization typically starts with a software reset that puts the device into a known state and enables the device driver to continue the initialization sequence.
	//	 Following a Global Reset the Software driver should wait at least 10msec to enable smooth initialization flow."
	ixgbe_device_disable_interrupts(addr);
	ixgbe_device_reset(addr);
	tn_sleep_us(10 * 1000);
	ixgbe_device_disable_interrupts(addr);

// TODO moveme
ixgbe_device_init_sfp(addr);
// TODO dpdk driver does a check for the firmware version; we should at least state this in our assumptions?

	//	"To enable flow control, program the FCTTV, FCRTL, FCRTH, FCRTV and FCCFG registers.
	//	 If flow control is not enabled, these registers should be written with 0x0.
	//	 If Tx flow control is enabled then Tx CRC by hardware should be enabled as well (HLREG0.TXCRCEN = 1b).
	//	 Refer to Section 3.7.7.3.2 through Section 3.7.7.3.5 for the recommended setting of the Rx packet buffer sizes and flow control thresholds.
	//	 Note that FCRTH[n].RTH fields must be set by default regardless if flow control is enabled or not.
	//	 Typically, FCRTH[n] default value should be equal to RXPBSIZE[n]-0x6000. FCRTH[n].
	//	 FCEN should be set to 0b if flow control is not enabled as all the other registers previously indicated."
	// INTERPRETATION: Sections 3.7.7.3.{2-5} are irrelevant here since we do not want flow control.
	for (uint32_t n = 0; n < IXGBE_FCTTV_REGISTERS_COUNT; n++) {
		IXGBE_REG_CLEAR(addr, FCTTV, n);
	}
	for (uint32_t n = 0; n < IXGBE_FCRTL_REGISTERS_COUNT; n++) {
		IXGBE_REG_CLEAR(addr, FCRTL, n);
	}
	for (uint32_t n = 0; n < IXGBE_FCRTH_REGISTERS_COUNT; n++) {
		IXGBE_REG_CLEAR(addr, FCRTH, n);
	}
	IXGBE_REG_CLEAR(addr, FCRTV, _);
	IXGBE_REG_CLEAR(addr, FCCFG, _);
	// Section 8.2.3.8.9 Receive Packet Buffer Size (RXPBSIZE[n])
	//	"The size is defined in KB units and the default size of PB[0] is 512 KB."
	// Section 8.2.3.3.4 Flow Control Receive Threshold High (FCRTH[n])
	//	"Bits 4:0; Reserved"
	//	"RTH: Bits 18:5; Receive packet buffer n FIFO high water mark for flow control transmission (32 bytes granularity)."
	//	"Bits 30:19; Reserved"
	//	"FCEN: Bit 31; Transmit flow control enable for packet buffer n."
	//	"This register contains the receive threshold used to determine when to send an XOFF packet and counts in units of bytes.
	//	 This value must be at least eight bytes less than the maximum number of bytes allocated to the receive packet buffer and the lower four bits must be programmed to 0x0 (16-byte granularity).
	//	 Each time the receive FIFO reaches the fullness indicated by RTH, hardware transmits a pause frame if the transmission of flow control frames is enabled."
	// INTERPRETATION: There is an obvious contradiction in the stated granularities (16 vs 32 bytes). We assume 32 is correct, since the DPDK ixgbe driver treats it that way..
	// INTERPRETATION: We assume that the "RXPBSIZE[n]-0x6000" calculation above refers to the RXPBSIZE in bytes (otherwise the size of FCRTH[n].RTH would be negative by default...)
	//                 Thus we set FCRTH[0].RTH = 512 * 1024 - 0x6000, which importantly has the 5 lowest bits unset.
	IXGBE_REG_WRITE(addr, FCRTH, 0, RTH, 512 * 1024 - 0x6000);

	// "- Wait for EEPROM auto read completion."
	// INTERPRETATION: This refers to Section 8.2.3.2.1 EEPROM/Flash Control Register (EEC), Bit 9 "EEPROM Auto-Read Done"
	// INTERPRETATION: We also need to check bit 8 of the same register, "EEPROM Present", which indicates "EEPROM is present and has the correct signature field. This bit is read-only.",
	//                 since bit 9 "is also set when the EEPROM is not present or whether its signature field is not valid."
	// INTERPRETATION: We also need to check whether the EEPROM has a valid checksum, using the FWSM's register EXT_ERR_IND, where "0x00 = No error"
	// INTERPRETATION: No timeout is mentioned, so we use 1s.
	bool eeprom_timed_out;
	WAIT_WITH_TIMEOUT(eeprom_timed_out, 1000 * 1000, !IXGBE_REG_CLEARED(addr, EEC, _, AUTORD));
	if (eeprom_timed_out || IXGBE_REG_CLEARED(addr, EEC, _, EEPRES) || !IXGBE_REG_CLEARED(addr, FWSM, _, EXTERRIND)) {
		TN_INFO("EEPROM auto read timed out");
		return false;
	}

	// "- Wait for DMA initialization done (RDRXCTL.DMAIDONE)."
	// INTERPRETATION: Once again, no timeout mentioned, so we use 1s
	bool dma_timed_out;
	WAIT_WITH_TIMEOUT(dma_timed_out, 1000 * 1000, !IXGBE_REG_CLEARED(addr, RDRXCTL, _, DMAIDONE));
	if (dma_timed_out) {
		TN_INFO("DMA init timed out");
		return false;
	}

	// "- Setup the PHY and the link (see Section 4.6.4)."
	// ASSUMPTION: The cables are already plugged in.
	// INTERPRETATION: We don't need to do anything here.

	// "- Initialize all statistical counters (see Section 4.6.5)."
	// ASSUMPTION: We do not care about statistics.
	// INTERPRETATION: We don't need to do anything here.

	// "- Initialize receive (see Section 4.6.7)."
	// Section 4.6.7 Receive Initialization
	//	"Initialize the following register tables before receive and transmit is enabled:"

	//	"- Receive Address (RAL[n] and RAH[n]) for used addresses."
	//	"Program the Receive Address register(s) (RAL[n], RAH[n]) per the station address
	//	 This can come from the EEPROM or from any other means (for example, it could be stored anywhere in the EEPROM or even in the platform PROM for LOM design)."
	//	Section 8.2.3.7.9 Receive Address High (RAH[n]):
	//		"After reset, if the EEPROM is present, the first register (Receive Address Register 0) is loaded from the IA field in the EEPROM, its Address Select field is 00b, and its Address Valid field is 1b."
	// INTERPRETATION: Since we checked that the EEPROM is present and valid, RAH[0] and RAL[0] are initialized from the EEPROM, thus we do not need to initialize them.

	//	"- Receive Address High (RAH[n].VAL = 0b) for unused addresses."
	//	Section 8.2.3.7.9 Receive Address High (RAH[n]):
	//		"After reset, if the EEPROM is present, the first register (Receive Address Register 0) is loaded [...] The Address Valid field for all of the other registers are 0b."
	// INTERPRETATION: Since we checked that the EEPROM is present and valid, RAH[n] for n != 0 has Address Valid == 0, thus we do not need to initialize them.

	//	"- Unicast Table Array (PFUTA)."
	//	Section 8.2.3.27.12 PF Unicast Table Array (PFUTA[n]):
	//		"This table should be zeroed by software before start of operation."
	for (uint32_t n = 0; n < IXGBE_PFUTA_REGISTERS_COUNT; n++) {
		IXGBE_REG_CLEAR(addr, PFUTA, n);
	}

	//	"- VLAN Filter Table Array (VFTA[n])."
	//	Section 7.1.1.2 VLAN Filtering:
	//		Figure 7-3 states that matching to a valid VFTA[n] is only done if VLNCTRL.VFE is set.
	//	Section 8.2.3.7.2 VLAN Control Register (VLNCTRL):
	//		"VFE: Bit 30; Init val: 0; VLAN Filter Enable. 0b = Disabled (filter table does not decide packet acceptance)"
	// INTERPRETATION: By default, VLAN filtering is disabled, and the value of VFTA[n] does not matter; thus we do not need to initialize them.

	//	"- VLAN Pool Filter (PFVLVF[n])."
	// INTERPRETATION: While the spec appears to mention PFVLVF only in conjunction with VLNCTRL.VFE being enabled, let's be conservative and initialize them anyway.
	// 	Section 8.2.3.27.15 PF VM VLAN Pool Filter (PFVLVF[n]):
	//		"Software should initialize these registers before transmit and receive are enabled."
	for (uint32_t n = 0; n < IXGBE_PFVLVF_REGISTERS_COUNT; n++) {
		IXGBE_REG_CLEAR(addr, PFVLVF, n);
	}

	//	"- MAC Pool Select Array (MPSAR[n])."
	//	Section 8.2.3.7.10 MAC Pool Select Array (MPSAR[n]):
	//		"Software should initialize these registers before transmit and receive are enabled."
	//		"Each couple of registers '2*n' and '2*n+1' are associated with Ethernet MAC address filter 'n' as defined by RAL[n] and RAH[n].
	//		 Each bit when set, enables packet reception with the associated pools as follows:
	//		 Bit 'i' in register '2*n' is associated with POOL 'i'.
	//		 Bit 'i' in register '2*n+1' is associated with POOL '32+i'."
	// INTERPRETATION: We should enable all pools with address 0, just in case, and disable everything else since we only have 1 MAC address.
	IXGBE_REG_WRITE(addr, MPSAR, 0, 0xFFFFFFFF);
	IXGBE_REG_WRITE(addr, MPSAR, 1, 0xFFFFFFFF);
	for (uint32_t n = 2; n < IXGBE_MPSAR_REGISTERS_COUNT; n++) {
		IXGBE_REG_CLEAR(addr, MPSAR, n);
	}

	//	"- VLAN Pool Filter Bitmap (PFVLVFB[n])."
	// INTERPRETATION: See above remark on PFVLVF
	//	Section 8.2.3.27.16: PF VM VLAN Pool Filter Bitmap
	for (uint32_t n = 0; n < IXGBE_PFVLVFB_REGISTERS_COUNT; n++) {
		IXGBE_REG_CLEAR(addr, PFVLVFB, n);
	}

	//	"Set up the Multicast Table Array (MTA) registers.
	//	 This entire table should be zeroed and only the desired multicast addresses should be permitted (by writing 0x1 to the corresponding bit location).
	//	 Set the MCSTCTRL.MFE bit if multicast filtering is required."
	for (uint32_t n = 0; n < IXGBE_MTA_REGISTERS_COUNT; n++) {
		IXGBE_REG_CLEAR(addr, MTA, n);
	}

	//	"Initialize the flexible filters 0...5 — Flexible Host Filter Table registers (FHFT)."
	//	Section 5.3.3.2 Flexible Filter:
	//		"The 82599 supports a total of six host flexible filters.
	//		 Each filter can be configured to recognize any arbitrary pattern within the first 128 bytes of the packet.
	//		 To configure the flexible filter, software programs the required values into the Flexible Host Filter Table (FHFT).
	//		 These contain separate values for each filter.
	//		 Software must also enable the filter in the WUFC register, and enable the overall wake-up functionality must be enabled by setting the PME_En bit in the PMCSR or the WUC register."
	//	Section 8.2.3.24.2 Wake Up Filter Control Register (WUFC):
	//		"FLX{0-5}: Bits {16-21}; Init val 0b; Flexible Filter {0-5} Enable"
	// ASSUMPTION: We do not want flexible filters.
	// INTERPRETATION: Since WUFC.FLX{0-5} are disabled by default, and FHFT(n) only matters if the corresponding WUFC.FLX is enabled, we do not need to do anything as we do not want flexible filters.

	//	"After all memories in the filter units previously indicated are initialized, enable ECC reporting by setting the RXFECCERR0.ECCFLT_EN bit."
	//	Section 8.2.3.7.23 Rx Filter ECC Err Insertion 0 (RXFECCERR0):
	//		"Filter ECC Error indication Enablement.
	//		 When set to 1b, enables the ECC-INT + the RXF-blocking during ECC-ERR in one of the Rx filter memories.
	//		 At 0b, the ECC logic can still function overcoming only single errors while dual or multiple errors can be ignored silently."
	// INTERPRETATION: Since we do not want flexible filters, this step is not necessary.

	//	"Program the different Rx filters and Rx offloads via registers FCTRL, VLNCTRL, MCSTCTRL, RXCSUM, RQTC, RFCTL, MPSAR, RSSRK, RETA, SAQF, DAQF, SDPQF, FTQF, SYNQF, ETQF, ETQS, RDRXCTL, RSCDBU."
	//	"Note that RDRXCTL.CRCStrip and HLREG0.RXCRCSTRP must be set to the same value. At the same time the RDRXCTL.RSCFRSTSIZE should be set to 0x0 as opposed to its hardware default."
	// We do not touch FCTRL here, if the user wants promiscuous mode they will call the appropriate function.
	//	Section 8.2.3.7.2 VLAN Control Register (VLNCTRL):
	//		"Bit 30, VLAN Filter Enable, Init val 0b; 0b = Disabled."
	// ASSUMPTION: We do not want VLAN handling.
	// INTERPRETATION: Since we do not want VLAN handling, we do not need to set up VLNCTRL.
	//	Section 8.2.3.7.2 Multicast Control Register (MCSTCTRL):
	//		"Bit 2, Multicast Filter Enable, Init val 0b; 0b = The multicast table array filter (MTA[n]) is disabled."
	// ASSUMPTION: We do not want multicast filtering.
	// INTERPRETATION: Since multicast filtering is disabled by default, we do not need to set up MCSTCTRL.
	// 	Section 8.2.3.7.5 Receive Checksum Control (RXCSUM):
	//		"Bit 12, Init val 0b, IP Payload Checksum Enable."
	//		"Bit 13, Init val 0b, RSS/Fragment Checksum Status Selection."
	//		"The Receive Checksum Control register controls the receive checksum offloading features of the 82599."
	// ASSUMPTION: We do not want receive checksum offloading.
	// INTERPRETATION: Since checksum offloading is disabled by default, we do not need to set up RXCSUM.
	//	Section 8.2.3.7.13 RSS Queues Per Traffic Class Register (RQTC):
	//		"RQTC{0-7}, This field is used only if MRQC.MRQE equals 0100b or 0101b."
	//	Section 8.2.3.7.12 Multiple Receive Queues Command Register (MRQC):
	//		"MRQE, Init val 0x0"
	// ASSUMPTION: We do not want RSS.
	// INTERPRETATION: Since RSS is disabled by default, we do not need to do anything.
	//	Section 8.2.3.7.6 Receive Filter Control Register (RFCTL):
	//		"Bit 5, Init val 0b; RSC Disable. The default value is 0b (RSC feature is enabled)."
	//		"Bit 6, Init val 0b; NFS Write disable."
	//		"Bit 7, Init val 0b; NFS Read disable."
	// ASSUMPTION: We do not care about RSC.
	// ASSUMPTION: We do not care about NFS.
	// INTERPRETATION: We do not need to write to RFCTL.
	// We already initialized MPSAR earlier.
	//	Section 4.6.10.1.1 Global Filtering and Offload Capabilities:
	//		"In RSS mode, the RSS key (RSSRK) and redirection table (RETA) should be programmed."
	// INTERPRETATION: Since we do not want RSS, we do not need to touch RSSRK or RETA.
	//	Section 8.2.3.7.19 Five tuple Queue Filter (FTQF[n]):
	//		All bits have an unspecified default value.
	//		"Mask, bits 29:25: Mask bits for the 5-tuple fields (1b = don’t compare)."
	//		"Queue Enable, bit 31; When set, enables filtering of Rx packets by the 5-tuple defined in this filter to the queue indicated in register L34TIMIR."
	// ASSUMPTION: We do not want 5-tuple filtering.
	// INTERPRETATION: We clear Queue Enable, and set the mask to 0b11111 just in case. We then do not need to deal with SAQF, DAQF, SDPQF, SYNQF.
	for (uint32_t n = 0; n < IXGBE_FTQF_REGISTERS_COUNT; n++) {
		IXGBE_REG_SET(addr, FTQF, n, MASK);
		IXGBE_REG_CLEAR(addr, FTQF, n, QUEUEENABLE);
	}
	//	Section 7.1.2.3 L2 Ethertype Filters:
	//		"The following flow is used by the Ethertype filters:
	//		 1. If the Filter Enable bit is cleared, the filter is disabled and the following steps are ignored."
	//	Section 8.2.3.7.21 EType Queue Filter (ETQF[n]):
	//		"Bit 31, Filter Enable, Init val 0b; 0b = The filter is disabled for any functionality."
	// ASSUMPTION: We do not want L2 ethertype filtering.
	// INTERPRETATION: Since filters are disabled by default, we do not need to do anything to ETQF and ETQS.
	//	Section 8.2.3.8.8 Receive DMA Control Register (RDRXCTL):
	//		The only non-reserved, non-RO bit is "CRCStrip, bit 1, Init val 0; 0b = No CRC Strip by HW."
	// ASSUMPTION: We do not want HW CRC strip.
	// INTERPRETATION: We do not need to change RDRXCTL.
	//	Section 8.2.3.8.12 RSC Data Buffer Control Register (RSCDBU):
	//		The only non-reserved bit is "RSCACKDIS, bit 7, init val 0b; Disable RSC for ACK Packets."
	// ASSUMPTION: We do not care of disabling RSC for ACK packets.
	// INTERPRETATION: We do not need to change RSCDBU.

	//	"Program RXPBSIZE, MRQC, PFQDE, RTRUP2TC, MFLCN.RPFCE, and MFLCN.RFCE according to the DCB and virtualization modes (see Section 4.6.11.3)."
	//	Section 4.6.11.3.4 DCB-Off, VT-Off:
	//		"Set the configuration bits as specified in Section 4.6.11.3.1 with the following exceptions:"
	//		"Disable multiple packet buffers and allocate all queues and traffic to PB0:"
	//		"- RXPBSIZE[0].SIZE=0x200, RXPBSIZE[1-7].SIZE=0x0"
	//		Section 8.2.3.8.9 Receive Packet Buffer Size (RXPBSIZE[n]):
	//			"SIZE, Init val 0x200"
	//			"The default size of PB[1-7] is also 512 KB but it is meaningless in non-DCB mode."
	// INTERPRETATION: We do not need to change PB[0]. Let's stay on the safe side and clear PB[1-7] to 0 anyway.
	for (uint32_t n = 1; n < IXGBE_RXPBSIZE_REGISTERS_COUNT; n++) {
		IXGBE_REG_CLEAR(addr, RXPBSIZE, n);
	}
	//		"- TXPBSIZE[0].SIZE=0xA0, TXPBSIZE[1-7].SIZE=0x0"
	//		Section 8.2.3.9.13 Transmit Packet Buffer Size (TXPBSIZE[n]):
	//			"SIZE, Init val 0xA0"
	//			"At default setting (no DCB) only packet buffer 0 is enabled and TXPBSIZE values for TC 1-7 are meaningless."
	// INTERPRETATION: We do not need to change TXPBSIZE[0]. Let's stay on the safe side and clear TXPBSIZE[1-7] anyway.
	for (uint32_t n = 1; n < IXGBE_TXPBSIZE_REGISTERS_COUNT; n++) {
		IXGBE_REG_CLEAR(addr, TXPBSIZE, n);
	}
	//		"- TXPBTHRESH.THRESH[0]=0xA0 — Maximum expected Tx packet length in this TC TXPBTHRESH.THRESH[1-7]=0x0"
	// INTERPRETATION: Typo in the spec; should be TXPBTHRESH[0].THRESH
	//		Section 8.2.3.9.16 Tx Packet Buffer Threshold (TXPBTHRESH):
	//			"Default values: 0x96 for TXPBSIZE0, 0x0 for TXPBSIZE1-7."
	// INTERPRETATION: Typo in the spec, this refers to TXPBTHRESH, not TXPBSIZE.
	// Thus we need to set TXPBTHRESH[0] but not TXPBTHRESH[1-7].
	IXGBE_REG_WRITE(addr, TXPBTHRESH, 0, THRESH, 0xA0u);
	//		"- MRQC and MTQC"
	//			"- Set MRQE to 0xxxb, with the three least significant bits set according to the RSS mode"
	// 			Section 8.2.3.7.12 Multiple Receive Queues Command Register (MRQC): "MRQE, Init Val 0x0; 0000b = RSS disabled"
	// Thus we do not need to modify MRQC.
	//			"- Clear both RT_Ena and VT_Ena bits in the MTQC register."
	//			"- Set MTQC.NUM_TC_OR_Q to 00b."
	//			Section 8.2.3.9.15 Multiple Transmit Queues Command Register (MTQC):
	//				"RT_Ena, Init val 0b"
	//				"VT_Ena, Init val 0b"
	//				"NUM_TC_OR_Q, Init val 00b"
	// Thus we do not need to modify MTQC.
	//		"- Clear PFVTCTL.VT_Ena (as the MRQC.VT_Ena)"
	//		Section 8.2.3.27.1 VT Control Register (PFVTCTL):
	//			"VT_Ena, Init val 0b"
	// Thus we do not need to modify PFVTCTL.
	//		(from 4.6.11.3.1) "Queue Drop Enable (PFQDE) — In SR-IO the QDE bit should be set to 1b in the PFQDE register for all queues. In VMDq mode, the QDE bit should be set to 0b for all queues."
	// ASSUMPTION: We do not need SR-IO or VMDq.
	// INTERPRETATION: We do not need to change PFQDE.
	//		"- Rx UP to TC (RTRUP2TC), UPnMAP=0b, n=0,...,7"
	//		Section 8.2.3.10.4 DCB Receive User Priority to Traffic Class (RTRUP2TC): All init vals = 0
	// Thus we do not need to modify RTRUP2TC.
	//		"- Tx UP to TC (RTTUP2TC), UPnMAP=0b, n=0,...,7"
	//		Section 8.2.3.10.5 DCB Transmit User Priority to Traffic Class (RTTUP2TC): All init vals = 0
	// Thus we do not need to modify RTTUP2TC.
	//		"- DMA TX TCP Maximum Allowed Size Requests (DTXMXSZRQ) — set Max_byte_num_req = 0xFFF = 1 MB"
	IXGBE_REG_WRITE(addr, DTXMXSZRQ, _, MAXBYTESNUMREQ, 0xFFF);
	//		"Allow no-drop policy in Rx:"
	//		"- PFQDE: The QDE bit should be set to 0b in the PFQDE register for all queues enabling per queue policy by the SRRCTL[n] setting."
	//		Section 8.2.3.27.9 PF PF Queue Drop Enable Register (PFQDE): "QDE, Init val 0b"
	// Thus we do not need to modify PFQDE.
	//		"- Split Receive Control (SRRCTL[0-127]): The Drop_En bit should be set per receive queue according to the required drop / no-drop policy of the TC of the queue."
	//		Section 8.2.3.8.7 Split Receive Control Registers (SRRCTL[n]): "Drop_En, Init val 0b; Drop Enabled."
	// ASSUMPTION: We do not want to drop packets.
	// Thus we do not need to modify SRRCTL.
	//		"Disable PFC and enable legacy flow control:"
	//		"- Disable receive PFC via: MFLCN.RPFCE=0b"
	//		Section 8.2.3.22.34 MAC Flow Control Register (MFLCN): "RPFCE, Init val 0b"
	// Thus we do not need to modify MFLCN.
	//		"- Enable receive legacy flow control via: MFLCN.RFCE=1b"
	IXGBE_REG_WRITE(addr, MFLCN, _, RFCE, 1);
	//		"- Enable transmit legacy flow control via: FCCFG.TFCE=01b"
	IXGBE_REG_WRITE(addr, FCCFG, _, TFCE, 1);
	//		"Reset all arbiters:"
	//		"- Clear RTTDT1C register, per each queue, via setting RTTDQSEL first"
	for (uint32_t n = 0; n < IXGBE_TX_QUEUE_POOLS_COUNT; n++) {
		IXGBE_REG_WRITE(addr, RTTDQSEL, _, TXDQIDX, n);
		IXGBE_REG_CLEAR(addr, RTTDT1C, _);
	}
	//		"- Clear RTTDT2C[0-7] registers"
	for (uint32_t n = 0; n < IXGBE_RTTDT2C_REGISTERS_COUNT; n++) {
		IXGBE_REG_CLEAR(addr, RTTDT2C, n);
	}
	//		"- Clear RTTPT2C[0-7] registers"
	for (uint32_t n = 0; n < IXGBE_RTTPT2C_REGISTERS_COUNT; n++) {
		IXGBE_REG_CLEAR(addr, RTTPT2C, n);
	}
	//		"- Clear RTRPT4C[0-7] registers"
	for (uint32_t n = 0; n < IXGBE_RTRPT4C_REGISTERS_COUNT; n++) {
		IXGBE_REG_CLEAR(addr, RTRPT4C, n);
	}
	//		"Disable TC and VM arbitration layers:"
	//		"- Tx Descriptor Plane Control and Status (RTTDCS), bits: TDPAC=0b, VMPAC=0b, TDRM=0b, BDPM=1b, BPBFSM=1b"
	//		Section 8.2.3.10.2 DCB Transmit Descriptor Plane Control and Status (RTTDCS): the above values are the default ones
	// Thus we do not need to modify RTTDCS.
	//		"- Tx Packet Plane Control and Status (RTTPCS): TPPAC=0b, TPRM=0b, ARBD=0x224"
	//		Section 8.2.3.10.3 DCB Transmit Packet Plane Control and Status (RTTPCS): the above values are the default ones
	// Thus we do not need to modify RTTPCS.
	//		"- Rx Packet Plane Control and Status (RTRPCS): RAC=0b, RRM=0b"
	//		Section 8.2.3.10.1 DCB Receive Packet Plane Control and Status (RTRPCS): the above values are the default ones
	// Thus we do not need to modify RTTPCS.
	//		(from 4.6.11.3.1) "Set the SECTXMINIFG.SECTXDCB field to 0x1F."
	//		Section 8.2.3.12.4 Security Tx Buffer Minimum IFG (SECTXMINIFG):
	//			"If PFC is enabled, then the SECTXDCB field should be set to 0x1F.
	//			 If PFC is not enabled, then the default value should be used (0x10)."
	//		Section 8.2.3.22.34 MAC Flow Control Register:
	//			"Note: PFC should be enabled in DCB mode only."
	// INTERPRETATION: Despite the lack of an explicit exception, this part of Section 4.6.11.3.1 does not apply in this case.

	//	"Enable jumbo reception by setting HLREG0.JUMBOEN in one of the following two cases:
	//	 1. Jumbo packets are expected. Set the MAXFRS.MFS to expected max packet size.
	//	 2. LinkSec encapsulation is expected."
	// ASSUMPTION: We do not want jumbo or LinkSec packets.
	// Thus we do not have anything to do here.

	//	"Enable receive coalescing if required as described in Section 4.6.7.2."
	// Since we do not require it, we do not need to do anything.

	// We do not set up receive queues at this point.


	// "- Initialize transmit (see Section 4.6.8)."
	//	Section 4.6.8 Transmit Initialization:
	//		"- Program the HLREG0 register according to the required MAC behavior."
	//		Section 8.2.3.22.8 MAC Core Control 0 Register (HLREG0):
	//			"TXCRCEN, Init val 1b; Tx CRC Enable, Enables a CRC to be appended by hardware to a Tx packet if requested by user."
	// INTERPRETATION: We do not need to explicitly disable this, since it only allows the user to request it, but does not do it automatically.
	//			"TXPADEN, Init val 1b; Tx Pad Frame Enable. Pad short Tx frames to 64 bytes if requested by user."
	// INTERPRETATION: We do not need to explicitly disable this, since it only allows the user to request it, but does not do it automatically.
	//			"LPBK, Init val 0b; LOOPBACK. Turn On Loopback Where Transmit Data Is Sent Back Through Receiver."
	// ASSUMPTION: We do not want loopback.
	// Thus we do not need to change this.
	//			There are two more registers for MDC, and one for CRC, which we do not care about here. TODO be a bit more formal for this... too lazy right now...
	//		"- Program TCP segmentation parameters via registers DMATXCTL (while maintaining TE bit cleared), DTXTCPFLGL, and DTXTCPFLGH; and DCA parameters via DCA_TXCTRL."
	//			Section 8.2.3.9.2 DMA Tx Control (DMATXCTL):
	//				There is only one field besides TE that the user should modify: "GDV, Init val 0b, Global Double VLAN Mode."
	// ASSUMPTION: We do not want global double VLAN mode.
	// Thus we do not need to change DMATXCTL for now.
	//			Section 8.2.3.9.3 DMA Tx TCP Flags Control Low (DTXTCPFLGL),
	//			Section 8.2.3.9.4 DMA Tx TCP Flags Control High (DTXTCPFLGH):
	//				"This register holds the mask bits for the TCP flags in Tx segmentation."
	// INTERPRETATION: The default values make sense for TCP.
	// Thus we do not need to modify DTXTCPFLGL/H.
	//			Section 8.2.3.11.2 Tc DCA Control Registers (DCA_TXCTRL[n]):
	//				"Tx Descriptor DCA EN, Init val 0b; Descriptor DCA Enable. When set, hardware enables DCA for all Tx descriptors written back into memory.
	//				 When cleared, hardware does not enable DCA for descriptor write-backs. This bit is cleared as a default and also applies to head write back when enabled."
	//				"CPUID, Init val 0x0, Physical ID (see complete description in Section 3.1.3.1.2)
	//				 Legacy DCA capable platforms — the device driver, upon discovery of the physical CPU ID and CPU bus ID, programs the CPUID field with the physical CPU and bus ID associated with this Tx queue.
	//				 DCA 1.0 capable platforms — the device driver programs a value, based on the relevant APIC ID, associated with this Tx queue."
	// ASSUMPTION: We want DCA, since it helps performance.
	// TODO: Actually implement it.
	// TODO: DCA for RX as well.
	// TODO: Benchmark with DCA enabled and disabled.
	//				There are fields dealing with relaxed ordering; Section 3.1.4.5.3 Relaxed Ordering states that it "enables the system to optimize performance", with no apparent correctness impact.
	// INTERPRETATION: Relaxed ordering has no correctness issues, and thus should be enabled.
	// TODO: Benchmark with relaxed ordering enabled and disabled.
	//		"- Set RTTDCS.ARBDIS to 1b."
	//		"- Program DTXMXSZRQ, TXPBSIZE, TXPBTHRESH, MTQC, and MNGTXMAP, according to the DCB and virtualization modes (see Section 4.6.11.3)."
	//		"- Clear RTTDCS.ARBDIS to 0b"
	// INTERPRETATION: The spec forgot to mention it earlier, but MTQC requires ARBDIS to be disabled (see Section 7.2.1.2.1 Tx Queues Assignment).
	// We've already done DCB/VT config earlier, no need to do anything here.

	// TODO: Look into Section 7.1.10 and the related errata about header splitting.

	// "- Enable interrupts (see Section 4.6.3.1)."
	// Section 4.6.3.1 Interrupts During Initialization "After initialization completes, a typical driver enables the desired interrupts by writing to the IMS register."
	// ASSUMPTION: We do not want interrupts.
	// INTERPRETATION: We don't need to do anything here.

	return true;
}

bool ixgbe_device_set_promiscuous(const uintptr_t addr)
{
	// Section 8.2.3.7.1 Filter Control Register:
	// "Before receive filters are updated/modified the RXCTRL.RXEN bit should be set to 0b.
	// After the proper filters have been set the RXCTRL.RXEN bit can be set to 1b to re-enable the receiver."
	bool was_rx_enabled = !IXGBE_REG_CLEARED(addr, RXCTRL, _, RXEN);
	if (was_rx_enabled) {
		IXGBE_REG_CLEAR(addr, RXCTRL, _, RXEN);
	}

	// "Multicast Promiscuous Enable. 1b = Enabled."
	IXGBE_REG_SET(addr, FCTRL, _, MPE);
	// "Unicast Promiscuous Enable. 1b = Enabled.
	IXGBE_REG_SET(addr, FCTRL, _, UPE);
	// "Broadcast Accept Mode. 1b = Accept broadcast packets to host."
	IXGBE_REG_SET(addr, FCTRL, _, BAM);

	if (was_rx_enabled) {
		IXGBE_REG_SET(addr, RXCTRL, _, RXEN);
	}

	// This function cannot fail (for now?)
	return true;
}

bool ixgbe_device_init_receive(const uintptr_t addr, const uint8_t queue, const uintptr_t ring_addr, const uint16_t ring_size, const uintptr_t buffer_addr)
{
	// At this point we need to write 64-bit memory values, so pointers better be 64 bits!
	if (UINTPTR_MAX != UINT64_MAX) {
		TN_INFO("Wrong size of uintptr_t");
		return false;
	}

	// Section 4.6.7.1 Dynamic Enabling and Disabling of Receive Queues:
	// "Receive queues can be enabled or disabled dynamically using the following procedure."
	// Section 4.6.7.1.1 Enabling:
	// "Follow the per queue initialization described in the previous section."

	// Section 4.6.7 Receive Initialization:
	// "The following should be done per each receive queue:"

	// "- Allocate a region of memory for the receive descriptor list."
	// Given to us as 'ring_addr'

	// "- Receive buffers of appropriate size should be allocated and pointers to these buffers should be stored in the descriptor ring."
	// The buffers are given to us as 'buffer_addr'
	uint64_t* ring = (uint64_t*) ring_addr;
	for (uint16_t n = 0; n < ring_size; n++) {
		// Section 7.1.6.1 Advanced Receive Descriptors - Read Format:
		// Line 0 - Packet Buffer Address
		uintptr_t virt_buffer_addr = buffer_addr + (uintptr_t) (n * IXGBE_RECEIVE_PACKET_SIZE_MAX);
		uintptr_t phys_buffer_addr = tn_mem_virtual_to_physical_address(virt_buffer_addr);
		if (phys_buffer_addr == (uintptr_t) -1) {
			// TODO tn_mem_virt_to_phys makes it too easy to forget to handle the error...
			TN_INFO("Buffer address could not be mapped to a physical address");
			return false;
		}
		ring[n * 2u] = phys_buffer_addr;
		// Line 1 - Header Buffer Address (63:1), Descriptor Done (0)
		ring[n * 2u + 1u] = 0u;
	}

	// "- Program the descriptor base address with the address of the region (registers RDBAL, RDBAL)."
	// INTERPRETATION: This is a typo, the second "RDBAL" should read "RDBAH".
	uintptr_t phys_ring_addr = tn_mem_virtual_to_physical_address(ring_addr);
	if (phys_ring_addr == (uintptr_t) -1) {
		TN_INFO("Ring address could not be mapped to a physical address");
		return false;
	}
	IXGBE_REG_WRITE(addr, RDBAH, queue, (uint32_t) (phys_ring_addr >> 32));
	IXGBE_REG_WRITE(addr, RDBAL, queue, (uint32_t) (phys_ring_addr & 0xFFFFFFFFu));

	// "- Set the length register to the size of the descriptor ring (register RDLEN)."
	// Section 8.2.3.8.3 Receive DEscriptor Length (RDLEN[n]):
	// "This register sets the number of bytes allocated for descriptors in the circular descriptor buffer. It must be 128-byte aligned"
	// INTERPRETATION: Since each descriptor takes 16 bytes, the size of the ring must be a multiple of 8.
	if (ring_size % 8u != 0u) {
		TN_INFO("Ring size is not a multiple of 8");
		return false;
	}
	IXGBE_REG_WRITE(addr, RDLEN, queue, ring_size * 16u);

	// "- Program SRRCTL associated with this queue according to the size of the buffers and the required header control."
	//	Section 8.2.3.8.7 Split Receive Control Registers (SRRCTL[n]):
	//		"BSIZEPACKET, Receive Buffer Size for Packet Buffer. The value is in 1 KB resolution. Value can be from 1 KB to 16 KB."
	// TODO: Play with PACKET_SIZE_MAX, see if it changes perf in any way.
	IXGBE_REG_WRITE(addr, SRRCTL, queue, BSIZEPACKET, IXGBE_RECEIVE_PACKET_SIZE_MAX / 1024u);
	//		"DESCTYPE, Define the descriptor type in Rx: [...] 001b = Advanced descriptor one buffer."
	IXGBE_REG_WRITE(addr, SRRCTL, queue, DESCTYPE, 1);
	//		"Drop_En, Drop Enabled. If set to 1b, packets received to the queue when no descriptors are available to store them are dropped."
	// ASSUMPTION: We want to drop packets if we can't process them fast enough, to have predictable behavior.
	IXGBE_REG_SET(addr, SRRCTL, queue, DROPEN);

	// "- If header split is required for this queue, program the appropriate PSRTYPE for the appropriate headers."
	// Section 7.1.10 Header Splitting: "Header Splitting mode might cause unpredictable behavior and should not be used with the 82599."

	// "- Program RSC mode for the queue via the RSCCTL register."
	// Nothing to do, we do not want RSC.
	// TODO: Write all assumptions in a single place, then refer to them by ID or something.

	// "- Program RXDCTL with appropriate values including the queue Enable bit. Note that packets directed to a disabled queue are dropped."
	IXGBE_REG_SET(addr, RXDCTL, queue, ENABLE);

	// "- Poll the RXDCTL register until the Enable bit is set. The tail should not be bumped before this bit was read as 1b."
	// INTERPRETATION: No timeout is mentioned here, let's say 1s to be safe.
	// TODO: Categorize all interpretations (e.g. "no timeout", "clear typo", ...)
	bool queue_timed_out;
	WAIT_WITH_TIMEOUT(queue_timed_out, 1000 * 1000, !IXGBE_REG_CLEARED(addr, RXDCTL, queue, ENABLE));
	if (queue_timed_out) {
		TN_INFO("RXDCTL.ENABLE did not set, cannot enable queue");
		return false;
	}

	// "- Bump the tail pointer (RDT) to enable descriptors fetching by setting it to the ring length minus one."
	// Section 7.1.9 Receive Descriptor Queue Structure:
	// "Software inserts receive descriptors by advancing the tail pointer(s) to refer to the address of the entry just beyond the last valid descriptor."
	// INTERPRETATION: There is a clear contradiction here, according to 7.1.9 RDT should be 0 to refer to the entire ring... but empirically, it's indeed ring_size-1.
	IXGBE_REG_WRITE(addr, RDT, queue, ring_size - 1u);

	// "- Enable the receive path by setting RXCTRL.RXEN. This should be done only after all other settings are done following the steps below."
	//	"- Halt the receive data path by setting SECRXCTRL.RX_DIS bit."
	IXGBE_REG_SET(addr, SECRXCTRL, _, RXDIS);
	//	"- Wait for the data paths to be emptied by HW. Poll the SECRXSTAT.SECRX_RDY bit until it is asserted by HW."
	// INTERPRETATION: Another undefined timeout, assuming 1s as usual
	bool sec_timed_out;
	WAIT_WITH_TIMEOUT(sec_timed_out, 1000 * 1000, !IXGBE_REG_CLEARED(addr, SECRXSTAT, _, SECRXRDY));
	if (sec_timed_out) {
		TN_INFO("SECRXSTAT.SECRXRDY timed out, cannot enable queue");
		return false;
	}
	//	"- Set RXCTRL.RXEN"
	IXGBE_REG_SET(addr, RXCTRL, _, RXEN);
	//	"- Clear the SECRXCTRL.SECRX_DIS bits to enable receive data path"
	// INTERPRETATION: This refers to RX_DIS, not SECRX_DIS, since it's RX_DIS being cleared that enables the receive data path.
	IXGBE_REG_CLEAR(addr, SECRXCTRL, _, RXDIS);
	//	"- If software uses the receive descriptor minimum threshold Interrupt, that value should be set."
	// ASSUMPTION: We don't want interrupts.
	// Nothing to do.
	// "  Set bit 16 of the CTRL_EXT register and clear bit 12 of the DCA_RXCTRL[n] register[n]."
	// Section 8.2.3.1.3 Extended Device Control Register (CTRL_EXT): Bit 16 == "NS_DIS, No Snoop Disable"
	IXGBE_REG_SET(addr, CTRLEXT, _, NSDIS);
	// Section 8.2.3.11.1 Rx DCA Control Register (DCA_RXCTRL[n]): Bit 12 == "Default 1b; Reserved. Must be set to 0."
	IXGBE_REG_SET(addr, DCARXCTRL, queue, UNKNOWN);

	
	// TODO document
	// Section 8.2.3.22.19 Auto Negotiation Control Register
	ixgbe_lock_resources(addr);
	// "Link Mode Select. Selects the active link mode: [...] 011b = 10 GbE serial link (SFI – no backplane auto-negotiation)."
	IXGBE_REG_WRITE(addr, AUTOC, _, LMS, 3);
	ixgbe_unlock_resources(addr);

	return true;
}

bool ixgbe_device_init_send(const uintptr_t addr, const uint8_t queue, const uintptr_t ring_addr, const uint16_t ring_size, const uintptr_t buffer_addr)
{
	// Section 4.6.8.1 Dynamic Enabling and Disabling of Transmit Queues:
	// "Transmit queues can be enabled or disabled dynamically if the following procedure is followed."
	// Section 4.6.8.1.1 Enabling:
	// "Follow the per queue initialization described in the previous section."

	// Section 4.6.8 Transmit Initialization:
	// "The following steps should be done once per transmit queue:"
	// "- Allocate a region of memory for the transmit descriptor list."
	// "- Program the descriptor base address with the address of the region (TDBAL, TDBAH)."
	// "- Set the length register to the size of the descriptor ring (TDLEN)."
	// "- Program the TXDCTL register with the desired TX descriptor write back policy (see Section 8.2.3.9.10 for recommended values)."
	// "- If needed, set TDWBAL/TWDBAH to enable head write back."
	// "- Enable transmit path by setting DMATXCTL.TE.
	//    This step should be executed only for the first enabled transmit queue and does not need to be repeated for any following queues."
	// "- Enable the queue using TXDCTL.ENABLE.
	//    Poll the TXDCTL register until the Enable bit is set."
	// "Note: The tail register of the queue (TDT) should not be bumped until the queue is enabled."

	// TODO
	(void)addr;
	(void)queue;
	(void)ring_addr;
	(void)ring_size;
	(void)buffer_addr;
	return false;
}

#include <stdio.h>
#include <inttypes.h>
#define IXGBE_REG_RAL(n) (0x0A200u + 8u*n)
#define IXGBE_REG_RAH(n) (0x0A204u + 8u*n)
#define IXGBE_REG_RDH(n) (n <= 63u ? (0x01010u + 0x40u*n) : (0x0D010u + 0x40u*(n-64u)))
#define IXGBE_REG_LINKS(_) 0x042A4u
#define IXGBE_REG_LINKS2(_) 0x04324u
#define IXGBE_REG_AUTOC2(_) 0x042A8u
#define IXGBE_REG_VLNCTRL(_) 0x05088u
void ixgbe_sanity_check(const uintptr_t addr)
{
	uint32_t vlnctrl = IXGBE_REG_READ(addr, VLNCTRL, _);
	printf("vlnctrl = 0x%08"PRIx32"\n",vlnctrl);

	uint32_t rxdctl0 = IXGBE_REG_READ(addr,RXDCTL,0);
	printf("rxdcl[0] = 0x%08"PRIx32"\n",rxdctl0);

	if (IXGBE_REG_CLEARED(addr, RXCTRL, _, RXEN)) {
		printf("RXEN is cleared!\n");
	}

	if (IXGBE_REG_CLEARED(addr, RXDCTL, 0, ENABLE)) {
		printf("QUEUE ENABLE is cleared!\n");
	}

	uint32_t status = IXGBE_REG_READ(addr,STATUS,_);
	printf("status = 0x%08"PRIx32"\n",status);


	uint32_t links = IXGBE_REG_READ(addr,LINKS,_);
	printf("links = 0x%08"PRIx32"\n",links);
	uint32_t links2 = IXGBE_REG_READ(addr,LINKS2,_);
	printf("links2 = 0x%08"PRIx32"\n",links2);


	IXGBE_REG_FORCE_READ(addr, AUTOC, _);
	uint32_t autoc = IXGBE_REG_READ(addr,AUTOC,_);
	printf("autoc = 0x%08"PRIx32"\n",autoc);
	IXGBE_REG_FORCE_READ(addr, AUTOC2, _);
	uint32_t autoc2 = IXGBE_REG_READ(addr,AUTOC2,_);
	printf("autoc2 = 0x%08"PRIx32"\n",autoc2);

	uint32_t rdbah = IXGBE_REG_READ(addr, RDBAH, 0);
	uint32_t rdbal = IXGBE_REG_READ(addr, RDBAL, 0);
	printf("RDBAH %"PRIu32" RDBAL %"PRIu32"\n",rdbah,rdbal);

	uint32_t len = IXGBE_REG_READ(addr, RDLEN, 0);
	uint32_t rdh = IXGBE_REG_READ(addr, RDH, 0);
	uint32_t rdt = IXGBE_REG_READ(addr, RDT, 0);

	printf("len %"PRIu32"\n", len);
	printf("rdh %"PRIu32" rdt %"PRIu32"\n",rdh,rdt);

	uint32_t ral = IXGBE_REG_READ(addr, RAL, 0);
	uint32_t rah = IXGBE_REG_READ(addr, RAH, 0);
	printf("RAL 0x%" PRIx32 " RAH 0x%"PRIx32"\n", ral,rah);

	printf("End of sanity check.\n");
}


	static uint32_t regs[] = {
		0x04000, 0x04004, 0x04008,
		0x04034, 0x04038, 0x04040,
		0x08780,
		0x041A4, 0x041A8,
		0x04140 + 0,
		0x04140 + 4,
		0x04140 + 8,
		0x04140 + 12,
		0x04140 + 16,
		0x04140 + 20,
		0x04140 + 24,
		0x04140 + 28,
		0x04160 + 0,
		0x04160 + 4,
		0x04160 + 8,
		0x04160 + 12,
		0x04160 + 16,
		0x04160 + 20,
		0x04160 + 24,
		0x04160 + 28,
		0x0405C, 0x04060, 0x04064, 0x04068, 0x0406C, 0x04070, 0x04078, 0x0407C, 0x04074, 0x04088, 0x0408C,
		0x041B0, 0x041B4, 0x041B8,
		0x02F50, 0x02F54, 0x02F58, 0x02F5C, 0x02F60, 0x02F64, 0x02F68, 0x02F6C, 0x02F70, 0x02F74, 0x02F78, 0x02F7C,
		0x04080,
		0x04090, 0x04094,
		0x087A0, 0x087A4, 0x087A8,
		0x040A4, 0x040A8, 0x040B0, 0x040B4, 0x040B8, 0x040C0, 0x040C0, 0x040C4, 0x040D0, 0x040D4, 0x040D8, 0x040DC, 0x040E0, 0x040E4,
			0x040E8, 0x040EC, 0x040F0, 0x040F4, 0x04010, 0x04120,
		0x02300 + 0,
		0x02300 + 1*4,
		0x02300 + 2*4,
		0x02300 + 3*4,
		0x02300 + 4*4,
		0x02300 + 5*4,
		0x02300 + 6*4,
		0x02300 + 7*4,
		0x02300 + 8*4,
		0x02300 + 9*4,
		0x02300 + 10*4,
		0x02300 + 11*4,
		0x02300 + 12*4,
		0x02300 + 13*4,
		0x02300 + 14*4,
		0x02300 + 15*4,
		0x02300 + 16*4,
		0x02300 + 17*4,
		0x02300 + 18*4,
		0x02300 + 19*4,
		0x02300 + 20*4,
		0x02300 + 21*4,
		0x02300 + 22*4,
		0x02300 + 23*4,
		0x02300 + 24*4,
		0x02300 + 25*4,
		0x02300 + 26*4,
		0x02300 + 27*4,
		0x02300 + 28*4,
		0x02300 + 30*4,
		0x02300 + 31*4,
		0x02F40,
		0x08600 + 0*4,
		0x08600 + 1*4,
		0x08600 + 2*4,
		0x08600 + 3*4,
		0x08600 + 4*4,
		0x08600 + 5*4,
		0x08600 + 6*4,
		0x08600 + 7*4,
		0x08600 + 8*4,
		0x08600 + 9*4,
		0x08600 + 10*4,
		0x08600 + 11*4,
		0x08600 + 12*4,
		0x08600 + 13*4,
		0x08600 + 14*4,
		0x08600 + 15*4,
		0x08600 + 16*4,
		0x08600 + 17*4,
		0x08600 + 18*4,
		0x08600 + 19*4,
		0x08600 + 20*4,
		0x08600 + 21*4,
		0x08600 + 22*4,
		0x08600 + 23*4,
		0x08600 + 24*4,
		0x08600 + 25*4,
		0x08600 + 26*4,
		0x08600 + 27*4,
		0x08600 + 28*4,
		0x08600 + 29*4,
		0x08600 + 30*4,
		0x08600 + 31*4,
		0x01030+0x40*0,
		0x01030+0x40*1,
		0x01030+0x40*2,
		0x01030+0x40*3,
		0x01030+0x40*4,
		0x01030+0x40*5,
		0x01030+0x40*6,
		0x01030+0x40*7,
		0x01030+0x40*8,
		0x01030+0x40*9,
		0x01030+0x40*10,
		0x01030+0x40*11,
		0x01030+0x40*12,
		0x01030+0x40*13,
		0x01030+0x40*14,
		0x01030+0x40*15,
		0x01430+0x40*0,
		0x01430+0x40*1,
		0x01430+0x40*2,
		0x01430+0x40*3,
		0x01430+0x40*4,
		0x01430+0x40*5,
		0x01430+0x40*6,
		0x01430+0x40*7,
		0x01430+0x40*8,
		0x01430+0x40*9,
		0x01430+0x40*10,
		0x01430+0x40*11,
		0x01430+0x40*12,
		0x01430+0x40*13,
		0x01430+0x40*14,
		0x01430+0x40*15,
		0x1034+0x40*0,
		0x1034+0x40*1,
		0x1034+0x40*2,
		0x1034+0x40*3,
		0x1034+0x40*4,
		0x1034+0x40*5,
		0x1034+0x40*6,
		0x1034+0x40*7,
		0x1034+0x40*8,
		0x1034+0x40*9,
		0x1034+0x40*10,
		0x1034+0x40*11,
		0x1034+0x40*12,
		0x1034+0x40*13,
		0x1034+0x40*14,
		0x1034+0x40*15,
		0x1038+0x40*0,
		0x1038+0x40*1,
		0x1038+0x40*2,
		0x1038+0x40*3,
		0x1038+0x40*4,
		0x1038+0x40*5,
		0x1038+0x40*6,
		0x1038+0x40*7,
		0x1038+0x40*8,
		0x1038+0x40*9,
		0x1038+0x40*10,
		0x1038+0x40*11,
		0x1038+0x40*12,
		0x1038+0x40*13,
		0x1038+0x40*14,
		0x1038+0x40*15,
		0x08680+0x4*0,
		0x08680+0x4*1,
		0x08680+0x4*2,
		0x08680+0x4*3,
		0x08680+0x4*4,
		0x08680+0x4*5,
		0x08680+0x4*6,
		0x08680+0x4*7,
		0x08680+0x4*8,
		0x08680+0x4*9,
		0x08680+0x4*10,
		0x08680+0x4*11,
		0x08680+0x4*12,
		0x08680+0x4*13,
		0x08680+0x4*14,
		0x08680+0x4*15,
		0x08700+0x8*0,
		0x08700+0x8*1,
		0x08700+0x8*2,
		0x08700+0x8*3,
		0x08700+0x8*4,
		0x08700+0x8*5,
		0x08700+0x8*6,
		0x08700+0x8*7,
		0x08700+0x8*8,
		0x08700+0x8*9,
		0x08700+0x8*10,
		0x08700+0x8*11,
		0x08700+0x8*12,
		0x08700+0x8*13,
		0x08700+0x8*14,
		0x08700+0x8*15,
		0x08704+0x8*0,
		0x08704+0x8*1,
		0x08704+0x8*2,
		0x08704+0x8*3,
		0x08704+0x8*4,
		0x08704+0x8*5,
		0x08704+0x8*6,
		0x08704+0x8*7,
		0x08704+0x8*8,
		0x08704+0x8*9,
		0x08704+0x8*10,
		0x08704+0x8*11,
		0x08704+0x8*12,
		0x08704+0x8*13,
		0x08704+0x8*14,
		0x08704+0x8*15,
		0x05118, 0x0241C, 0x02424, 0x02428, 0x0242C, 0x08784, 0x08788
	};
void ixgbe_stats_reset(const uintptr_t addr)
{
	for (unsigned n = 0; n < sizeof(regs)/sizeof(uint32_t); n++) {
		ixgbe_reg_force_read(addr, regs[n]);
	}
}
#include <stdio.h>
#include <inttypes.h>
void ixgbe_stats_probe(const uintptr_t addr)
{
	bool changed=false;
	for (unsigned n = 0; n < sizeof(regs)/sizeof(uint32_t); n++) {
		uint32_t xxx = ixgbe_reg_read(addr, regs[n]);
		if (xxx != 0 && regs[n] !=0x405c && regs[n]!=0x4074&&regs[n]!=0x4088&&regs[n]!=0x41b0&&regs[n]!=0x41b4&&regs[n]!=0x40c0&&regs[n]!=0x40d0) {
if(regs[n]!=0x1430)			changed=true;
			printf("REG 0x%" PRIx32 " == %" PRIu32"\n", regs[n], xxx);
		}
	}
	if(changed)ixgbe_sanity_check(addr);
//	printf("checked\n");
}
