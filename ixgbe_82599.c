#include "arch.h"
#include "pci.h"

#include <stdbool.h>
#include <unistd.h>


// Fundamental constants

// TODO find reference for this
#define IXGBE_RECEIVE_QUEUES_COUNT 128
// Section 8.2.3.10.13 DCB Transmit Descriptor Plane Queue Select:
// "Field TXDQ_IDX, Bits 6:0" -> 128 pools
// TODO find a better ref...
#define IXGBE_TX_QUEUE_POOLS_COUNT 128
// Section 7.3.1 Interrupts Registers:
//	"These registers are extended to 64 bits by an additional set of two registers.
//	 EICR has an additional two registers EICR(1)... EICR(2) and so on for the EICS, EIMS, EIMC, EIAM and EITR registers."
// TODO move this to the registers section
#define IXGBE_INTERRUPT_REGISTERS_COUNT 3


// ---------
// Utilities
// ---------

// Overload macros for up to 5 args, see https://stackoverflow.com/a/11763277/3311770
#define GET_MACRO(_1, _2, _3, _4, _5, NAME, ...) NAME

// Bit tricks; note that we count bits starting from 0!
#define BIT(n) (1 << n)
#define BITS(start, end) ((end == 31 ? 0 : (0xFFFFFFFF << (end + 1))) ^ (0xFFFFFFFF << start))
#define TRAILING_ZEROES(n) __builtin_ctzll(n)

// Poll until the given condition holds, or the given timeout occurs; store whether a timeout occurred in result_name
#define WAIT_WITH_TIMEOUT(result_name, timeout_in_ms, condition) \
		result_name = true; \
		for (int i = 0; i < ((timeout_in_ms) * 20); i++) { \
			if (condition) { \
				result_name = false; \
				break; \
			} \
			usleep(50); \
		}


// ---------------------
// Operations on the NIC
// ---------------------

const int _ = 0;

// Register primitives
static uint32_t ixgbe_reg_read(uint64_t addr, uint32_t reg) { uint32_t val = *((volatile uint32_t*)((char*)addr + reg)); tn_read_barrier(); return tn_le_to_cpu(val); }
static void ixgbe_reg_write(uint64_t addr, uint32_t reg, uint32_t value) { tn_write_barrier(); *((volatile uint32_t*)((char*)addr + reg)) = tn_cpu_to_le(value); }
#define IXGBE_REG_READ3(addr, reg, idx) ixgbe_reg_read(addr, IXGBE_REG_##reg(idx))
#define IXGBE_REG_READ4(addr, reg, idx, field) ((IXGBE_REG_READ3(addr, reg, idx) & IXGBE_REG_##reg##_##field) >> TRAILING_ZEROES(IXGBE_REG_##reg##_##field))
#define IXGBE_REG_READ(...) GET_MACRO(__VA_ARGS__, _UNUSED, IXGBE_REG_READ4, IXGBE_REG_READ3, _UNUSED)(__VA_ARGS__)
#define IXGBE_REG_WRITE4(addr, reg, idx, value) ixgbe_reg_write(addr, IXGBE_REG_##reg(idx), value)
#define IXGBE_REG_WRITE5(addr, reg, idx, field, value) ixgbe_reg_write(addr, IXGBE_REG_##reg(idx), ((IXGBE_REG_READ(addr, reg, idx) & ~IXGBE_REG_##reg##_##field) | ((value << TRAILING_ZEROES(IXGBE_REG_##reg##_##field)) & IXGBE_REG_##reg##_##field)))
#define IXGBE_REG_WRITE(...) GET_MACRO(__VA_ARGS__, IXGBE_REG_WRITE5, IXGBE_REG_WRITE4, _UNUSED)(__VA_ARGS__)
#define IXGBE_REG_CLEARED(addr, reg, idx, field) (IXGBE_REG_READ(addr, reg, idx, field) == 0)
#define IXGBE_REG_CLEAR3(addr, reg, idx) IXGBE_REG_WRITE(addr, reg, idx, 0)
#define IXGBE_REG_CLEAR4(addr, reg, idx, field) IXGBE_REG_WRITE(addr, reg, idx, field, (IXGBE_REG_READ(addr, reg, idx) & ~IXGBE_REG_##reg##_##field))
#define IXGBE_REG_CLEAR(...) GET_MACRO(__VA_ARGS__, _UNUSED, IXGBE_REG_CLEAR4, IXGBE_REG_CLEAR3, _UNUSED)(__VA_ARGS__)
// TODO better name than "set", since set implies to a specific value? what's the opposite of clear?
#define IXGBE_REG_SET(addr, reg, idx, field) IXGBE_REG_WRITE(addr, reg, idx, field, (IXGBE_REG_READ(addr, reg, idx) | IXGBE_REG_##reg##_##field))

// PCI primitives (we do not write to PCI)
#define IXGBE_PCIREG_READ(addr, reg) tn_pci_read(addr, IXGBE_PCIREG_##reg)
#define IXGBE_PCIREG_CLEARED(addr, reg, field) ((IXGBE_PCIREG_READ(addr, reg) & IXGBE_PCIREG_##reg##_##field) == 0)


// -------------------------------------------------------------
// PCI registers, in alphabetical order, along with their fields
// -------------------------------------------------------------

#define IXGBE_PCIREG_DEVICESTATUS 0xAA
#define IXGBE_PCIREG_DEVICESTATUS_TRANSACTIONPENDING BIT(5)


// ---------------------------------------------------------
// Registers, in alphabetical order, along with their fields
// ---------------------------------------------------------

// TODO eliminate all "count" variables, and express them in terms of primitive counts instead (#pools, #MACs, ...)

#define IXGBE_REG_CTRL(_) 0x00000
#define IXGBE_REG_CTRL_MASTERDISABLE BIT(2)
#define IXGBE_REG_CTRL_LRST BIT(3)

// Section 8.2.3.9.1 DMA Tx TCP Max Allow Size Requests
#define IXGBE_REG_DTXMXSZRQ(_) 0x08100
#define IXGBE_REG_DTXMXSZRQ_MAXBYTESNUMREQ BITS(0,11)

// Section 8.2.3.2.1 EEPROM/Flash Control Register
#define IXGBE_REG_EEC(_) 0x10010
#define IXGBE_REG_EEC_EEPRES BIT(8)
#define IXGBE_REG_EEC_AUTORD BIT(9)

#define IXGBE_REG_EIMC(n) (n == 0 ? 0x00888 : (0x00AB0 + 4*(n-1)))
#define IXGBE_REG_EIMC_MASK BITS(0,31)

// Section 8.2.3.3.7 Flow Control Configuration
#define IXGBE_REG_FCCFG(_) 0x03D00
#define IXGBE_REG_FCCFG_TFCE BITS(3,4)

// Section 8.2.3.3.2 Flow Control Transmit Timer Value n
#define IXGBE_FCTTV_REGISTERS_COUNT 4
#define IXGBE_REG_FCTTV(n) (0x03200 + 4*n)

// Section 8.2.3.3.3 Flow Control Receive Threshold Low
#define IXGBE_FCRTL_REGISTERS_COUNT 8
#define IXGBE_REG_FCRTL(n) (0x03220 + 4*n)

// Section 8.2.3.3.4 Flow Control Receive Threshold High
#define IXGBE_FCRTH_REGISTERS_COUNT 8
#define IXGBE_REG_FCRTH(n) (0x03260 + 4*n)

// Section 8.2.3.3.5 Flow Control Refresh Threshold Value
#define IXGBE_REG_FCRTV(_) 0x032A0

// Section 8.2.3.7.1 Filter Control Register (FCTRL)
#define IXGBE_REG_FCTRL(_) 0x05080

// Section 8.2.3.7.19 Five tuple Queue Filter
#define IXGBE_FTQF_REGISTERS_COUNT 128
#define IXGBE_REG_FTQF(n) (0x0E600 + 4*n)
#define IXGBE_REG_FTQF_MASK BITS(25,29)
#define IXGBE_REG_FTQF_QUEUEENABLE BIT(31)

#define IXGBE_REG_FWSM(_) 0x10148
#define IXGBE_REG_FWSM_EXTERRIND BITS(19,24)

#define IXGBE_REG_GCREXT(_) 0x11050
#define IXGBE_REG_GCREXT_BUFFERSCLEAR BIT(30)

#define IXGBE_REG_HLREG0(_) 0x04240
#define IXGBE_REG_HLREG0_LPBK BIT(15)

// Section 8.2.3.22.34 MAC Flow Control Register
#define IXGBE_REG_MFLCN(_) 0x04294
#define IXGBE_REG_MFLCN_RFCE BIT(3)

// Section 8.2.3.7.10 MAC Pool Select Array
#define IXGBE_MPSAR_REGISTERS_COUNT 256
#define IXGBE_REG_MPSAR(n) (0x0A600 + 4*n)

// Section 8.2.3.7.7 Multicast Table Array
#define IXGBE_MTA_REGISTERS_COUNT 128
#define IXGBE_REG_MTA(n) (0x05200 + 4*n)

// Section 8.2.3.27.17 PF Unicast Table Array
#define IXGBE_PFUTA_REGISTERS_COUNT 128
#define IXGBE_REG_PFUTA(n) (0x0F400 + 4*n)

// Section 8.2.3.27.15 PF VM VLAN Pool Filter
#define IXGBE_PFVLVF_REGISTERS_COUNT 64
#define IXGBE_REG_PFVLVF(n) (0x0F100 + 4*n)

// Section 8.2.3.27.16 PF VM VLAN Pool Filter Bitmap
#define IXGBE_PFVLVFB_REGISTERS_COUNT 128
#define IXGBE_REG_PFVLVFB(n) (0x0F200 + 4*n)

// Section 8.2.3.10.6 DCB Receive Packet Plane T4 Config
#define IXGBE_RTRPT4C_REGISTERS_COUNT 8
#define IXGBE_REG_RTRPT4C(n) (0x02140 + 4*n)

// Section 8.2.3.10.13 DCB Transmit Descriptor Plane Queue Select
#define IXGBE_REG_RTTDQSEL(_) 0x04904
#define IXGBE_REG_RTTDQSEL_TXDQIDX BITS(0,6)

// Section 8.2.3.10.14 DCB Transmit Descriptor Plane T1 Config
#define IXGBE_REG_RTTDT1C(_) 0x04908

// Section 8.2.3.10.9 DCB Transmit Descriptor Plane T2 Config
#define IXGBE_RTTDT2C_REGISTERS_COUNT 8
#define IXGBE_REG_RTTDT2C(n) (0x04910 + 4*n)

// Section 8.2.3.10.10 DCB Transmit Packet Plane T2 Config
#define IXGBE_RTTPT2C_REGISTERS_COUNT 8
#define IXGBE_REG_RTTPT2C(n) (0x0CD20 + 4*n)

// Section 8.2.3.8.8 Receive DMA Control Register
#define IXGBE_REG_RDRXCTL(_) 0x02F00
#define IXGBE_REG_RDRXCTL_DMAIDONE BIT(3)

#define IXGBE_REG_RXCTRL(_) 0x03000
#define IXGBE_REG_RXCTRL_RXEN BIT(0)

#define IXGBE_REG_RXDCTL(n) (n <= 63 ? (0x01028 + 0x40*n) : (0x0D028 + 0x40*(n-64)))
#define IXGBE_REG_RXDCTL_ENABLE BIT(25)

// Section 8.2.3.8.9 Receive Packe Buffer Size
#define IXGBE_RXPBSIZE_REGISTERS_COUNT 8
#define IXGBE_REG_RXPBSIZE(n) (0x03C00 + 4*n)
#define IXGBE_REG_RXPBSIZE_SIZE BITS(10,19)

#define IXGBE_REG_STATUS(_) 0x00008
#define IXGBE_REG_STATUS_MASTERENABLE BIT(19)

#define IXGBE_REG_SWFWSYNC(_) 0x10160
#define IXGBE_REG_SWFWSYNC_SW BITS(0,4)
#define IXGBE_REG_SWFWSYNC_FW BITS(5,9)

#define IXGBE_REG_SWSM(_) 0x10140
#define IXGBE_REG_SWSM_SMBI    BIT(0)
#define IXGBE_REG_SWSM_SWESMBI BIT(1)

#define IXGBE_TXPBSIZE_REGISTERS_COUNT 8
#define IXGBE_REG_TXPBSIZE(n) (0x0CC00 + 4*n)
#define IXGBE_REG_TXPBSIZE_SIZE BITS(10,19)

// Section 8.2.3.9.16 Tx Packet Buffer Threshold
#define IXGBE_TXPBTHRESH_REGISTERS_COUNT 8
#define IXGBE_REG_TXPBTHRESH(n) (0x04950 + 4*n)
#define IXGBE_REG_TXPBTHRESH_THRESH BITS(0,9)

// ----------------------------------------------------
// Section 10.5.4 Software and Firmware Synchronization
// ----------------------------------------------------

// NOTE: For simplicity, we always gain/release control of all resources
// TODO: Do we really need this part?

// "Gaining Control of Shared Resource by Software"
static void ixgbe_lock_swsm(uint64_t addr, bool* out_sw_malfunction, bool* out_fw_malfunction)
{
	// "Software checks that the software on the other LAN function does not use the software/firmware semaphore"

	// "- Software polls the SWSM.SMBI bit until it is read as 0b or time expires (recommended expiration is ~10 ms+ expiration time used for the SWSM.SWESMBI)."
	// "- If SWSM.SMBI is found at 0b, the semaphore is taken. Note that following this read cycle hardware auto sets the bit to 1b."
	// "- If time expired, it is assumed that the software of the other function malfunctions. Software proceeds to the next steps checking SWESMBI for firmware use."
	WAIT_WITH_TIMEOUT(*out_sw_malfunction, 10 + 3000, IXGBE_REG_CLEARED(addr, SWSM, _, SMBI));


	// "Software checks that the firmware does not use the software/firmware semaphore and then takes its control"

	// "- Software writes a 1b to the SWSM.SWESMBI bit"
	IXGBE_REG_SET(addr, SWSM, _, SWESMBI);

	// "- Software polls the SWSM.SWESMBI bit until it is read as 1b or time expires (recommended expiration is ~3 sec).
	//    If time has expired software assumes that the firmware malfunctioned and proceeds to the next step while ignoring the firmware bits in the SW_FW_SYNC register."
	WAIT_WITH_TIMEOUT(*out_fw_malfunction, 3000, IXGBE_REG_CLEARED(addr, SWSM, _, SWESMBI));
}

static void ixgbe_unlock_swsm(uint64_t addr)
{
	IXGBE_REG_CLEAR(addr, SWSM, _, SWESMBI);
	IXGBE_REG_CLEAR(addr, SWSM, _, SMBI);
}

static bool ixgbe_lock_resources(uint64_t addr)
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

		if (attempts == 200) {
			return false;
		}

		if (attempts == 100) {
			IXGBE_REG_CLEAR(addr, SWFWSYNC, _, SW);
			usleep(10 * 1000);
			goto start;
		}

		usleep(10 * 1000);
		goto start;
	}
}

// "Releasing a Shared Resource by Software"
static void ixgbe_unlock_resources(uint64_t addr)
{
	// "The software takes control over the software/firmware semaphore as previously described for gaining shared resources."
	bool ignored;
	ixgbe_lock_swsm(addr, &ignored, &ignored);

	// "Software clears the bit(s) of the released resource(s) in the SW_FW_SYNC register."
	IXGBE_REG_CLEAR(addr, SWFWSYNC, _, SW);

	// "Software releases the software/firmware semaphore by clearing the SWSM.SWESMBI and SWSM.SMBI bits"
	ixgbe_unlock_swsm(addr);

	// "Software should wait a minimum delay (recommended 5-10 ms) before trying to gain the semaphore again"
	usleep(10 * 1000);
}

// ---------------------------------------------------------
// Section 4.6.7.1.2 [Dynamic] Disabling [of Receive Queues]
// ---------------------------------------------------------

static bool ixgbe_recv_disable(uint64_t addr, uint16_t queue)
{
	// "Disable the queue by clearing the RXDCTL.ENABLE bit."
	IXGBE_REG_CLEAR(addr, RXDCTL, queue, ENABLE);

	// "The 82599 clears the RXDCTL.ENABLE bit only after all pending memory accesses to the descriptor ring are done.
	//  The driver should poll this bit before releasing the memory allocated to this queue."
	// INTERPRETATION: There is no mention of what to do if the 82599 never clears the bit; 1s seems like a decent timeout
	bool timed_out;
	WAIT_WITH_TIMEOUT(timed_out, 1000 * 1000, IXGBE_REG_CLEARED(addr, RXDCTL, queue, ENABLE));
	if (timed_out) {
		return false;
	}

	// "Once the RXDCTL.ENABLE bit is cleared the driver should wait additional amount of time (~100 us) before releasing the memory allocated to this queue."
	usleep(100);

	return true;
}


// --------------------------------
// Section 5.2.5.3.2 Master Disable
// --------------------------------

// See quotes inside to understand the meaning of the return value
static bool ixgbe_device_master_disable(uint64_t addr)
{
	// "The device driver disables any reception to the Rx queues as described in Section 4.6.7.1"
	for (uint16_t queue; queue <= IXGBE_RECEIVE_QUEUES_COUNT; queue++) {
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
		usleep(20);

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

static void ixgbe_device_reset(uint64_t addr)
{
	// "Prior to issuing link reset, the driver needs to execute the master disable algorithm as defined in Section 5.2.5.3.2."
	bool master_disabled = ixgbe_device_master_disable(addr);

	// "Initiated by writing the Link Reset bit of the Device Control register (CTRL.LRST)."
	IXGBE_REG_SET(addr, CTRL, _, LRST);

	// See quotes in ixgbe_device_master_disable
	if (master_disabled) {
		usleep(2);
		IXGBE_REG_SET(addr, CTRL, _, LRST);
	}

	// Section 8.2.3.1.1 Device Control Register
	// "To ensure that a global device reset has fully completed and that the 82599 responds to subsequent accesses,
	//  programmers must wait approximately 1 ms after setting before attempting to check if the bit has cleared or to access (read or write) any other device register."
	// INTERPRETATION: It's OK to access the CTRL register itself to double-reset it as above without waiting a full second,
	//                 and thus this does not contradict the "at least 1 us" rule of the double-reset.
	usleep(1000);
}


// -------------------------------------
// Section 4.6.3 Initialization Sequence
// -------------------------------------

static void ixgbe_device_disable_interrupts(uint64_t addr)
{
	for (int n = 0; n < IXGBE_INTERRUPT_REGISTERS_COUNT; n++) {
		IXGBE_REG_CLEAR(addr, EIMC, n, MASK);
	}
}

bool ixgbe_device_init(uint64_t addr)
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
	usleep(10 * 1000);
	ixgbe_device_disable_interrupts(addr);

	//	"To enable flow control, program the FCTTV, FCRTL, FCRTH, FCRTV and FCCFG registers.
	//	 If flow control is not enabled, these registers should be written with 0x0.
	//	 If Tx flow control is enabled then Tx CRC by hardware should be enabled as well (HLREG0.TXCRCEN = 1b).
	//	 Refer to Section 3.7.7.3.2 through Section 3.7.7.3.5 for the recommended setting of the Rx packet buffer sizes and flow control thresholds.
	//	 Note that FCRTH[n].RTH fields must be set by default regardless if flow control is enabled or not.
	//	 Typically, FCRTH[n] default value should be equal to RXPBSIZE[n]-0x6000. FCRTH[n].
	//	 FCEN should be set to 0b if flow control is not enabled as all the other registers previously indicated."
	// INTERPRETATION: Sections 3.7.7.3.{2-5} are irrelevant here since we do not want flow control.
	for (int n = 0; n < IXGBE_FCTTV_REGISTERS_COUNT; n++) {
		IXGBE_REG_CLEAR(addr, FCTTV, n);
	}
	for (int n = 0; n < IXGBE_FCRTL_REGISTERS_COUNT; n++) {
		IXGBE_REG_CLEAR(addr, FCRTL, n);
	}
	for (int n = 0; n < IXGBE_FCRTH_REGISTERS_COUNT; n++) {
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
	// INTERPRETATION: There is an obvious contradiction in the stated granularities (16 vs 32 bytes). We assume 32 is correct, and it refers to the 5 reserved bottom bits.
	// INTERPRETATION: We assume that the "RXPBSIZE[n]-0x6000" calculation above refers to the RXPBSIZE in bytes (otherwise the size of FCRTH[n].RTH would be negative by default...)
	//                 Thus we set FCRTH[0] = 512 * 1024 - 0x6000 = 0x7A000, which also disables flow control since bit 31 is unset.
	IXGBE_REG_WRITE(addr, FCRTH, 0, 0x7A000);

	// "- Wait for EEPROM auto read completion."
	// INTERPRETATION: This refers to Section 8.2.3.2.1 EEPROM/Flash Control Register (EEC), Bit 9 "EEPROM Auto-Read Done"
	// INTERPRETATION: We also need to check bit 8 of the same register, "EEPROM Present", which indicates "EEPROM is present and has the correct signature field. This bit is read-only.",
	//                 since bit 9 "is also set when the EEPROM is not present or whether its signature field is not valid."
	// INTERPRETATION: We also need to check whether the EEPROM has a valid checksum, using the FWSM's register EXT_ERR_IND, where "0x00 = No error"
	// INTERPRETATION: No timeout is mentioned, so we use 1s.
	bool eeprom_timed_out;
	WAIT_WITH_TIMEOUT(eeprom_timed_out, 1000 * 1000, !IXGBE_REG_CLEARED(addr, EEC, _, AUTORD));
	if (eeprom_timed_out || IXGBE_REG_CLEARED(addr, EEC, _, EEPRES) || !IXGBE_REG_CLEARED(addr, FWSM, _, EXTERRIND)) {
		return false;
	}

	// "- Wait for DMA initialization done (RDRXCTL.DMAIDONE)."
	// INTERPRETATION: Once again, no timeout mentioned, so we use 1s
	bool dma_timed_out;
	WAIT_WITH_TIMEOUT(dma_timed_out, 1000 * 1000, !IXGBE_REG_CLEARED(addr, RDRXCTL, _, DMAIDONE));
	if (dma_timed_out) {
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
	for (int n = 0; n < IXGBE_PFUTA_REGISTERS_COUNT; n++) {
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
	for (int n = 0; n < IXGBE_PFVLVF_REGISTERS_COUNT; n++) {
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
	for (int n = 2; n < IXGBE_MPSAR_REGISTERS_COUNT; n++) {
		IXGBE_REG_CLEAR(addr, MPSAR, n);
	}

	//	"- VLAN Pool Filter Bitmap (PFVLVFB[n])."
	// INTERPRETATION: See above remark on PFVLVF
	//	Section 8.2.3.27.16: PF VM VLAN Pool Filter Bitmap
	for (int n = 0; n < IXGBE_PFVLVFB_REGISTERS_COUNT; n++) {
		IXGBE_REG_CLEAR(addr, PFVLVFB, n);
	}

	//	"Set up the Multicast Table Array (MTA) registers.
	//	 This entire table should be zeroed and only the desired multicast addresses should be permitted (by writing 0x1 to the corresponding bit location).
	//	 Set the MCSTCTRL.MFE bit if multicast filtering is required."
	for (int n = 0; n < IXGBE_MTA_REGISTERS_COUNT; n++) {
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
	//	Section 8.2.3.7.1 Filter Control Register (FCTRL):
	//		"Bit 1, Store Bad Bacpets; 0b = Do not store."
	//		"Bit 8, Multicast Promiscuous Enable. 1b = Enabled."
	//		"Bit 9, Unicast Promiscuous Enable. 1b = Enabled."
	//		"Bit 10, Broadcast Accept Mode. 1b = Accept broadcast packets to host."
	//		all other bits are "Reserved"
	// We want to receive all good packets, thus we disable bad packet store but enable promiscuous and broadcast accept.
	// TODO should not use BITS here
	IXGBE_REG_WRITE(addr, FCTRL, _, BITS(8,10));
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
	for (int n = 0; n < IXGBE_FTQF_REGISTERS_COUNT; n++) {
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
	for (int n = 1; n < IXGBE_RXPBSIZE_REGISTERS_COUNT; n++) {
		IXGBE_REG_CLEAR(addr, RXPBSIZE, 0);
	}
	//		"- TXPBSIZE[0].SIZE=0xA0, TXPBSIZE[1-7].SIZE=0x0"
	//		Section 8.2.3.9.13 Transmit Packet Buffer Size (TXPBSIZE[n]):
	//			"SIZE, Init val 0xA0"
	//			"At default setting (no DCB) only packet buffer 0 is enabled and TXPBSIZE values for TC 1-7 are meaningless."
	// INTERPRETATION: We do not need to change TXPBSIZE[0]. Let's stay on the safe side and clear TXPBSIZE[1-7] anyway.
	for (int n = 1; n < IXGBE_TXPBSIZE_REGISTERS_COUNT; n++) {
		IXGBE_REG_CLEAR(addr, TXPBSIZE, 0);
	}
	//		"- TXPBTHRESH.THRESH[0]=0xA0 — Maximum expected Tx packet length in this TC TXPBTHRESH.THRESH[1-7]=0x0"
	// INTERPRETATION: Typo in the spec; should be TXPBTHRESH[0].THRESH
	//		Section 8.2.3.9.16 Tx Packet Buffer Threshold (TXPBTHRESH):
	//			"Default values: 0x96 for TXPBSIZE0, 0x0 for TXPBSIZE1-7."
	// INTERPRETATION: Typo in the spec, this refers to TXPBTHRESH, not TXPBSIZE.
	// Thus we need to set TXPBTHRESH[0] but not TXPBTHRESH[1-7].
	IXGBE_REG_WRITE(addr, TXPBTHRESH, 0, THRESH, 0xA0);
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
	for (int n = 0; n < IXGBE_TX_QUEUE_POOLS_COUNT; n++) {
		IXGBE_REG_WRITE(addr, RTTDQSEL, _, TXDQIDX, n);
		IXGBE_REG_CLEAR(addr, RTTDT1C, _);
	}
	//		"- Clear RTTDT2C[0-7] registers"
	for (int n = 0; n < IXGBE_RTTDT2C_REGISTERS_COUNT; n++) {
		IXGBE_REG_CLEAR(addr, RTTDT2C, n);
	}
	//		"- Clear RTTPT2C[0-7] registers"
	for (int n = 0; n < IXGBE_RTTPT2C_REGISTERS_COUNT; n++) {
		IXGBE_REG_CLEAR(addr, RTTPT2C, n);
	}
	//		"- Clear RTRPT4C[0-7] registers"
	for (int n = 0; n < IXGBE_RTRPT4C_REGISTERS_COUNT; n++) {
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
