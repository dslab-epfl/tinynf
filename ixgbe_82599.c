#include <errno.h>
#include <stdbool.h>
#include <unistd.h>


// Fundamental constants

// TODO find reference for this
#define IXGBE_RECEIVE_QUEUES_COUNT 128
// Section 7.3.1 Interrupts Registers:
//	"These registers are extended to 64 bits by an additional set of two registers.
//	 EICR has an additional two registers EICR(1)... EICR(2) and so on for the EICS, EIMS, EIMC, EIAM and EITR registers."
#define IXGBE_INTERRUPT_REGISTERS_COUNT 3


// Utilities

// Refer to a bit, or an inclusive range of bits; zero-based indexes!
#define BIT(n) (1 << (n + 1))
#define BITS(start, end) (0xFFFFFFFF << (end + 1)) ^ (0xFFFFFFFF << start)
#define TRAILING_ZEROES(n) __builtin_ctzll(n)

// Poll until the given condition holds, or the given timeout occurs; store whether a timeout occurred in result_name
#define WAIT_WITH_TIMEOUT(result_name, timeout_in_ms, condition) \
		result_name = true; \
		for (int i = 0; i < ((timeout_in_ms) * 20); i++) { \
			if (condition) { \
				result_name = false; \
				break; \
			} \
			usec_delay(50); \
		}


// Operations on the NIC

// Macros that assume _READ and _WRITE primitives for the given type
// TODO reconsider whether we need this abomination
#define _IXGBE_WRITE(type, addr, reg, field, value) \
		IXGBE_##type_WRITE(addr, IXGBE_##type_##reg, \
				((IXGBE_##type_READ(addr, IXGBE_##type_##reg) & ~IXGBE_##type_##reg_##field) | ((value << TRAILING_ZEROES(IXGBE_##type_##reg_##field)) & IXGBE_##type_##reg_##field)))
#define _IXGBE_CLEARED(type, addr, reg, field) (IXGBE_##type_READ(addr, IXGBE_##type_##reg) & IXGBE_REG_##reg_##field) == 0
#define _IXGBE_SET(type, addr, reg, field) IXGBE_##type_WRITE(addr, IXGBE_##type_##reg, (IXGBE_##type_READ(addr, IXGBE_##type_##reg) | IXGBE_##type_##reg_##field))
#define _IXGBE_CLEAR(type, addr, reg, field) IXGBE_##type_WRITE(addr, IXGBE_##type_##reg, (IXGBE_##type_READ(addr, IXGBE_##type_##reg) & ~IXGBE_##type_##reg_##field))

#define IXGBE_REG_READ(addr, reg) ???
#define IXGBE_REG_WRITE(addr, reg, value) ???
#define IXGBE_REG_WRITE(addr, reg, field, value) _IXGBE_WRITE(type, addr, reg, field, value)
#define IXGBE_REG_CLEARED(addr, reg, field) _IXGBE_CLEARED(REG, addr, reg, field)
#define IXGBE_REG_SET(addr, reg, field) _IXGBE_SET(REG, addr, reg, field)
#define IXGBE_REG_CLEAR(addr, reg, field) _IXGBE_CLEAR(REG, addr, reg, field)
#define IXGBE_REG_CLEAR(addr, reg) IXGBE_REG_CLEAR(addr, reg, 0xFFFFFFFF)

#define IXGBE_PCIREG_READ(addr, reg) ???
#define IXGBE_PCIREG_WRITE(addr, reg, value) ???
#define IXGBE_PCIREG_CLEARED(addr, reg, field) _IXGBE_CLEARED(PCIREG, addr, reg, field)
#define IXGBE_PCIREG_SET(addr, reg, field) _IXGBE_SET(PCIREG, addr, reg, field)
#define IXGBE_PCIREG_CLEAR(addr, reg, field) _IXGBE_CLEAR(PCIREG, addr, reg, field)


// -------------------------------------------------------------
// PCI registers, in alphabetical order, along with their fields
// -------------------------------------------------------------

#define IXGBE_PCIREG_DEVICESTATUS 0xAA
#define IXGBE_PCIREG_DEVICESTATUS_TRANSACTIONPENDING BIT(5)


// -------------------------------------------------------------
// Registers, in alphabetical order, along with their sub-values
// -------------------------------------------------------------

#define IXGBE_REG_CTRL 0x00000
#define IXGBE_REG_CTRL_MASTERDISABLE BIT(2)
#define IXGBE_REG_CTRL_LRST BIT(3)

// Section 8.2.3.2.1 EEPROM/Flash Control Register
#define IXGBE_REG_EEC 0x10010
#define IXGBE_REG_EEC_EEPRES BIT(8)
#define IXGBE_REG_EEC_AUTORD BIT(9)

#define IXGBE_REG_EIMC(n) (n == 0 ? 0x00888 : (0x00AB0 + 4*(n-1)))
#define IXGBE_REG_EIMC_MASK BITS(0,31)

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
#define IXGBE_REG_FCRTV 0x032A0

// Section 8.2.3.3.7 Flow Control Configuration
#define IXGBE_REG_FCCFG 0x03D00

#define IXGBE_REG_FWSM 0x10148
#define IXGBE_REG_FWSM_EXTERRIND BITS(19,24)

#define IXGBE_REG_GCREXT 0x11050
#define IXGBE_REG_GCREXT_BUFFERSCLEAR BIT(30)

#define IXGBE_REG_HLREG0 0x04240
#define IXGBE_REG_HLREG0_LPBK BIT(15)

#define IXGBE_REG_SWFWSYNC 0x10160
#define IXGBE_REG_SWFWSYNC_SW BITS(0,4)
#define IXGBE_REG_SWFWSYNC_FW BITS(5,9)

#define IXGBE_REG_SWSM 0x10140
#define IXGBE_REG_SWSM_SMBI    BIT(0)
#define IXGBE_REG_SWSM_SWESMBI BIT(1)

// Section 8.2.3.8.8 Receive DMA Control Register
#define IXGBE_REG_RDRXCTL 0x02F00
#define IXGBE_REG_RDRXCTL_DMAIDONE BIT(3)

#define IXGBE_REG_RXCTRL 0x03000
#define IXGBE_REG_RXCTRL_RXEN BIT(0)

#define IXGBE_REG_RXDCTL(queue) (queue <= 63 ? (0x01028 + 0x40*queue) : (0x0D028 + 0x40*(queue-64)))
#define IXGBE_REG_RXDCTL_ENABLE BIT(25)

#define IXGBE_REG_STATUS 0x00008
#define IXGBE_REG_STATUS_MASTERENABLE BIT(19)

// ----------------------------------------------------
// Section 10.5.4 Software and Firmware Synchronization
// ----------------------------------------------------

// NOTE: For simplicity, we always gain/release control of all resources

// "Gaining Control of Shared Resource by Software"
static void ixgbe_lock_swsm(uint64_t addr, bool* out_sw_malfunction, bool* out_fw_malfunction)
{
	// "Software checks that the software on the other LAN function does not use the software/firmware semaphore"

	// "- Software polls the SWSM.SMBI bit until it is read as 0b or time expires (recommended expiration is ~10 ms+ expiration time used for the SWSM.SWESMBI)."
	// "- If SWSM.SMBI is found at 0b, the semaphore is taken. Note that following this read cycle hardware auto sets the bit to 1b."
	// "- If time expired, it is assumed that the software of the other function malfunctions. Software proceeds to the next steps checking SWESMBI for firmware use."
	WAIT_WITH_TIMEOUT(*out_sw_malfunction, 10 + 3000, IXGBE_REG_CLEARED(SWSM, SMBI));


	// "Software checks that the firmware does not use the software/firmware semaphore and then takes its control"

	// "- Software writes a 1b to the SWSM.SWESMBI bit"
	IXGBE_REG_SET(SWSM, SWESMBI);

	// "- Software polls the SWSM.SWESMBI bit until it is read as 1b or time expires (recommended expiration is ~3 sec).
	//    If time has expired software assumes that the firmware malfunctioned and proceeds to the next step while ignoring the firmware bits in the SW_FW_SYNC register."
	WAIT_WITH_TIMEOUT(*out_fw_malfunction, 3000, IXGBE_REG_CLEARED(SWSM, SWESMBI));
}

static void ixgbe_unlock_swsm(uint64_t addr)
{
	IXGBE_REG_CLEAR(SWSM, SWESMBI);
	IXGBE_REG_CLEAR(SWSM, SMBI);
}

static bool ixgbe_lock_resources(uint64_t addr)
{
	uint32_t attempts = 0;

start:
	bool sw_malfunction;
	bool fw_malfunction;
	ixgbe_lock_swsm(addr, &sw_malfunction, &fw_malfunction);

	// "Software takes control of the requested resource(s)"

	// "- Software reads the firmware and software bit(s) of the requested resource(s) in the SW_FW_SYNC register."
	uint32_t sync = IXGBE_REG_READ(addr, IXGBE_REG_SWFWSYNC);
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
		IXGBE_WRITE_REG(addr, IXGBE_REG_SWFWSYNC, sync);

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
			IXGBE_REG_CLEAR(addr, SWFWSYNC, SW);
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
	ixgbe_lock_swfw(addr, &ignored, &ignored);

	// "Software clears the bit(s) of the released resource(s) in the SW_FW_SYNC register."
	IXGBE_REG_CLEAR(SWFWSYNC, SW);

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
	IXGBE_REG_CLEAR(addr, RXDCTL(queue), ENABLE);

	// "The 82599 clears the RXDCTL.ENABLE bit only after all pending memory accesses to the descriptor ring are done.
	//  The driver should poll this bit before releasing the memory allocated to this queue."
	// INTERPRETATION: There is no mention of what to do if the 82599 never clears the bit; 1s seems like a decent timeout
	bool timed_out;
	WAIT_WITH_TIMEOUT(timed_out, 1000 * 1000, IXGBE_REG_CLEARED(addr, RXDCTL(queue), ENABLE));
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
	IXGBE_REG_SET(CTRL, MASTERDISABLE);

	// "The 82599 then blocks new requests and proceeds to issue any pending requests by this function.
	//  The driver then reads the change made to the PCIe Master Disable bit and then polls the PCIe Master Enable Status bit.
	//  Once the bit is cleared, it is guaranteed that no requests are pending from this function."
	// INTERPRETATION: The next sentence refers to "a given time"; let's say 1 second should be plenty...
	bool timed_out;
	WAIT_WITH_TIMEOUT(timed_out, 1000 * 1000, IXGBE_REG_CLEARED(addr, STATUS, MASTERENABLE));

	// "The driver might time out if the PCIe Master Enable Status bit is not cleared within a given time."
	if (timed_out) {
		// "In these cases, the driver should check that the Transaction Pending bit (bit 5) in the Device Status register in the PCI config space is clear before proceeding.
		//  In such cases the driver might need to initiate two consecutive software resets with a larger delay than 1 us between the two of them."
		uint32_t devstatus = IXGBE_READ_PCIREG(addr, IXGBE_PCIREG_DEVICESTATUS);
		if (!IXGBE_PCIREG_CLEARED(addr, DEVICESTATUS, TRANSACTIONPENDING)) {
			return false;
		}

		// "In the above situation, the data path must be flushed before the software resets the 82599.
		//  The recommended method to flush the transmit data path is as follows:"
		// "- Inhibit data transmission by setting the HLREG0.LPBK bit and clearing the RXCTRL.RXEN bit.
		//    This configuration avoids transmission even if flow control or link down events are resumed."
		IXGBE_REG_SET(HLREG0, LPBK);
		IXGBE_REG_CLEAR(RXCTRL, RXEN);

		// "- Set the GCR_EXT.Buffers_Clear_Func bit for 20 microseconds to flush internal buffers."
		IXGBE_REG_SET(GCREXT, BUFFERSCLEAR);
		usleep(20);

		// "- Clear the HLREG0.LPBK bit and the GCR_EXT.Buffers_Clear_Func"
		IXGBE_REG_CLEAR(HLREG0, LPBK);
		IXGBE_REG_CLEAR(GCREXT, BUFFERSCLEAR);

		// "- It is now safe to issue a software reset."
	}
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
	IXGBE_REG_SET(CTRL, LRST);

	// See quotes in ixgbe_device_master_disable
	if (master_disabled) {
		usleep(2);
		IXGBE_REG_SET(CTRL, LRST);
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
		IXGBE_REG_CLEAR(addr, EIMC(n), MASK);
	}
}

static bool ixgbe_device_init(uint64_t addr)
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
		IXGBE_REG_CLEAR(addr, FCTTV(n));
	}
	for (int n = 0; n < IXGBE_FCRTL_REGISTERS_COUNT; n++) {
		IXGBE_REG_CLEAR(addr, FCRTL(n));
	}
	for (int n = 0; n < IXGBE_FCRTH_REGISTERS_COUNT; n++) {
		IXGBE_REG_CLEAR(addr, FCRTH(n));
	}
	IXGBE_REG_CLEAR(addr, FCRTV);
	IXGBE_REG_CLEAR(addr, FCCFG);
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
	IXGBE_REG_WRITE(addr, FCRTH(0), 0x7A000);

	// "- Wait for EEPROM auto read completion."
	// INTERPRETATION: This refers to Section 8.2.3.2.1 EEPROM/Flash Control Register (EEC), Bit 9 "EEPROM Auto-Read Done"
	// INTERPRETATION: We also need to check bit 8 of the same register, "EEPROM Present", which indicates "EEPROM is present and has the correct signature field. This bit is read-only.",
	//                 since bit 9 "is also set when the EEPROM is not present or whether its signature field is not valid."
	// INTERPRETATION: We also need to check whether the EEPROM has a valid checksum, using the FWSM's register EXT_ERR_IND, where "0x00 = No error"
	// INTERPRETATION: No timeout is mentioned, so we use 1s.
	bool eeprom_timed_out;
	WAIT_WITH_TIMEOUT(eeprom_timed_out, 1000 * 1000, !IXGBE_REG_CLEARED(addr, EEC, AUTORD));
	if (eeprom_timed_out || IXGBE_REG_CLEARED(addr, EEC, EEPRES) || !IXGBE_REG_CLEARED(FWSM, EXTERRIND)) {
		return false;
	}

	// "- Wait for DMA initialization done (RDRXCTL.DMAIDONE)."
	// INTERPRETATION: Once again, no timeout mentioned, so we use 1s
	bool dma_timed_out;
	WAIT_WITH_TIMEOUT(dma_timed_out, 1000 * 1000, !IXGBE_REG_CLEARED(addr, RDRXCTL, DMAIDONE));
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
	???

	// "- Initialize transmit (see Section 4.6.8)."
	???

	// "- Enable interrupts (see Section 4.6.3.1)."
	// Section 4.6.3.1 Interrupts During Initialization "After initialization completes, a typical driver enables the desired interrupts by writing to the IMS register."
	// ASSUMPTION: We do not want interrupts.
	// INTERPRETATION: We don't need to do anything here.
}
