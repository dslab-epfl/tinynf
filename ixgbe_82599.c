#include <errno.h>
#include <stdbool.h>
#include <unistd.h>

#define IXGBE_REG_SWSM 0x10140
#define IXGBE_REG_SWSM_SMBI    0b01
#define IXGBE_REG_SWSM_SWESMBI 0b10

#define IXGBE_REG_SWFWSYNC 0x10160
#define IXGBE_REG_SWFWSYNC_SW 0b0000011111
#define IXGBE_REG_SWFWSYNC_FW 0b1111100000

#define IXGBE_READ_REG(addr, reg) ???
#define IXGBE_WRITE_REG(addr, reg, value) ???

#define WAIT_WITH_TIMEOUT(result_name, timeout_in_ms, condition) result_name = false; for (int i = 0; i < ((timeout_in_ms) * 20); i++) { if (condition) { result_name = true; break; } usec_delay(50); }

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
	WAIT_WITH_TIMEOUT(*out_sw_malfunction, 10 + 3000, (IXGBE_READ_REG(addr, IXGBE_REG_SWSM) & IXGBE_SWSM_SMBI) == 0);


	// "Software checks that the firmware does not use the software/firmware semaphore and then takes its control"

	// "- Software writes a 1b to the SWSM.SWESMBI bit"
	uint32_t swsm = IXGBE_READ_REG(addr, IXGBE_REG_SWSM);
	swsm |= IXGBE_REG_SWSM_SWESMBI;
	IXGBE_WRITE_REG(addr, IXGBE_REG_SWSM, swsm);

	// "- Software polls the SWSM.SWESMBI bit until it is read as 1b or time expires (recommended expiration is ~3 sec).
	//    If time has expired software assumes that the firmware malfunctioned and proceeds to the next step while ignoring the firmware bits in the SW_FW_SYNC register."
	WAIT_WITH_TIMEOUT(*out_fw_malfunction, 3000, (IXGBE_READ_REG(addr, IXGBE_REG_SWSM) & IXGBE_SWSM_SWESMBI) != 0);
}

static void ixgbe_unlock_swsm(uint64_t addr)
{
	uint32_t swsm = IXGBE_READ_REG(addr, IXGBE_REG_SWSM);
	swsm &= ~IXGBE_REG_SWSM_SMBI;
	swsm &= ~IXGBE_REG_SWSM_SWESMBI;
	IXGBE_WRITE_REG(addr, IXGBE_REG_SWSM, swsm);
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
	uint32_t sync = IXGBE_READ_REG(addr, IXGBE_REG_SWFWSYNC);
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
		sync &= IXGBE_REG_SWFWSYNC_SW;
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
			sync &= ~IXGBE_REG_SWFWSYNC_SW;
			IXGBE_WRITE_REG(addr, IXGBE_REG_SWFWSYNC, sync);
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
	uint32_t sync = IXGBE_READ_REG(addr, IXGBE_REG_SWFWSYNC);
	sync &= ~IXGBE_REG_SWFWSYNC_SW;

	// "Software releases the software/firmware semaphore by clearing the SWSM.SWESMBI and SWSM.SMBI bits"
	ixgbe_unlock_swsm(addr);

	// "Software should wait a minimum delay (recommended 5-10 ms) before trying to gain the semaphore again"
	usleep(10 * 1000);
}


int ixgbe_device_init(uint64_t addr)
{
}
