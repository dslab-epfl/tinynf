#include "net/network.h"

struct tn_net_device;

// Reuse as much code as possible, renaming some functions so we can implement our own
bool pf_init(struct tn_pci_address pci_address, struct tn_net_device** out_device);
bool pf_set_input(struct tn_net_agent* agent, struct tn_net_device* device);
bool pf_add_output(struct tn_net_agent* agent, struct tn_net_device* device);
#define tn_net_device_init pf_init
#define tn_net_agent_set_input pf_set_input
#define tn_net_agent_add_output pf_add_output
// This should be the normal ixgbe.c... if VFs supported tdwba and legacy descriptors :(
#include "pf/ixgbe.c"
#undef tn_net_device_init
#undef tn_net_agent_set_input
#undef tn_net_agent_add_output


// Section 9.4.4.3 PCIe SR-IOV Control/Status Register
#define PCIREG_SRIOV_CONTROL 0x168u
#define PCIREG_SRIOV_CONTROL_VFE BIT(0)
#define PCIREG_SRIOV_CONTROL_VFMSE BIT(3)
#define PCIREG_SRIOV_CONTROL_VFARI BIT(4)

// Section 9.4.4.4 PCIe SR-IOV Max/Total VFs Register
#define PCIREG_SRIOV_VFS 0x16C

// Section 9.4.4.5 PCIe SR-IOV Num VFs Register
#define PCIREG_SRIOV_NUMVFS 0x170u
#define PCIREG_SRIOV_NUMVFS_NUMVFS BITS(0,15)

// Section 9.4.4.10 PCIe SR-IOV BAR 0 Low Register
#define PCIREG_SRIOV_BAR0_LOW 0x184u

// Section 9.4.4.11 PCIe SR-IOV BAR 0 High Register
#define PCIREG_SRIOV_BAR0_HIGH 0x188u


// Section 8.2.3.1.3 Extended Device Control Register
#define REG_CTRLEXT_PFRSTD BIT(14)

// Section 8.2.3.4.12 PCIe Control Extended Register
#define REG_GCREXT_VT_MODE BITS(0,1)

// Section 8.2.3.5.18 General Purpose Interrupt Enable
#define REG_GPIE 0x00898u
#define REG_GPIE_VT_MODE BITS(14,15)

// Section 8.2.3.7.12 Multiple Receive Queues Command Register
#define REG_MRQC 0x0EC80u
#define REG_MRQC_MRQE BITS(0,3)

// Section 8.2.3.9.15 Multiple Transmit Queues Command Register
#define REG_MTQC 0x08120u
#define REG_MTQC_VT_ENA BIT(1)
#define REG_MTQC_NUM_TC_OR_Q BITS(2,3)

// Section 8.2.3.27.6 PF VFLR Events Clear
#define REG_PFVFLREC(n) (0x00700u + 4u*(n))

// Section 8.2.3.27.7 PF VF Receive Enable
#define REG_PFVFRE(n) (0x051E0u + 4u*(n))

// Section 8.2.3.27.8 PF VF Transmit Enable
#define REG_PFVFTE(n) (0x08110u + 4u*(n))

// Section 8.2.3.27.1 VT Control Register
#define REG_PFVTCTL 0x051B0u
#define REG_PFVTCTL_VT_ENA BIT(0)
#define REG_PFVTCTL_DIS_DEF_POOL BIT(29)
#define REG_PFVTCTL_RPL_EN BIT(30)

// Section 8.2.3.27.14 PF VM L2 Control Register
#define REG_PFVML2FLT(n) (0x0F000u + 4u*n)
#define REG_PFVML2FLT_AUPE BIT(24)
#define REG_PFVML2FLT_BAM BIT(27)
#define REG_PFVML2FLT_MPE BIT(28)

// Section 8.2.3.7.9 Receive Address High
#define REG_RAH(n) (0x0A204u + 8u*(n))

// Section 8.2.3.7.8 Receive Address Low
#define REG_RAL(n) (0x0A200u + 8u*(n))

// Section 8.2.3.7.6 Receive Filter Control Register
#define REG_RFCTL 0x05008u
// INTERPRETATION-TYPO: Bits 0:5 are marked reserved then bit 5 is RSC_DIS, so it's actually 0:4 that are reserved
#define REG_RFCTL_RSC_DIS BIT(5)

// Section 8.2.3.10.2 DCB Transmit Descriptor Plane Control and Status
#define REG_RTTDCS_VMPAC BIT(1)
#define REG_RTTDCS_BPBFSM BIT(23)

// Section 8.2.3.10.14 DCB Transmit Descriptor Plane T1 Config
#define REG_RTTDT1C_CRQ BITS(0,13)

// Section 8.2.3.1.2 Device Status Register
#define REG_STATUS_NUMVFS BITS(10,17)

// Section 8.3.5.2.1 VF Extended Interrupt Cause
#define REG_VFEICR 0x00100u
#define REG_VFEICR_MSIX BITS(0,2)

// Section 8.3.5.2.4 VF Extended Interrupt Mask Clear
#define REG_VFEIMC 0x0010Cu
#define REG_VFEIMC_MSIX BITS(0,2)


// 16 KB
#define IXGBE_VF_SIZE 16u * 1024u
// Max number of supported VFs
#define IXGBE_VF_COUNT 64u


static bool get_pcie_extended_address(struct tn_pci_address pci_address, uint16_t reg, volatile uint32_t** out_addr)
{
	// HUGE UNSAFE BAD TERRIBLE NO GOOD HACK
	// The proper way to do this is to find the ACPI RSDP, then use it to find the ACPI XSDT,
	// then use it to find the ACPI MCFG, then loop through sub-tables to find the base address corresponding to the bus,
	// then use memory-mapped access to the enhanced config space (ECAM).
	// So instead we just lookup MMCONFIG in `sudo cat /proc/iomem` and use that; it will only work on this machine but oh well.
	uintptr_t ecam_addr = 0xC0000000;
	void* ecam_virt_addr;
	if (!tn_mem_phys_to_virt(ecam_addr, 256 * 1024 * 1024, &ecam_virt_addr)) { // ECAM is 256 MB max
		TN_DEBUG("Could not phys-to-virt the ECAM base addr");
		return false;
	}
	uintptr_t offset = ((uintptr_t) pci_address.bus << 20) | ((uintptr_t) pci_address.device << 15) | ((uintptr_t) pci_address.function << 12) | (uintptr_t) reg;
	*out_addr = (volatile uint32_t*) ((uint8_t*) ecam_virt_addr + offset);
	return true;
}

static uint32_t read_pcie_extended_reg(struct tn_pci_address pci_address, uint16_t reg)
{
	volatile uint32_t* mmapped_addr;
	if (get_pcie_extended_address(pci_address, reg, &mmapped_addr)) {
		return *mmapped_addr;
	}
	return 0xFFFFFFFFu; // like other bad PCI reads

}

static void write_pcie_extended_field(struct tn_pci_address pci_address, uint16_t reg, uint32_t field, uint32_t value)
{
	volatile uint32_t* mmapped_addr;
	if (get_pcie_extended_address(pci_address, reg, &mmapped_addr)) {
		uint32_t old_value = *mmapped_addr;
		uint32_t new_value = (old_value & ~field) | (value << find_first_set(field));
		*mmapped_addr = new_value;
	}
	// else ignore, like other bad PCI writes

}

static bool vf_get_virtual_bar(struct tn_net_device* device, uint64_t index, void** out_addr)
{
	// See HACK after calling pf_init
	struct tn_pci_address device_pci_addr = *((struct tn_pci_address*)(device + 1));

	// See Section 8.3.5 for a quick explanation
	uint32_t bar0low = read_pcie_extended_reg(device_pci_addr, PCIREG_SRIOV_BAR0_LOW);
	// Sanity check: a 64-bit BAR must have bit 2 of low as 1 and bit 1 of low as 0 as per Table 9-4 Base Address Registers' Fields
	if ((bar0low & BIT(2)) == 0 || (bar0low & BIT(1)) != 0) {
		TN_DEBUG("VF BAR0 is not a 64-bit BAR");
		return false;
	}
	uint32_t bar0high = read_pcie_extended_reg(device_pci_addr, PCIREG_SRIOV_BAR0_HIGH);
	uintptr_t bar0 = ((uint64_t) bar0high << 32) | (bar0low & ~BITS(0,3));
	if (!tn_mem_phys_to_virt(bar0 + index * IXGBE_VF_SIZE, IXGBE_VF_SIZE, out_addr)) {
		TN_DEBUG("Could not phys-to-virt VF BAR.");
		return false;
	}

	return true;
}


bool tn_net_device_init(struct tn_pci_address pci_address, struct tn_net_device** out_device)
{
// Step 1: PCIe configuration, done before PF init

	// Sanity check: there's a register with the number of VFs, it should be 64 in the upper part and 64 in the lower part
	if (read_pcie_extended_reg(pci_address, PCIREG_SRIOV_VFS) != 0x00400040u) {
		TN_DEBUG("Bad SRIOV_VFS: %" PRIx32, read_pcie_extended_reg(pci_address, PCIREG_SRIOV_VFS));
		return false;
	}
	// First set the number of VFs
	write_pcie_extended_field(pci_address, PCIREG_SRIOV_NUMVFS, PCIREG_SRIOV_NUMVFS_NUMVFS, IXGBE_VF_COUNT);
	// Then enable VFs in PCIREG_SRIOV_CONTROL, which has a separate bit for allowing them to use memory.
	// This has to be done _after_ setting the number of VFs, despite the data sheet not mentioning this.
	write_pcie_extended_field(pci_address, PCIREG_SRIOV_CONTROL, PCIREG_SRIOV_CONTROL_VFE, 1);
	write_pcie_extended_field(pci_address, PCIREG_SRIOV_CONTROL, PCIREG_SRIOV_CONTROL_VFMSE, 1);
	// Not sure why but addressing VFs in non-ARI mode sometimes fails
	write_pcie_extended_field(pci_address, PCIREG_SRIOV_CONTROL, PCIREG_SRIOV_CONTROL_VFARI, 1);

// Step 2: PF init for PF, including overriding some registers with IOV-specific values

	if (!pf_init(pci_address, out_device)) {
		TN_DEBUG("PF could not init");
		return false;
	}
	struct tn_net_device* device = *out_device;
	// HACK: We need the PCI address for later, let's store it past the device, since it's allocated as a huge page so there's plenty of space
	*((struct tn_pci_address*)(device + 1)) = pci_address;

	// Sanity check: The STATUS register (in memory space, not PCI) mirrors NUMVFS
	if (reg_read_field(device->addr, REG_STATUS, REG_STATUS_NUMVFS) != IXGBE_VF_COUNT) {
		TN_DEBUG("Did not properly write to NUMVFS");
		return false;
	}

	// 4.6.7.2.1 casually tells us this must be done
	reg_set_field(device->addr, REG_RFCTL, REG_RFCTL_RSC_DIS);

	// Diff between 4.6.11.3.3 (DCB-Off, VT-On) and 4.6.11.3.4 (DCB-Off, VT-Off):
	// "Set MRQE to 1xxxb, with the three least significant bits set according to the number of VFs and RSS mode"
	//   Section 8.2.3.7.12 Multiple Receive Queues Command Register - MRQC: "1000b = Virtualization only - 64 pools, no RSS, each pool allocated 2 queues."
	reg_write_field(device->addr, REG_MRQC, REG_MRQC_MRQE, 8);

	// "Clear RT_Ena bit and set the VT_Ena bit in the MTQC register."
	//     Section 7.2.1.2.1 Tx Queues Assignment: "Programming MTQC must be done only during the init phase while software must also set RTTDCS.ARBDIS before configuring MTQC and then clear RTTDCS.ARBDIS afterwards."
	reg_set_field(device->addr, REG_RTTDCS, REG_RTTDCS_ARBDIS);
	reg_set_field(device->addr, REG_MTQC, REG_MTQC_VT_ENA);
	// "Set MTQC.NUM_TC_OR_Q according to the number of VFs enabled"
	//   Section 8.2.3.9.15 Multiple Transmit Queues Command Register states that NUM_TC_OR_Q should be 01 for 64 VMs
	reg_write_field(device->addr, REG_MTQC, REG_MTQC_NUM_TC_OR_Q, 1);
	reg_clear_field(device->addr, REG_RTTDCS, REG_RTTDCS_ARBDIS);

	// "Set PFVTCTL.VT_Ena (as the MRQC.VT_Ena)"
	reg_set_field(device->addr, REG_PFVTCTL, REG_PFVTCTL_VT_ENA);

	// "Tx Descriptor Plane Control and Status (RTTDCS), bits: TDPAC=0b, VMPAC=1b, TDRM=0b, BDPM=1b, BPBFSM=0b"
	reg_set_field(device->addr, REG_RTTDCS, REG_RTTDCS_VMPAC);
	reg_clear_field(device->addr, REG_RTTDCS, REG_RTTDCS_BPBFSM);

	// Not written anywhere except in these registers' descriptions...
	reg_write_field(device->addr, REG_GCREXT, REG_GCREXT_VT_MODE, 3);
	reg_write_field(device->addr, REG_GPIE, REG_GPIE_VT_MODE, 3);

// Step 3: VF init, except RX and TX

	for (uint8_t vf_index = 0; vf_index < IXGBE_VF_COUNT; vf_index++) {
		// Section 7.10.2.6.1.1 explains VF PCI addressing
		struct tn_pci_address vf_pci_addr = {
			.bus = pci_address.bus,
			.device = 16 | (vf_index >> 2),
			.function = ((vf_index & 3) << 1) | pci_address.function
		};
		// This bit persists across resets but not reboots; do not remove this line because the code "still works without it"!
		write_pcie_extended_field(vf_pci_addr, PCIREG_COMMAND, PCIREG_COMMAND_BUS_MASTER_ENABLE, 1);

		void* vf_addr;
		if (!vf_get_virtual_bar(device, vf_index, &vf_addr)) {
			TN_DEBUG("Could not get VF BAR during init");
			return false;
		}

		// Now we need to reset the VF
		reg_set_field(vf_addr, REG_CTRL, REG_CTRL_RST);
		tn_sleep_us(10 * 1000);

		// Clear the corresponding bit in the PF VFLR clear register, just in case
		reg_clear_field(device->addr, REG_PFVFLREC(vf_index / 32), BIT(vf_index % 32));

		// Disable and clear interrupts
		reg_set_field(vf_addr, REG_VFEIMC, REG_VFEIMC_MSIX);
		reg_set_field(vf_addr, REG_VFEICR, REG_VFEICR_MSIX);
	}

// Step 4: PF init for VFs

	// A few more things mentioned in sections 4.6.10.*:
	// "Configure PFVTCTL to define the default pool."
	reg_set_field(device->addr, REG_PFVTCTL, REG_PFVTCTL_DIS_DEF_POOL);
	// "Enable replication via PFVTCTL.Rpl_En."
	reg_set_field(device->addr, REG_PFVTCTL, REG_PFVTCTL_RPL_EN);

	// "Tx Descriptor Plane T1 Config (RTTDT1C) per pool, via setting RTTDQSEL first for the pool index.
	//  Clear RTTDT1C for other queues. Note that the RTTDT1C for queue zero must always be initialized."
	// PF init already cleared the queues
	for (uint8_t n = 0; n < IXGBE_VF_COUNT; n++) {
		reg_write(device->addr, REG_RTTDQSEL, n);
		reg_set_field(device->addr, REG_RTTDT1C, REG_RTTDT1C_CRQ);
	}

	// "Associate the unicast Ethernet MAC address of the VM by enabling the pool in the MPSAR registers."
	// One address per VF
	for (uint32_t n = 0; n < IXGBE_VF_COUNT; n++) {
		if (n < 32) {
			reg_write(device->addr, REG_MPSAR(2 * n), BIT(n));
		} else {
			reg_write(device->addr, REG_MPSAR(2 * n + 1), BIT(n - 32));
		}
	}
	// Also we should set RAL/RAH
	// (note that the data sheet seems to confuse RAL/RAH with MPSAR sometimes...)
	// silly hack to match our benchmark scripts
	// TODO document this at least, cause it probably won't work if wires aren't crossed
	static bool first_mac = true;
	uint32_t rah_val = first_mac ? 0 : 0xFF00u;
	first_mac = false;
	for (uint8_t n = 0; n < IXGBE_VF_COUNT; n++) {
		reg_write(device->addr, REG_RAL(n), n);
		reg_write(device->addr, REG_RAH(n), rah_val | BIT(31)); // bit 31 is "address valid"
	}

	// "Define whether this VM should get all multicast/broadcast packets in the same VLAN via PFVML2FLT.MPE and PFVML2FLT.BAM, and whether it should accept untagged packets via PFVML2FLT.AUPE."
	// We don't want broadcast but we do want untagged packets for all
	for (uint8_t n = 0; n < IXGBE_VF_COUNT; n++) {
		reg_set_field(device->addr, REG_PFVML2FLT(n), REG_PFVML2FLT_AUPE);
	}

	// Open the receive and transmit gates now, simpler
	for (uint8_t n = 0; n < 2; n++) {
		reg_write(device->addr, REG_PFVFRE(n), 0xFFFFFFFFu);
		reg_write(device->addr, REG_PFVFTE(n), 0xFFFFFFFFu);
	}

	// "After all the common parameters are set, the PF driver should set all the VFMailbox[n].RSTD bits by setting CTRL_EXT.PFRSTD."
	reg_set_field(device->addr, REG_CTRLEXT, REG_CTRLEXT_PFRSTD);

	return true;
}

bool tn_net_agent_set_input(struct tn_net_agent* agent, struct tn_net_device* device)
{
	// This needs to be done on the PF, not the VFs
	if (!device->rx_enabled) {
		// see the PF file for comments
		reg_set_field(device->addr, REG_SECRXCTRL, REG_SECRXCTRL_RX_DIS);
		IF_AFTER_TIMEOUT(1000 * 1000, reg_is_field_cleared(device->addr, REG_SECRXSTAT, REG_SECRXSTAT_SECRX_RDY)) {
			TN_DEBUG("SECRXSTAT.SECRXRDY timed out, cannot start device");
			return false;
		}
		reg_set_field(device->addr, REG_RXCTRL, REG_RXCTRL_RXEN);
		reg_clear_field(device->addr, REG_SECRXCTRL, REG_SECRXCTRL_RX_DIS);
		reg_set_field(device->addr, REG_CTRLEXT, REG_CTRLEXT_NSDIS);
		device->rx_enabled = true;
	}

	// HACK: We store the next VF index in the device padding (which is zero-initialized)
	uint8_t vf_index = device->_padding[0];
	if (vf_index == IXGBE_VF_COUNT) {
		TN_DEBUG("No VF available for input");
		return false;
	}

	void* vf_addr;
	if (!vf_get_virtual_bar(device, vf_index, &vf_addr)) {
		TN_DEBUG("Could not get VF BAR.");
		return false;
	}

	// Fake device!
	// The address is the VF one, since RX queue registers are at the same offset on PFs and VFs
	// We pretend rx_enabled is true cause we did this above to the PF, not VF
	struct tn_net_device vf_device = {
		.addr = vf_addr,
		.rx_enabled = true,
		.tx_enabled = true // irrelevant
	};
	if (!pf_set_input(agent, &vf_device)) {
		TN_DEBUG("Could not set input using the VF device");
		return false;
	}

	TN_INFO("Using VF %" PRIu8 " for input", vf_index);
	// see HACK above
	device->_padding[0] = vf_index + 1;
	return true;
}

bool tn_net_agent_add_output(struct tn_net_agent* agent, struct tn_net_device* device)
{
	// This needs to be done on the PF, not the VF
	if (!device->tx_enabled) {
		reg_set_field(device->addr, REG_DMATXCTL, REG_DMATXCTL_TE);
		device->rx_enabled = true;
	}

	// HACK: We store the next VF index in the device padding (which is zero-initialized)
	uint8_t vf_index = device->_padding[1];
	if (vf_index == IXGBE_VF_COUNT) {
		TN_DEBUG("No VF available for output");
		return false;
	}

	void* vf_addr;
	if (!vf_get_virtual_bar(device, vf_index, &vf_addr)) {
		TN_DEBUG("Could not get VF BAR.");
		return false;
	}

	// Fake device!
	// The address is the VF one minus 0x4000, since TX queue registers are at 0x20xx in VFs but 0x60xx in PFs
	// We pretend tx_enabled is true since we do it ourselves to the PF, not VF, above
	struct tn_net_device vf_device = {
		.addr = (uint8_t*) vf_addr - 0x4000u,
		.rx_enabled = true, // irrelevant
		.tx_enabled = true // don't touch DMATXCTL
	};
	if (!pf_add_output(agent, &vf_device)) {
		TN_DEBUG("Could not set output using the VF device");
		return false;
	}

	TN_INFO("Using VF %" PRIu8 " for output", vf_index);
	// see HACK above
	device->_padding[1] = vf_index + 1;
	return true;
}
