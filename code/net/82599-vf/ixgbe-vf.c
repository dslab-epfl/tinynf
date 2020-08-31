#include "net/network.h"

// Reuse as much code as possible, renaming some functions so we can implement our own

#define tn_net_device_init pf_init
#define tn_net_device_set_promiscuous pf_set_promiscuous
#define tn_net_agent_set_input pf_set_input
#include "net/82599/ixgbe.c"
#undef tn_net_device_init
#undef tn_net_device_set_promiscuous
#undef tn_net_agent_set_input


#include "util/log.h"


// Section 9.4.4.3 PCIe SR-IOV Control/Status Register
#define PCIREG_SRIOV_CONTROL 0x168u
#define PCIREG_SRIOV_CONTROL_VFE BIT(0)
#define PCIREG_SRIOV_CONTROL_VFMSE BIT(3)

// Section 9.4.4.5 PCIe SR-IOV Num VFs Register
#define PCIREG_SRIOV_NUMVFS 0x170u
#define PCIREG_SRIOV_NUMVFS_NUMVFS BITS(0,15)

// Section 9.4.4.10 PCIe SR-IOV BAR 0 Low Register
#define PCIREG_SRIOV_BAR0_LOW 0x184u

// Section 9.4.4.11 PCIe SR-IOV BAR 0 High Register
#define PCIREG_SRIOV_BAR0_HIGH 0x188u


// Section 8.2.3.1.3 Extended Device Control Register
#define REG_CTRLEXT_PFRSTD BIT(14)

// Section 8.2.3.7.12 Multiple Receive Queues Command Register
#define REG_MRQC 0x0EC80u
#define REG_MRQC_MRQE BITS(0,3)

// Section 8.2.3.9.15 Multiple Transmit Queues Command Register
#define REG_MTQC 0x08120u
#define REG_MTQC_VT_ENA BIT(1)
#define REG_MTQC_NUM_TC_OR_Q BITS(2,3)

// Section 8.2.3.27.14 PF VM L2 Control Register
#define REG_PFVML2FLT(n) (0x0F000u + 4u*n)
#define REG_PFVML2FLT_AUPE BIT(24)
#define REG_PFVML2FLT_BAM BIT(27)
#define REG_PFVML2FLT_MPE BIT(28)

// Section 8.2.3.27.7 PF VF Receive Enable
#define REG_PFVFRE(n) (0x051E0u + 4u*n)

// Section 8.2.3.27.8 PF VF Transmit Enable
#define REG_PFVFTE(n) (0x08110u + 4u*n)


// 16 KB
#define IXGBE_VF_SIZE 16u * 1024u



// Write 'value' to the field 'field' (from the PCIREG_... #defines) of register 'reg' on the PCI device at address 'addr'
static void pcireg_write_field(struct tn_pci_address address, uint16_t reg, uint32_t field, uint32_t field_value)
{
	uint32_t old_value = tn_pci_read(address, reg);
	uint32_t shift = find_first_set(field);
	uint32_t new_value = (old_value & ~field) | (field_value << shift);
	tn_pci_write(address, reg, new_value);
}



bool tn_net_device_init(struct tn_pci_address pci_address, struct tn_net_device** out_device)
{
	if (!pf_init(pci_address, out_device)) {
		TN_DEBUG("PF could not init");
		return false;
	}
	struct tn_net_device* device = *out_device;

	// Now for the fun part of enabling the VFs, which isn't really documented outside of specific registers' descriptions...
	// First, we clearly need to enable VFs in PCIREG_SRIOV_CONTROL, which has a separate bit for allowing them to use memory.
	pcireg_set_field(pci_address, PCIREG_SRIOV_CONTROL, PCIREG_SRIOV_CONTROL_VFE);
	pcireg_set_field(pci_address, PCIREG_SRIOV_CONTROL, PCIREG_SRIOV_CONTROL_VFMSE);
	// Then let's set the number of VFs; 64 is the max and seems like a nice number
	pcireg_write_field(pci_address, PCIREG_SRIOV_NUMVFS, PCIREG_SRIOV_NUMVFS_NUMVFS, 64u);
	// This should be enough... now there are enabled VFs, whose BARs are at at 16 KB offsets starting at the VF BAR0.


	// Section 4.6.10.2 IOV Initialization
	// Section 4.6.10.2.1 Physical Function (PF) Driver Initialization
	// "The PF driver is responsible for the link setup and handling of all the filtering and offload capabilities for all the VFs as described in Section 4.6.10.1.1
	//  and the security features as described in Section 4.6.10.1.3.
	//  It should also set the bandwidth allocation per transmit queue for each VF as described in Section 4.6.10."

	// Section 4.6.10.1.1 Global Filtering and Offload Capabilities
	// "Select one of the VMDQ pooling methods — MAC/VLAN filtering for pool selection and either DCB or RSS for the queue in pool selection.
	//  MRQC.Multiple Receive Queues Enable = 1000b, 1010b, 1011b, 1100b, or 1101b."
	//   Section 8.2.3.7.12 Multiple Receive Queues Command Register - MRQC: "1000b = Virtualization only � 64 pools, no RSS, each pool allocated 2 queues."
	reg_write_field(device->addr, REG_MRQC, REG_MRQC_MRQE, 8);

	// "DCB should be initiated as described in Section 4.6.11. In RSS mode, the RSS key (RSSRK) and redirection table (RETA) should be programmed."
	// INTERPRETATION-POINTLESS: We just chose not to use DCB or RSS.

	// "Configure PFVTCTL to define the default pool."
	//   Section 8.2.3.27.1 VT Control Register (PFVTCTL): "DEF_PL, bits 12:7, init val 0x0, Default Pool."
	// We're good with 0 as a default pool so nothing to do here.

	// "Enable replication via PFVTCTL.Rpl_En."
	//   Section 7.10.3.10 Switch Control: "Replication Enable (Rpl_En) — enables replication of multicast and broadcast packets - both in incoming and local traffic.
	//                                      If this bit is cleared, Tx multicast and broadcast packets are sent only to the network and Rx multicast and broadcast packets are sent to the default pool."
	// We're good with using the default pool only for multi/broadcast packets so nothing to do here.

	// "If needed, enable padding of small packets via HLREG0.TXPADEN."
	// The PF init already takes care of this

	// "The MPSAR registers are used to associate Ethernet MAC addresses to pools. Using the MPSAR registers, software must reprogram RAL[0] and RAH[0] by their values
	//  (software could read these registers and then write them back with the same content)."
	// The PF init enabled the first pool, we're good

	// Section 4.6.10.1.3 Security Features
	// "For each pool, the driver might activate the MAC and VLAN anti-spoof features via the relevant bit in PFVFSPOOF.MACAS and PFVFSPOOF.VLANAS, respectively."
	// We do not want these features since they would prevent the implementation of NFs that forward packets without changing the MAC addresses such as bridges; any filtering should be done in software.

	// INTERPRETATION-MISSING: It's not clear what is referred to by "the bandwidth allocation per transmit queue for each VF as described in Section 4.6.10";
	//                         since we did not enable DCB and Section 7.7.2.3 states that means VMs are served round-robin, we'll assume there's nothing to do for using exactly one pool

	// "After all the common parameters are set, the PF driver should set all the VFMailbox[n].RSTD bits by setting CTRL_EXT.PFRSTD."
	reg_set_field(device->addr, REG_CTRLEXT, REG_CTRLEXT_PFRSTD);

	// "PF enables VF traffic via the PFVFTE and PFVFRE registers after all VF parameters are set as defined in Section 4.6.10.1.4."
	//   Section 4.6.10.1.4 Per Pool Settings:
	//   "As soon as a pool of queues is associated to a VM, software should set the following parameters:"
	//   "Associate the unicast Ethernet MAC address of the VM by enabling the pool in the MPSAR registers."
	// We don't care about this, as stated earlier
	//   "If all the Ethernet MAC addresses are used [...]"
	// They aren't.
	//   "Enable the pool in all the RAH/RAL registers representing the multicast Ethernet MAC addresses this VM belongs to."
	// We do not support multicast addresses outside of promiscuous mode.
	//   "If all the Ethernet MAC addresses are used [...]"
	// They still aren't.
	//   "Define whether this VM should get all multicast/broadcast packets in the same VLAN via PFVML2FLT.MPE and PFVML2FLT.BAM, and whether it should accept untagged packets via PFVML2FLT.AUPE."
	// We leave the first two choices to the user via the set_promiscuous function, but we definitely want to accept untagged packets.
	reg_set_field(device->addr, REG_PFVML2FLT(0), REG_PFVML2FLT_AUPE);
	//   "Enable the pool in each PFVLVF and PFVLVFB registers this VM belongs to."
	// The PF init already cleared these registers, and we don't need VLANs.
	//   "A VM might be set to receive it’s own traffic in case the source and the destination are in the same pool via the PFVMTXSW.LLE."
	// We do not want loopback, especially given the possibility of promiscuous mode.
	//   "Whether VLAN header and CRC should be stripped from the packet."
	// The PF init already enabled CRC stripping, nothing to do per Section 7.10.3.6.2 Rx Traffic Offload: "CRC offload is a global policy. CRC strip is enabled or disabled for all received packets."
	//   "Set which header split is required via the PSRTYPE register"
	// Header split should not be used as per Section 7.1.10 Header Splitting: "Header Splitting mode might cause unpredictable behavior and should not be used with the 82599."
	//   "In RSS mode [...]"
	// We do not use RSS.
	//   "Enable the Pool in the PFVFRE register to allow Rx Filtering"
	// We only want to enable VF 0, which is bit 0 of PFVFRE(0) as per Section 8.2.3.27.7 PF VF Receive Enable: "Enables receiving packets to VF# (32*n+j)"
	reg_write(device->addr, REG_PFVFRE(0), BIT(0));
	//   "To Enable Multiple Tx queues, Set the MTQC as described in Section 7.2.1.2.1"
	//     Section 7.2.1.2.1 Tx Queues Assignment: "Programming MTQC must be done only during the init phase while software must also set RTTDCS.ARBDIS before configuring MTQC and then clear RTTDCS.ARBDIS afterwards."
	reg_set_field(device->addr, REG_RTTDCS, REG_RTTDCS_ARBDIS);
	//     Section 8.2.3.9.15 Multiple Transmit Queues Command Register states that NUM_TC_OR_Q should be 01 for 64 VMs
	reg_set_field(device->addr, REG_MTQC, REG_MTQC_VT_ENA);
	reg_write_field(device->addr, REG_MTQC, REG_MTQC_NUM_TC_OR_Q, 1);
	reg_clear_field(device->addr, REG_RTTDCS, REG_RTTDCS_ARBDIS);
	//   "Enable the Pool in the PFVFTE register to allow Tx Filtering"
	// Again, only VF 0, this register works the same way as REG_PFVFRE
	reg_write(device->addr, REG_PFVFTE(0), BIT(0));
	//   "Enable Rx and Tx queues as described in Section 4.6.7 and Section 4.6.8."
	// We'll do this later
	//   "For each Rx queue a drop/no drop flag can be set in SRRCTL.DROP_EN and via the PFQDE register, controlling the behavior if no receive buffers are available in the queue to receive packets.
	//    The usual behavior is to allow drop in order to avoid head of line blocking. Setting PFQDE per queue is made by using the Queue Index field in the PFQDE register."
	// Multiple parts of the spec, such as Section 8.2.3.23.75 Queue Packets Received Drop Count, describe this as an "OR" with the usual Drop_En, so we don't need it since PF init sets Drop_En

	return true;
}

bool tn_net_device_set_promiscuous(struct tn_net_device* device)
{
	if (!pf_set_promiscuous(device)) {
		TN_DEBUG("PF could not be set to promiscuous");
		return false;
	}

	// See the init function for an explanation
	// Not sure if we should stop reception or anything... not written in the data sheet... but this is just a toy driver so let's not
	reg_set_field(device->addr, REG_PFVML2FLT(0), REG_PFVML2FLT_BAM);
	reg_set_field(device->addr, REG_PFVML2FLT(0), REG_PFVML2FLT_MPE);
	return true;
}

static bool vf_get_virtual_bar(struct tn_net_device* device, uint64_t index, void** out_addr)
{
	uint32_t bar0low = pcireg_read(device->pci_addr, PCIREG_SRIOV_BAR0_LOW);
	// Sanity check: a 64-bit BAR must have bit 2 of low as 1 and bit 1 of low as 0 as per Table 9-4 Base Address Registers' Fields
	if ((bar0low & BIT(2)) == 0 || (bar0low & BIT(1)) != 0) {
		TN_DEBUG("VF BAR0 is not a 64-bit BAR");
		return false;
	}

	uint32_t bar0high = pcireg_read(device->pci_addr, PCIREG_SRIOV_BAR0_HIGH);

	uintptr_t bar0 = ((uint64_t) bar0high << 32) | (uint64_t) bar0low;

	if (!tn_mem_phys_to_virt(bar0 + index * IXGBE_VF_SIZE, IXGBE_VF_SIZE, out_addr)) {
		TN_DEBUG("Could not phys-to-virt VF BAR.");
		return false;
	}

	return true;
}

bool tn_net_agent_set_input(struct tn_net_agent* agent, struct tn_net_device* device)
{
	void* vf0_addr;
	if (!vf_get_virtual_bar(device, 0, &vf0_addr)) {
		TN_DEBUG("Could not get VF0's BAR.");
		return false;
	}

	// Fake device!
	// - The address is the VF one, since RX queue registers are at the same offset on PFs and VFs
	// - We pretend rx_enabled is true cause it needs to be done to the PF, not VF
	struct tn_net_device vf_device = {
		.addr = vf0_addr,
		.pci_addr = device->pci_addr,
		.rx_enabled = true
	};
	if (!pf_set_input(agent, &vf_device)) {
		TN_DEBUG("Could not set input using the VF device");
		return false;
	}

	// Now we can start the PF itself
	// We should rollback the set_input call if this happens; but this is a toy driver, so...
	if (!ixgbe_device_start(device)) {
		TN_DEBUG("Could not start the PF");
		return false;
	}

	return true;
}
