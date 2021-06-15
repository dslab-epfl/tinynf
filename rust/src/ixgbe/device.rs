use std::convert::TryInto;
use std::mem::size_of;
use std::time::Duration;

use crate::env::Environment;
use crate::pci::PciAddress;

use super::device_limits;
use super::driver_constants;
use super::pci_regs;
use super::regs;


pub struct Device<'a> {
    buffer: &'a mut [u32],
    rx_enabled: bool,
    tx_enabled: bool
}


fn if_after_timeout<F1, F2>(env: &impl Environment, duration: Duration, buffer: &mut [u32], condition: F1, action: F2) where F1: Fn(&[u32]) -> bool, F2: Fn(&mut [u32]) {
    env.sleep(Duration::from_nanos((duration.as_nanos() % 10).try_into().unwrap())); // will panic if 'duration' is too big
    for _i in 0..10 {
        if !condition(buffer) {
            return;
        }
        env.sleep(duration / 10);
    }
    if !condition(buffer) {
        return;
    }
    action(buffer);
}


impl Device<'_> {
    fn create(env: &impl Environment, pci_address: PciAddress) -> Device {
        if size_of::<usize>() > 8 {
            panic!("Pointers must fit in a u64");
        }

        let pci_id = env.pci_read(pci_address, pci_regs::ID);
        if pci_id != ((0x10FB << 16) | 0x8086) {
            panic!("PCI device is not what was expected");
        }

        if !pci_regs::is_field_cleared(env, pci_address, pci_regs::PMCSR, pci_regs::PMCSR_::POWER_STATE) {
            panic!("PCI device not in D0");
        }

        pci_regs::set_field(env, pci_address, pci_regs::COMMAND, pci_regs::COMMAND_::BUS_MASTER_ENABLE);
        pci_regs::set_field(env, pci_address, pci_regs::COMMAND, pci_regs::COMMAND_::MEMORY_ACCESS_ENABLE);
        pci_regs::set_field(env, pci_address, pci_regs::COMMAND, pci_regs::COMMAND_::INTERRUPT_DISABLE);

        let pci_bar0_low = env.pci_read(pci_address, pci_regs::BAR0_LOW);
        if (pci_bar0_low & 0b0100) == 0 || (pci_bar0_low & 0b0010) != 0 {
            panic!("BAR0 is not a 64-bit BAR");
        }

        let pci_bar0_high = env.pci_read(pci_address, pci_regs::BAR0_HIGH);
        let dev_phys_addr = ((pci_bar0_high as u64) << 32) | ((pci_bar0_low as u64) & !0b1111);

        let buffer = env.map_physical_memory::<u32>(dev_phys_addr, 128 * 1024 / size_of::<u32>());

        for queue in 0..device_limits::RECEIVE_QUEUES_COUNT {
            regs::clear_field(buffer, regs::RXDCTL(queue), regs::RXDCTL_::ENABLE);
            if_after_timeout(env, Duration::from_secs(1), buffer, |b| !regs::is_field_cleared(b, regs::RXDCTL(queue), regs::RXDCTL_::ENABLE), |_| {
                panic!("RXDCTL.ENABLE did not clear, cannot disable receive to reset");
            });
            env.sleep(Duration::from_micros(100));
        }

        regs::set_field(buffer, regs::CTRL, regs::CTRL_::MASTER_DISABLE);

        if_after_timeout(env, Duration::from_secs(1), buffer, |b| !regs::is_field_cleared(b, regs::STATUS, regs::STATUS_::PCIE_MASTER_ENABLE_STATUS), |b| {
            if !pci_regs::is_field_cleared(env, pci_address, pci_regs::DEVICESTATUS, pci_regs::DEVICESTATUS_::TRANSACTIONPENDING) {
                panic!("DEVICESTATUS.TRANSACTIONPENDING did not clear, cannot perform master disable to reset");
            }

            regs::set_field(b, regs::HLREG0, regs::HLREG0_::LPBK);
            regs::clear_field(b, regs::RXCTRL, regs::RXCTRL_::RXEN);

            regs::set_field(b, regs::GCREXT, regs::GCREXT_::BUFFERS_CLEAR_FUNC);
            env.sleep(Duration::from_micros(20));

            regs::clear_field(b, regs::HLREG0, regs::HLREG0_::LPBK);
            regs::clear_field(b, regs::GCREXT, regs::GCREXT_::BUFFERS_CLEAR_FUNC);

            regs::set_field(b, regs::CTRL, regs::CTRL_::RST);
            env.sleep(Duration::from_micros(2));
        });

        regs::set_field(buffer, regs::CTRL, regs::CTRL_::RST);
        env.sleep(Duration::from_millis(1));
        env.sleep(Duration::from_millis(10));
        regs::write(buffer, regs::EIMC(0), 0x7FFFFFFF);
        for n in 1..device_limits::INTERRUPT_REGISTERS_COUNT {
            regs::write(buffer, regs::EIMC(n), 0xFFFFFFFF);
        }

        regs::write_field(buffer, regs::FCRTH(0), regs::FCRTH_::RTH, (512 * 1024 - 0x6000) / 32);

        if_after_timeout(env, Duration::from_secs(1), buffer, |b| regs::is_field_cleared(b, regs::EEC, regs::EEC_::AUTO_RD), |_| {
            panic!("EEPROM auto read timed out");
        });

        if regs::is_field_cleared(buffer, regs::EEC, regs::EEC_::EE_PRES) || !regs::is_field_cleared(buffer, regs::FWSM, regs::FWSM_::EXT_ERR_IND) {
            panic!("EEPROM not present or invalid");
        }

        if_after_timeout(env, Duration::from_secs(1), buffer, |b| regs::is_field_cleared(b, regs::RDRXCTL, regs::RDRXCTL_::DMAIDONE), |_| {
            panic!("DMA init timed out");
        });

        for n in 0..device_limits::UNICAST_TABLE_ARRAY_SIZE {
            regs::clear(buffer, regs::PFUTA(n));
        }

        for n in 0..device_limits::POOLS_COUNT {
            regs::clear(buffer, regs::PFVLVF(n));
        }

        regs::write(buffer, regs::MPSAR(0), 1);
        for n in 1..device_limits::RECEIVE_ADDRESSES_COUNT * 2 {
            regs::clear(buffer, regs::MPSAR(n));
        }

        for n in 0..device_limits::POOLS_COUNT * 2 {
            regs::clear(buffer, regs::PFVLVFB(n));
        }

        for n in 0..device_limits::MULTICAST_TABLE_ARRAY_SIZE / 32 {
            regs::clear(buffer, regs::MTA(n));
        }

        for n in 0..device_limits::FIVE_TUPLE_FILTERS_COUNT {
            regs::clear_field(buffer, regs::FTQF(n), regs::FTQF_::QUEUE_ENABLE);
        }

        regs::set_field(buffer, regs::RDRXCTL, regs::RDRXCTL_::CRC_STRIP);

        regs::clear_field(buffer, regs::RDRXCTL, regs::RDRXCTL_::RSCFRSTSIZE);

        regs::set_field(buffer, regs::RDRXCTL, regs::RDRXCTL_::RSCACKC);

        regs::set_field(buffer, regs::RDRXCTL, regs::RDRXCTL_::FCOE_WRFIX);

        for n in 1..device_limits::TRAFFIC_CLASSES_COUNT {
            regs::clear(buffer, regs::RXPBSIZE(n));
        }

        regs::set_field(buffer, regs::MFLCN, regs::MFLCN_::RFCE);

        regs::write_field(buffer, regs::FCCFG, regs::FCCFG_::TFCE, 1);

        for n in 0..device_limits::TRANSMIT_QUEUES_COUNT {
            regs::write(buffer, regs::RTTDQSEL, n);
            regs::clear(buffer, regs::RTTDT1C);
        }

        regs::set_field(buffer, regs::RTTDCS, regs::RTTDCS_::ARBDIS);

        for n in 1..device_limits::TRAFFIC_CLASSES_COUNT {
            regs::clear(buffer, regs::TXPBSIZE(n));
        }

        regs::write_field(buffer, regs::TXPBTHRESH(0), regs::TXPBTHRESH_::THRESH, 0xA0 - (driver_constants::PACKET_SIZE / 1024) as u32);

        regs::write_field(buffer, regs::DTXMXSZRQ, regs::DTXMXSZRQ_::MAX_BYTES_NUM_REQ, 0xFFF);

        regs::clear_field(buffer, regs::RTTDCS, regs::RTTDCS_::ARBDIS);

        Device {
            buffer,
            rx_enabled: false,
            tx_enabled: false
        }
    }
}
/*

        }

        // ----------------------------
        // Section 7.1.1.1 L2 Filtering
        // ----------------------------
        public void SetPromiscuous()
        {
        // "A packet passes successfully through L2 Ethernet MAC address filtering if any of the following conditions are met:"
        // 	Section 8.2.3.7.1 Filter Control Register:
        // 	"Before receive filters are updated/modified the RXCTRL.RXEN bit should be set to 0b.
        // 	After the proper filters have been set the RXCTRL.RXEN bit can be set to 1b to re-enable the receiver."
        if (_rxEnabled)
        {
            regs::clear_field(buffer, regs::RXCTRL, regs::RXCTRL_::RXEN);
        }
        // "Unicast packet filtering - Promiscuous unicast filtering is enabled (FCTRL.UPE=1b) or the packet passes unicast MAC filters (host or manageability)."
        regs::set_field(buffer, regs::FCTRL, regs::FCTRL_::FCTRL_UPE);
        // "Multicast packet filtering - Promiscuous multicast filtering is enabled by either the host or manageability (FCTRL.MPE=1b or MANC.MCST_PASS_L2 =1b) or the packet matches one of the multicast filters."
        regs::set_field(buffer, regs::FCTRL, regs::FCTRL_::MPE);
        // "Broadcast packet filtering to host - Promiscuous multicast filtering is enabled (FCTRL.MPE=1b) or Broadcast Accept Mode is enabled (FCTRL.BAM = 1b)."
        // INTERPRETATION-MISSING: Nothing to do here, since we just enabled MPE; but what is BAM for then?

        if (_rxEnabled)
        {
            regs::set_field(buffer, regs::RXCTRL, regs::RXCTRL_::RXEN);
        }
        }

        // ------------------------------------
        // Section 4.6.7 Receive Initialization
        // ------------------------------------
        internal Memory<uint> SetInput(IEnvironment env, Span<Descriptor> ring)
        {
        // The 82599 has more than one receive queue, but we only need queue 0
        uint queueIndex = 0;

        // See later for details of RXDCTL.ENABLE
        if (!regs::is_field_cleared(buffer, regs::RXDCTL(queueIndex), regs::RXDCTL_::ENABLE))
        {
            panic!("Receive queue is already in use");
        }

        // "The following should be done per each receive queue:"
        // "- Allocate a region of memory for the receive descriptor list."
        // This is already done in agent initialization as agent->rings[0]
        // "- Receive buffers of appropriate size should be allocated and pointers to these buffers should be stored in the descriptor ring."
        // This will be done when setting up the first transmit ring
        // Note that only the first line (buffer address) needs to be configured, the second line is only for write-back except End Of Packet (bit 33)
        // and Descriptor Done (bit 32), which must be 0 as per table in "EOP (End of Packet) and DD (Descriptor Done)"
        // "- Program the descriptor base address with the address of the region (registers RDBAL, RDBAL)."
        // INTERPRETATION-TYPO: This is a typo, the second "RDBAL" should read "RDBAH".
        // 	Section 8.2.3.8.1 Receive Descriptor Base Address Low (RDBAL[n]):
        // 	"The receive descriptor base address must point to a 128 byte-aligned block of data."
        // This alignment is guaranteed by the agent initialization
        nuint ringPhysAddr = env.GetPhysicalAddress(ref ring.GetPinnableReference());
        regs::write(buffer, regs::RDBAH(queueIndex), (uint)(ringPhysAddr >> 32));
        regs::write(buffer, regs::RDBAL(queueIndex), (uint)ringPhysAddr);
        // "- Set the length register to the size of the descriptor ring (register RDLEN)."
        // Section 8.2.3.8.3 Receive DEscriptor Length (RDLEN[n]):
        // "This register sets the number of bytes allocated for descriptors in the circular descriptor buffer."
        // Note that receive descriptors are 16 bytes.
        regs::write(buffer, regs::RDLEN(queueIndex), DriverConstants.RingSize * 16u);
        // "- Program SRRCTL associated with this queue according to the size of the buffers and the required header control."
        //	Section 8.2.3.8.7 Split Receive Control Registers (SRRCTL[n]):
        //		"BSIZEPACKET, Receive Buffer Size for Packet Buffer. The value is in 1 KB resolution. Value can be from 1 KB to 16 KB."
        regs::write_field(buffer, regs::SRRCTL(queueIndex), regs::SRRCTL_::BSIZEPACKET, PacketData.Size / 1024u);
        //		"DESCTYPE, Define the descriptor type in Rx: Init Val 000b [...] 000b = Legacy."
        //		"Drop_En, Drop Enabled. If set to 1b, packets received to the queue when no descriptors are available to store them are dropped."
        // Enable this because of assumption DROP
        regs::set_field(buffer, regs::SRRCTL(queueIndex), regs::SRRCTL_::DROP_EN);
        // "- If header split is required for this queue, program the appropriate PSRTYPE for the appropriate headers."
        // Section 7.1.10 Header Splitting: "Header Splitting mode might cause unpredictable behavior and should not be used with the 82599."
        // "- Program RSC mode for the queue via the RSCCTL register."
        // Nothing to do, we do not want RSC.
        // "- Program RXDCTL with appropriate values including the queue Enable bit. Note that packets directed to a disabled queue are dropped."
        regs::set_field(buffer, regs::RXDCTL(queueIndex), regs::RXDCTL_::ENABLE);
        // "- Poll the RXDCTL register until the Enable bit is set. The tail should not be bumped before this bit was read as 1b."
        // INTERPRETATION-MISSING: No timeout is mentioned here, let's say 1s to be safe.
        if_after_timeout(env, Duration::from_secs(1), ???, || regs::is_field_cleared(buffer, regs::RXDCTL(queueIndex), regs::RXDCTL_::ENABLE), ||
        {
            panic!("RXDCTL.ENABLE did not set, cannot enable queue");
        });
        // "- Bump the tail pointer (RDT) to enable descriptors fetching by setting it to the ring length minus one."
        // 	Section 7.1.9 Receive Descriptor Queue Structure:
        // 	"Software inserts receive descriptors by advancing the tail pointer(s) to refer to the address of the entry just beyond the last valid descriptor."
        regs::write(buffer, regs::RDT(queueIndex), DriverConstants.RingSize - 1u);
        // "- Enable the receive path by setting RXCTRL.RXEN. This should be done only after all other settings are done following the steps below."
        // INTERPRETATION-MISSING: "after all other settings are done" is ambiguous here, let's assume we can just do it after setting up a receive queue...
        if (!_rxEnabled)
        {
            //	"- Halt the receive data path by setting SECRXCTRL.RX_DIS bit."
            regs::set_field(buffer, regs::SECRXCTRL, regs::SECRXCTRL_::RX_DIS);
            //	"- Wait for the data paths to be emptied by HW. Poll the SECRXSTAT.SECRX_RDY bit until it is asserted by HW."
            // INTERPRETATION-MISSING: Another undefined timeout, assuming 1s as usual
            if_after_timeout(env, Duration::from_secs(1), ???, || regs::is_field_cleared(buffer, regs::SECRXSTAT, regs::SECRXSTAT_::SECRX_RDY), ||
            {
                panic!("SECRXSTAT.SECRXRDY timed out, cannot start device");
            });
            //	"- Set RXCTRL.RXEN"
            regs::set_field(buffer, regs::RXCTRL, regs::RXCTRL_::RXEN);
            //	"- Clear the SECRXCTRL.SECRX_DIS bits to enable receive data path"
            // INTERPRETATION-TYPO: This refers to RX_DIS, not SECRX_DIS, since it's RX_DIS being cleared that enables the receive data path.
            regs::clear_field(buffer, regs::SECRXCTRL, regs::SECRXCTRL_::RX_DIS);
            //	"- If software uses the receive descriptor minimum threshold Interrupt, that value should be set."
            // We do not have to set this by assumption NOWANT
            // "  Set bit 16 of the CTRL_EXT register and clear bit 12 of the DCA_RXCTRL[n] register[n]."
            // Again, we do the first part here since it's a non-queue-dependent register
            // Section 8.2.3.1.3 Extended Device Control Register (CTRL_EXT): Bit 16 == "NS_DIS, No Snoop Disable"
            regs::set_field(buffer, regs::CTRLEXT, regs::CTRLEXT_::NSDIS);

            _rxEnabled = true;
        }
        // Section 8.2.3.11.1 Rx DCA Control Register (DCA_RXCTRL[n]): Bit 12 == "Default 1b; Reserved. Must be set to 0."
        regs::clear_field(buffer, regs::DCARXCTRL(queueIndex), regs::DCARXCTRL_::UNKNOWN);

        return buffer.Slice((int)regs::RDT(queueIndex) / sizeof(uint), 1);
        }

        // -------------------------------------
        // Section 4.6.8 Transmit Initialization
        // -------------------------------------
        internal Memory<uint> AddOutput(IEnvironment env, Span<Descriptor> ring, ref uint transmitHead)
        {
        uint queueIndex = 0;
        for (; queueIndex < DeviceLimits.TransmitQueuesCount; queueIndex++)
        {
            // See later for details of TXDCTL.ENABLE
            if (regs::is_field_cleared(buffer, regs::TXDCTL(queueIndex), regs::TXDCTL_::ENABLE))
            {
                break;
            }
        }
        if (queueIndex == DeviceLimits.TransmitQueuesCount)
        {
            panic!("No available transmit queues");
        }

        // "The following steps should be done once per transmit queue:"
        // "- Allocate a region of memory for the transmit descriptor list."
        // This is already done in agent initialization as agent->rings[*]

        // "- Program the descriptor base address with the address of the region (TDBAL, TDBAH)."
        // 	Section 8.2.3.9.5 Transmit Descriptor Base Address Low (TDBAL[n]):
        // 	"The Transmit Descriptor Base Address must point to a 128 byte-aligned block of data."
        // This alignment is guaranteed by the agent initialization
        nuint ringPhysAddr = env.GetPhysicalAddress(ref ring.GetPinnableReference());
        regs::write(buffer, regs::TDBAH(queueIndex), (uint)(ringPhysAddr >> 32));
        regs::write(buffer, regs::TDBAL(queueIndex), (uint)ringPhysAddr);
        // "- Set the length register to the size of the descriptor ring (TDLEN)."
        // 	Section 8.2.3.9.7 Transmit Descriptor Length (TDLEN[n]):
        // 	"This register sets the number of bytes allocated for descriptors in the circular descriptor buffer."
        // Note that each descriptor is 16 bytes.
        regs::write(buffer, regs::TDLEN(queueIndex), DriverConstants.RingSize * 16u);
        // "- Program the TXDCTL register with the desired TX descriptor write back policy (see Section 8.2.3.9.10 for recommended values)."
        //	Section 8.2.3.9.10 Transmit Descriptor Control (TXDCTL[n]):
        //	"HTHRESH should be given a non-zero value each time PTHRESH is used."
        //	"For PTHRESH and HTHRESH recommended setting please refer to Section 7.2.3.4."
        // INTERPRETATION-MISSING: The "recommended values" are in 7.2.3.4.1 very vague; we use (cache line size)/(descriptor size) for HTHRESH (i.e. 64/16 by assumption CACHE),
        //                 and a completely arbitrary value for PTHRESH
        // PERFORMANCE: This is required to forward 10G traffic on a single NIC.
        regs::write_field(buffer, regs::TXDCTL(queueIndex), regs::TXDCTL_::PTHRESH, 60);
        regs::write_field(buffer, regs::TXDCTL(queueIndex), regs::TXDCTL_::HTHRESH, 4);
        // "- If needed, set TDWBAL/TWDBAH to enable head write back."
        nuint headPhysAddr = env.GetPhysicalAddress(ref transmitHead);
        //	Section 7.2.3.5.2 Tx Head Pointer Write Back:
        //	"The low register's LSB hold the control bits.
        // 	 * The Head_WB_EN bit enables activation of tail write back. In this case, no descriptor write back is executed.
        // 	 * The 30 upper bits of this register hold the lowest 32 bits of the head write-back address, assuming that the two last bits are zero."
        //	"software should [...] make sure the TDBAL value is Dword-aligned."
        //	Section 8.2.3.9.11 Tx Descriptor completion Write Back Address Low (TDWBAL[n]): "the actual address is Qword aligned"
        // INTERPRETATION-CONTRADICTION: There is an obvious contradiction here; qword-aligned seems like a safe option since it will also be dword-aligned.
        // INTERPRETATION-INCORRECT: Empirically, the answer is... 16 bytes. Write-back has no effect otherwise. So both versions are wrong.
        if (headPhysAddr % 16u != 0)
        {
            panic!("Transmit head's physical address is not aligned properly");
        }
        //	Section 8.2.3.9.11 Tx Descriptor Completion Write Back Address Low (TDWBAL[n]):
        //	"Head_WB_En, bit 0 [...] 1b = Head write-back is enabled."
        //	"Reserved, bit 1"
        regs::write(buffer, regs::TDWBAH(queueIndex), (uint)(headPhysAddr >> 32));
        regs::write(buffer, regs::TDWBAL(queueIndex), (uint)headPhysAddr | 1u);
        // INTERPRETATION-MISSING: We must disable relaxed ordering of head pointer write-back, since it could cause the head pointer to be updated backwards
        regs::clear_field(buffer, regs::DCATXCTRL(queueIndex), regs::DCATXCTRL_::TX_DESC_WB_RO_EN);
        // "- Enable transmit path by setting DMATXCTL.TE.
        //    This step should be executed only for the first enabled transmit queue and does not need to be repeated for any following queues."
        if (!_txEnabled)
        {
            regs::set_field(buffer, regs::DMATXCTL, regs::DMATXCTL_::TE);
            _txEnabled = true;
        }
        // "- Enable the queue using TXDCTL.ENABLE.
        //    Poll the TXDCTL register until the Enable bit is set."
        // INTERPRETATION-MISSING: No timeout is mentioned here, let's say 1s to be safe.
        regs::set_field(buffer, regs::TXDCTL(queueIndex), regs::TXDCTL_::ENABLE);
        if_after_timeout(env, Duration::from_secs(1), ???, || regs::is_field_cleared(buffer, regs::TXDCTL(queueIndex), regs::TXDCTL_::ENABLE), ||
        {
            panic!("TXDCTL.ENABLE did not set, cannot enable queue");
        });
        // "Note: The tail register of the queue (TDT) should not be bumped until the queue is enabled."
        // Nothing to transmit yet, so leave TDT alone.

        return buffer.Slice((int)regs::TDT(queueIndex) / sizeof(uint), 1);
        }
    }
*/
