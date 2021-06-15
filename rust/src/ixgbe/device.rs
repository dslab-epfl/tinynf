use std::convert::TryInto;
use std::mem::size_of;
use std::time::Duration;

use crate::env::Environment;
use crate::pci::PciAddress;

use super::descriptor::Descriptor;
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

        regs::write_field(buffer, regs::TXPBTHRESH(0), regs::TXPBTHRESH_::THRESH, 0xA0 - driver_constants::PACKET_SIZE / 1024);

        regs::write_field(buffer, regs::DTXMXSZRQ, regs::DTXMXSZRQ_::MAX_BYTES_NUM_REQ, 0xFFF);

        regs::clear_field(buffer, regs::RTTDCS, regs::RTTDCS_::ARBDIS);

        Device {
            buffer,
            rx_enabled: false,
            tx_enabled: false
        }
    }

    pub fn set_promiscuous(&mut self) {
        if self.rx_enabled {
            regs::clear_field(self.buffer, regs::RXCTRL, regs::RXCTRL_::RXEN);
        }
        regs::set_field(self.buffer, regs::FCTRL, regs::FCTRL_::FCTRL_UPE);
        regs::set_field(self.buffer, regs::FCTRL, regs::FCTRL_::MPE);
        if self.rx_enabled {
            regs::set_field(self.buffer, regs::RXCTRL, regs::RXCTRL_::RXEN);
        }
    }

    pub fn set_input<'a>(&'a mut self, env: &impl Environment, ring: &mut [Descriptor]) -> &'a mut u32 {
        let queue_index: u32 = 0;

        if !regs::is_field_cleared(self.buffer, regs::RXDCTL(queue_index), regs::RXDCTL_::ENABLE) {
            panic!("Receive queue is already in use");
        }

        let ring_phys_addr = env.get_physical_address(ring);
        regs::write(self.buffer, regs::RDBAH(queue_index), (ring_phys_addr >> 32) as u32);
        regs::write(self.buffer, regs::RDBAL(queue_index), ring_phys_addr as u32);

        regs::write(self.buffer, regs::RDLEN(queue_index), driver_constants::RING_SIZE * 16);

        regs::write_field(self.buffer, regs::SRRCTL(queue_index), regs::SRRCTL_::BSIZEPACKET, driver_constants::PACKET_SIZE / 1024);

        regs::set_field(self.buffer, regs::SRRCTL(queue_index), regs::SRRCTL_::DROP_EN);

        regs::set_field(self.buffer, regs::RXDCTL(queue_index), regs::RXDCTL_::ENABLE);

        if_after_timeout(env, Duration::from_secs(1), self.buffer, |b| regs::is_field_cleared(b, regs::RXDCTL(queue_index), regs::RXDCTL_::ENABLE), |_| {
            panic!("RXDCTL.ENABLE did not set, cannot enable queue");
        });

        regs::write(self.buffer, regs::RDT(queue_index), driver_constants::RING_SIZE - 1);

        if !self.rx_enabled {
            regs::set_field(self.buffer, regs::SECRXCTRL, regs::SECRXCTRL_::RX_DIS);

            if_after_timeout(env, Duration::from_secs(1), self.buffer, |b| regs::is_field_cleared(b, regs::SECRXSTAT, regs::SECRXSTAT_::SECRX_RDY), |_| {
                panic!("SECRXSTAT.SECRXRDY timed out, cannot start device");
            });

            regs::set_field(self.buffer, regs::RXCTRL, regs::RXCTRL_::RXEN);

            regs::clear_field(self.buffer, regs::SECRXCTRL, regs::SECRXCTRL_::RX_DIS);

            regs::set_field(self.buffer, regs::CTRLEXT, regs::CTRLEXT_::NSDIS);

            self.rx_enabled = true;
        }

        regs::clear_field(self.buffer, regs::DCARXCTRL(queue_index), regs::DCARXCTRL_::UNKNOWN);

        &mut self.buffer[regs::RDT(queue_index) as usize / size_of::<u32>()]
    }
/*
        // -------------------------------------
        // Section 4.6.8 Transmit Initialization
        // -------------------------------------
        internal Memory<uint> AddOutput(IEnvironment env, Span<Descriptor> ring, ref uint transmitHead)
        {
        uint queue_index = 0;
        for (; queue_index < DeviceLimits.TransmitQueuesCount; queue_index++)
        {
            // See later for details of TXDCTL.ENABLE
            if (regs::is_field_cleared(buffer, regs::TXDCTL(queue_index), regs::TXDCTL_::ENABLE))
            {
                break;
            }
        }
        if (queue_index == DeviceLimits.TransmitQueuesCount)
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
        nuint ring_phys_addr = env.GetPhysicalAddress(ref ring.GetPinnableReference());
        regs::write(buffer, regs::TDBAH(queue_index), (uint)(ring_phys_addr >> 32));
        regs::write(buffer, regs::TDBAL(queue_index), (uint)ring_phys_addr);
        // "- Set the length register to the size of the descriptor ring (TDLEN)."
        // 	Section 8.2.3.9.7 Transmit Descriptor Length (TDLEN[n]):
        // 	"This register sets the number of bytes allocated for descriptors in the circular descriptor buffer."
        // Note that each descriptor is 16 bytes.
        regs::write(buffer, regs::TDLEN(queue_index), DriverConstants.RingSize * 16u);
        // "- Program the TXDCTL register with the desired TX descriptor write back policy (see Section 8.2.3.9.10 for recommended values)."
        //	Section 8.2.3.9.10 Transmit Descriptor Control (TXDCTL[n]):
        //	"HTHRESH should be given a non-zero value each time PTHRESH is used."
        //	"For PTHRESH and HTHRESH recommended setting please refer to Section 7.2.3.4."
        // INTERPRETATION-MISSING: The "recommended values" are in 7.2.3.4.1 very vague; we use (cache line size)/(descriptor size) for HTHRESH (i.e. 64/16 by assumption CACHE),
        //                 and a completely arbitrary value for PTHRESH
        // PERFORMANCE: This is required to forward 10G traffic on a single NIC.
        regs::write_field(buffer, regs::TXDCTL(queue_index), regs::TXDCTL_::PTHRESH, 60);
        regs::write_field(buffer, regs::TXDCTL(queue_index), regs::TXDCTL_::HTHRESH, 4);
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
        regs::write(buffer, regs::TDWBAH(queue_index), (uint)(headPhysAddr >> 32));
        regs::write(buffer, regs::TDWBAL(queue_index), (uint)headPhysAddr | 1u);
        // INTERPRETATION-MISSING: We must disable relaxed ordering of head pointer write-back, since it could cause the head pointer to be updated backwards
        regs::clear_field(buffer, regs::DCATXCTRL(queue_index), regs::DCATXCTRL_::TX_DESC_WB_RO_EN);
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
        regs::set_field(buffer, regs::TXDCTL(queue_index), regs::TXDCTL_::ENABLE);
        if_after_timeout(env, Duration::from_secs(1), ???, || regs::is_field_cleared(buffer, regs::TXDCTL(queue_index), regs::TXDCTL_::ENABLE), ||
        {
            panic!("TXDCTL.ENABLE did not set, cannot enable queue");
        });
        // "Note: The tail register of the queue (TDT) should not be bumped until the queue is enabled."
        // Nothing to transmit yet, so leave TDT alone.

        return buffer.Slice((int)regs::TDT(queue_index) / sizeof(uint), 1);
        }
    }
*/
}
