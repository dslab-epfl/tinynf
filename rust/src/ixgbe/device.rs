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
}

fn after_timeout<'a>(env: &impl Environment<'a>, duration: Duration, cleared: bool, buffer: &mut [u32], reg: usize, field: u32) -> bool {
    env.sleep(Duration::from_nanos((duration.as_nanos() % 10).try_into().unwrap())); // will panic if 'duration' is too big
    for _i in 0..10 {
        if regs::is_field_cleared(buffer, reg, field) != cleared {
            return false;
        }
        env.sleep(duration / 10);
    }
    cleared == regs::is_field_cleared(buffer, reg, field)
}

impl<'a> Device<'a> {
    pub fn init(env: &impl Environment<'a>, pci_address: PciAddress) -> Device<'a> {
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
            regs::clear_field(buffer, regs::RX_ZONE_BASE(queue) + regs::RXDCTL, regs::RXDCTL_::ENABLE);
            if after_timeout(env, Duration::from_secs(1), false, buffer, regs::RX_ZONE_BASE(queue) + regs::RXDCTL, regs::RXDCTL_::ENABLE) {
                panic!("RXDCTL.ENABLE did not clear, cannot disable receive to reset");
            };
            env.sleep(Duration::from_micros(100));
        }

        regs::set_field(buffer, regs::CTRL, regs::CTRL_::MASTER_DISABLE);

        if after_timeout(env, Duration::from_secs(1), false, buffer, regs::STATUS, regs::STATUS_::PCIE_MASTER_ENABLE_STATUS) {
            if !pci_regs::is_field_cleared(env, pci_address, pci_regs::DEVICESTATUS, pci_regs::DEVICESTATUS_::TRANSACTIONPENDING) {
                panic!("DEVICESTATUS.TRANSACTIONPENDING did not clear, cannot perform master disable to reset");
            }

            regs::set_field(buffer, regs::HLREG0, regs::HLREG0_::LPBK);
            regs::clear_field(buffer, regs::RXCTRL, regs::RXCTRL_::RXEN);

            regs::set_field(buffer, regs::GCREXT, regs::GCREXT_::BUFFERS_CLEAR_FUNC);
            env.sleep(Duration::from_micros(20));

            regs::clear_field(buffer, regs::HLREG0, regs::HLREG0_::LPBK);
            regs::clear_field(buffer, regs::GCREXT, regs::GCREXT_::BUFFERS_CLEAR_FUNC);

            regs::set_field(buffer, regs::CTRL, regs::CTRL_::RST);
            env.sleep(Duration::from_micros(2));
        }

        regs::set_field(buffer, regs::CTRL, regs::CTRL_::RST);

        env.sleep(Duration::from_millis(1));

        env.sleep(Duration::from_millis(10));

        regs::write(buffer, regs::EIMC(0), 0x7FFF_FFFF);
        for n in 1..device_limits::INTERRUPT_REGISTERS_COUNT {
            regs::write(buffer, regs::EIMC(n), 0xFFFF_FFFF);
        }

        regs::write_field(buffer, regs::FCRTH(0), regs::FCRTH_::RTH, (512 * 1024 - 0x6000) / 32);

        if after_timeout(env, Duration::from_secs(1), true, buffer, regs::EEC, regs::EEC_::AUTO_RD) {
            panic!("EEPROM auto read timed out");
        }

        if regs::is_field_cleared(buffer, regs::EEC, regs::EEC_::EE_PRES) || !regs::is_field_cleared(buffer, regs::FWSM, regs::FWSM_::EXT_ERR_IND) {
            panic!("EEPROM not present or invalid");
        }

        if after_timeout(env, Duration::from_secs(1), true, buffer, regs::RDRXCTL, regs::RDRXCTL_::DMAIDONE) {
            panic!("DMA init timed out");
        }

        for n in 0..device_limits::UNICAST_TABLE_ARRAY_SIZE / 32 {
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
            regs::write(buffer, regs::RTTDQSEL, n as u32);
            regs::clear(buffer, regs::RTTDT1C);
        }

        regs::set_field(buffer, regs::RTTDCS, regs::RTTDCS_::ARBDIS);

        for n in 1..device_limits::TRAFFIC_CLASSES_COUNT {
            regs::clear(buffer, regs::TXPBSIZE(n));
        }

        regs::write_field(buffer, regs::TXPBTHRESH(0), regs::TXPBTHRESH_::THRESH, 0xA0 - (driver_constants::PACKET_SIZE / 1024) as u32);

        regs::write_field(buffer, regs::DTXMXSZRQ, regs::DTXMXSZRQ_::MAX_BYTES_NUM_REQ, 0xFFF);

        regs::clear_field(buffer, regs::RTTDCS, regs::RTTDCS_::ARBDIS);

        // Enable RX
        regs::set_field(buffer, regs::SECRXCTRL, regs::SECRXCTRL_::RX_DIS);
        if after_timeout(env, Duration::from_secs(1), true, buffer, regs::SECRXSTAT, regs::SECRXSTAT_::SECRX_RDY) {
            panic!("SECRXSTAT.SECRXRDY timed out, cannot start device");
        }
        regs::set_field(buffer, regs::RXCTRL, regs::RXCTRL_::RXEN);
        regs::clear_field(buffer, regs::SECRXCTRL, regs::SECRXCTRL_::RX_DIS);
        regs::set_field(buffer, regs::CTRLEXT, regs::CTRLEXT_::NSDIS);

        // Enable TX
        regs::set_field(buffer, regs::DMATXCTL, regs::DMATXCTL_::TE);
        // But disable first queue, which is enabled when we enable TX globally (see 8.2.3.9.10 ENABLE)
        regs::clear_field(buffer, regs::TX_ZONE_BASE(0) + regs::TXDCTL, regs::TXDCTL_::ENABLE);

        Device { buffer }
    }

    pub fn set_promiscuous(&mut self) {
        regs::clear_field(self.buffer, regs::RXCTRL, regs::RXCTRL_::RXEN);

        regs::set_field(self.buffer, regs::FCTRL, regs::FCTRL_::UPE);
        regs::set_field(self.buffer, regs::FCTRL, regs::FCTRL_::MPE);

        regs::set_field(self.buffer, regs::RXCTRL, regs::RXCTRL_::RXEN);
    }

    pub fn into_inout(self) -> (DeviceInput<'a>, DeviceOutput<'a>) {
        let (_x, rx_base) = self.buffer.split_at_mut(regs::RX_ZONE_BASE(0));
        let (rx, rest) = rx_base.split_at_mut(regs::RX_ZONE_LEN);
        let (_y, tx_base) = rest.split_at_mut(regs::TX_ZONE_BASE(0) - regs::RX_ZONE_LEN - regs::RX_ZONE_BASE(0));
        let (tx, _z) = tx_base.split_at_mut(regs::TX_ZONE_LEN);
        (DeviceInput { buffer: rx }, DeviceOutput { buffer: tx })
    }
}

pub struct DeviceInput<'a> {
    buffer: &'a mut [u32],
}

impl<'a> DeviceInput<'a> {
    pub fn associate<'b>(&'a mut self, env: &impl Environment<'b>, ring: &mut [Descriptor]) -> &'a mut u32 {
        if !regs::is_field_cleared(self.buffer, regs::RXDCTL, regs::RXDCTL_::ENABLE) {
            panic!("Receive queue is already in use");
        }

        let ring_phys_addr = env.get_physical_address(&mut ring[0]);
        regs::write(self.buffer, regs::RDBAH, (ring_phys_addr >> 32) as u32);
        regs::write(self.buffer, regs::RDBAL, ring_phys_addr as u32);

        regs::write(self.buffer, regs::RDLEN, driver_constants::RING_SIZE as u32 * 16);

        regs::write_field(self.buffer, regs::SRRCTL, regs::SRRCTL_::BSIZEPACKET, (driver_constants::PACKET_SIZE / 1024) as u32);

        regs::set_field(self.buffer, regs::SRRCTL, regs::SRRCTL_::DROP_EN);

        regs::set_field(self.buffer, regs::RXDCTL, regs::RXDCTL_::ENABLE);

        if after_timeout(env, Duration::from_secs(1), true, self.buffer, regs::RXDCTL, regs::RXDCTL_::ENABLE) {
            panic!("RXDCTL.ENABLE did not set, cannot enable queue");
        }

        regs::write(self.buffer, regs::RDT, driver_constants::RING_SIZE as u32 - 1);

        regs::clear_field(self.buffer, regs::DCARXCTRL, regs::DCARXCTRL_::UNKNOWN);

        &mut self.buffer[regs::RDT]
    }
}

pub struct DeviceOutput<'a> {
    buffer: &'a mut [u32],
}

impl<'a> DeviceOutput<'a> {
    pub fn associate<'b>(&'a mut self, env: &impl Environment<'b>, ring: &mut [Descriptor], transmit_head: &mut u32) -> &'a mut u32 {
        if !regs::is_field_cleared(self.buffer, regs::TXDCTL, regs::TXDCTL_::ENABLE) {
            panic!("Transmit queue is not available");
        }

        let ring_phys_addr = env.get_physical_address(&mut ring[0]);
        regs::write(self.buffer, regs::TDBAH, (ring_phys_addr >> 32) as u32);
        regs::write(self.buffer, regs::TDBAL, ring_phys_addr as u32);

        regs::write(self.buffer, regs::TDLEN, driver_constants::RING_SIZE as u32 * 16);

        regs::write_field(self.buffer, regs::TXDCTL, regs::TXDCTL_::PTHRESH, 60);
        regs::write_field(self.buffer, regs::TXDCTL, regs::TXDCTL_::HTHRESH, 4);

        let head_phys_addr = env.get_physical_address(transmit_head);
        if head_phys_addr % 16 != 0 {
            panic!("Transmit head's physical address is not aligned properly");
        }

        regs::write(self.buffer, regs::TDWBAH, (head_phys_addr >> 32) as u32);
        regs::write(self.buffer, regs::TDWBAL, head_phys_addr as u32 | 1);

        regs::clear_field(self.buffer, regs::DCATXCTRL, regs::DCATXCTRL_::TX_DESC_WB_RO_EN);

        regs::set_field(self.buffer, regs::TXDCTL, regs::TXDCTL_::ENABLE);
        if after_timeout(env, Duration::from_secs(1), true, self.buffer, regs::TXDCTL, regs::TXDCTL_::ENABLE) {
            panic!("TXDCTL.ENABLE did not set, cannot enable queue");
        }

        &mut self.buffer[regs::TDT]
    }
}
