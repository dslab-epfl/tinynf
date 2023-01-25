use std::convert::TryInto;
use std::mem::size_of;
use std::time::Duration;

use crate::env::Environment;
use crate::lifed::{LifedPtr, LifedSlice};
use crate::pci::PciAddress;

use super::pci_regs;
use super::regs;

pub const RING_SIZE: usize = 256;

pub struct Device<'a> {
    buffer: LifedSlice<'a, u32>,
}

#[repr(C)]
#[derive(Clone, Copy)]
pub struct Descriptor {
    pub addr: u64,
    pub metadata: u64,
}

#[repr(C)]
pub struct PacketData {
    data: [u8; 2048],
}
impl PacketData {
    pub fn write(&mut self, index: usize, value: u8) {
        // we really just want a volatile write; but the inliner does a great job here
        LifedPtr::new(&mut self.data[index]).write_volatile(value);
    }
}

#[repr(C, align(64))]
pub struct TransmitHead {
    pub value: u32,
}

pub const FIVE_TUPLE_FILTERS_COUNT: usize = 128;

pub const INTERRUPT_REGISTERS_COUNT: usize = 3;

pub const MULTICAST_TABLE_ARRAY_SIZE: usize = 4 * 1024;

pub const POOLS_COUNT: usize = 64;

pub const RECEIVE_ADDRESSES_COUNT: usize = 128;

pub const RECEIVE_QUEUES_COUNT: usize = 128;

pub const TRANSMIT_QUEUES_COUNT: usize = 128;

pub const TRAFFIC_CLASSES_COUNT: usize = 8;

pub const UNICAST_TABLE_ARRAY_SIZE: usize = 4 * 1024;

#[allow(non_snake_case)] // keep names consistent
pub fn RX_METADATA_LENGTH(meta: u64) -> u64 {
    meta & 0xFFFF
}
pub const RX_METADATA_DD: u64 = 1 << 32;

#[allow(non_snake_case)] // same
pub fn TX_METADATA_LENGTH(meta: u64) -> u64 {
    meta & 0xFFFF
}
pub const TX_METADATA_EOP: u64 = 1 << 24;
pub const TX_METADATA_IFCS: u64 = 1 << (24 + 1);
pub const TX_METADATA_RS: u64 = 1 << (24 + 3);

fn after_timeout<'a>(env: &impl Environment<'a>, duration: Duration, cleared: bool, buffer: LifedSlice<'a, u32>, reg: usize, field: u32) -> bool {
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

        let buffer = LifedSlice::new(env.map_physical_memory::<u32>(dev_phys_addr, 128 * 1024 / size_of::<u32>()));

        for queue in 0..RECEIVE_QUEUES_COUNT {
            regs::clear_field(buffer, regs::RXDCTL(queue), regs::RXDCTL_::ENABLE);
            if after_timeout(env, Duration::from_secs(1), false, buffer, regs::RXDCTL(queue), regs::RXDCTL_::ENABLE) {
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
        for n in 1..INTERRUPT_REGISTERS_COUNT {
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

        for n in 0..UNICAST_TABLE_ARRAY_SIZE / 32 {
            regs::clear(buffer, regs::PFUTA(n));
        }

        for n in 0..POOLS_COUNT {
            regs::clear(buffer, regs::PFVLVF(n));
        }

        regs::write(buffer, regs::MPSAR(0), 1);
        for n in 1..RECEIVE_ADDRESSES_COUNT * 2 {
            regs::clear(buffer, regs::MPSAR(n));
        }

        for n in 0..POOLS_COUNT * 2 {
            regs::clear(buffer, regs::PFVLVFB(n));
        }

        for n in 0..MULTICAST_TABLE_ARRAY_SIZE / 32 {
            regs::clear(buffer, regs::MTA(n));
        }

        for n in 0..FIVE_TUPLE_FILTERS_COUNT {
            regs::clear_field(buffer, regs::FTQF(n), regs::FTQF_::QUEUE_ENABLE);
        }

        regs::set_field(buffer, regs::RDRXCTL, regs::RDRXCTL_::CRC_STRIP);

        regs::clear_field(buffer, regs::RDRXCTL, regs::RDRXCTL_::RSCFRSTSIZE);

        regs::set_field(buffer, regs::RDRXCTL, regs::RDRXCTL_::RSCACKC);

        regs::set_field(buffer, regs::RDRXCTL, regs::RDRXCTL_::FCOE_WRFIX);

        for n in 1..TRAFFIC_CLASSES_COUNT {
            regs::clear(buffer, regs::RXPBSIZE(n));
        }

        regs::set_field(buffer, regs::MFLCN, regs::MFLCN_::RFCE);

        regs::write_field(buffer, regs::FCCFG, regs::FCCFG_::TFCE, 1);

        for n in 0..TRANSMIT_QUEUES_COUNT {
            regs::write(buffer, regs::RTTDQSEL, n as u32);
            regs::clear(buffer, regs::RTTDT1C);
        }

        regs::set_field(buffer, regs::RTTDCS, regs::RTTDCS_::ARBDIS);

        for n in 1..TRAFFIC_CLASSES_COUNT {
            regs::clear(buffer, regs::TXPBSIZE(n));
        }

        regs::write_field(buffer, regs::TXPBTHRESH(0), regs::TXPBTHRESH_::THRESH, 0xA0 - (size_of::<PacketData>() / 1024) as u32);

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
        // TODO not exactly what C does, fix this
        regs::clear_field(buffer, regs::TXDCTL(0), regs::TXDCTL_::ENABLE);

        Device { buffer }
    }

    pub fn set_promiscuous(&mut self) {
        regs::clear_field(self.buffer, regs::RXCTRL, regs::RXCTRL_::RXEN);

        regs::set_field(self.buffer, regs::FCTRL, regs::FCTRL_::UPE);
        regs::set_field(self.buffer, regs::FCTRL, regs::FCTRL_::MPE);

        regs::set_field(self.buffer, regs::RXCTRL, regs::RXCTRL_::RXEN);
    }

    pub fn set_input(&self, env: &impl Environment<'a>, ring_start: LifedPtr<'a, Descriptor>) -> LifedPtr<'a, u32> {
        let queue_index: usize = 0;

        if !regs::is_field_cleared(self.buffer, regs::RXDCTL(queue_index), regs::RXDCTL_::ENABLE) {
            panic!("Receive queue is already in use");
        }

        let ring_phys_addr = ring_start.get_physical_address(env);
        regs::write(self.buffer, regs::RDBAH(queue_index), (ring_phys_addr >> 32) as u32);
        regs::write(self.buffer, regs::RDBAL(queue_index), ring_phys_addr as u32);

        regs::write(self.buffer, regs::RDLEN(queue_index), RING_SIZE as u32 * 16);

        regs::write_field(self.buffer, regs::SRRCTL(queue_index), regs::SRRCTL_::BSIZEPACKET, (size_of::<PacketData>() / 1024) as u32);

        regs::set_field(self.buffer, regs::SRRCTL(queue_index), regs::SRRCTL_::DROP_EN);

        regs::set_field(self.buffer, regs::RXDCTL(queue_index), regs::RXDCTL_::ENABLE);

        if after_timeout(env, Duration::from_secs(1), true, self.buffer, regs::RXDCTL(queue_index), regs::RXDCTL_::ENABLE) {
            panic!("RXDCTL.ENABLE did not set, cannot enable queue");
        }

        regs::write(self.buffer, regs::RDT(queue_index), RING_SIZE as u32 - 1);

        regs::clear_field(self.buffer, regs::DCARXCTRL(queue_index), regs::DCARXCTRL_::UNKNOWN);

        self.buffer.index(regs::RDT(queue_index))
    }

    pub fn add_output(&self, env: &impl Environment<'a>, ring_start: LifedPtr<'a, Descriptor>, transmit_head: LifedPtr<'a, TransmitHead>) -> LifedPtr<'a, u32> {
        let mut queue_index = 0;
        while queue_index < TRANSMIT_QUEUES_COUNT {
            if regs::is_field_cleared(self.buffer, regs::TXDCTL(queue_index), regs::TXDCTL_::ENABLE) {
                break;
            }
            queue_index = queue_index + 1;
        }

        if queue_index == TRANSMIT_QUEUES_COUNT {
            panic!("No available transmit queues");
        }

        let ring_phys_addr = ring_start.get_physical_address(env);
        regs::write(self.buffer, regs::TDBAH(queue_index), (ring_phys_addr >> 32) as u32);
        regs::write(self.buffer, regs::TDBAL(queue_index), ring_phys_addr as u32);

        regs::write(self.buffer, regs::TDLEN(queue_index), RING_SIZE as u32 * 16);

        regs::write_field(self.buffer, regs::TXDCTL(queue_index), regs::TXDCTL_::PTHRESH, 60);
        regs::write_field(self.buffer, regs::TXDCTL(queue_index), regs::TXDCTL_::HTHRESH, 4);

        let head_phys_addr = transmit_head.get_physical_address(env);
        if head_phys_addr % 16 != 0 {
            panic!("Transmit head's physical address is not aligned properly");
        }

        regs::write(self.buffer, regs::TDWBAH(queue_index), (head_phys_addr >> 32) as u32);
        regs::write(self.buffer, regs::TDWBAL(queue_index), head_phys_addr as u32 | 1);

        regs::clear_field(self.buffer, regs::DCATXCTRL(queue_index), regs::DCATXCTRL_::TX_DESC_WB_RO_EN);

        regs::set_field(self.buffer, regs::TXDCTL(queue_index), regs::TXDCTL_::ENABLE);
        if after_timeout(env, Duration::from_secs(1), true, self.buffer, regs::TXDCTL(queue_index), regs::TXDCTL_::ENABLE) {
            panic!("TXDCTL.ENABLE did not set, cannot enable queue");
        }

        self.buffer.index(regs::TDT(queue_index))
    }
}
