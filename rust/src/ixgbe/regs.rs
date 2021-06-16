#![allow(non_snake_case)]

use crate::volatile;

pub fn read(buffer: &[u32], reg: usize) -> u32 {
    u32::from_le(volatile::read(&buffer[reg]))
}

pub fn read_field(buffer: &[u32], reg: usize, field: u32) -> u32 {
    let value = read(buffer, reg);
    let shift = field.trailing_zeros();
    (value & field) >> shift
}

pub fn write(buffer: &mut [u32], reg: usize, value: u32) {
    volatile::write(&mut buffer[reg], u32::to_le(value));
}

pub fn write_field(buffer: &mut [u32], reg: usize, field: u32, field_value: u32) {
    let old_value = read(buffer, reg);
    let shift = field.trailing_zeros();
    let new_value = (old_value & !field) | (field_value << shift);
    write(buffer, reg, new_value);
}

pub fn clear(buffer: &mut [u32], reg: usize) {
    write(buffer, reg, 0);
}

pub fn clear_field(buffer: &mut [u32], reg: usize, field: u32) {
    write_field(buffer, reg, field, 0);
}

pub fn set_field(buffer: &mut [u32], reg: usize, field: u32) {
    let old_value = read(buffer, reg);
    let new_value = old_value | field;
    write(buffer, reg, new_value);
}

pub fn is_field_cleared(buffer: &[u32], reg: usize, field: u32) -> bool {
    read_field(buffer, reg, field) == 0
}

// All regs divided by 4 since they'll be used to address a slice of u32, not of u8
// And they're usize so they can index a slice without ceremony

// Registers are split into general-purpose, RX, and TX, so that we can split the device address space
// Thankfully RX/TX spaces are contiguous, otherwise this would be a huuuuge pain

// --- General ---

pub const CTRL: usize = 0x00000 / 4;
pub mod CTRL_ {
    pub const MASTER_DISABLE: u32 = 1 << 2;
    pub const RST: u32 = 1 << 26;
}

pub const CTRLEXT: usize = 0x00018 / 4;
pub mod CTRLEXT_ {
    pub const NSDIS: u32 = 1 << 16;
}

pub const DMATXCTL: usize = 0x04A80 / 4;
pub mod DMATXCTL_ {
    pub const TE: u32 = 1 << 0;
}

pub const DTXMXSZRQ: usize = 0x08100 / 4;
pub mod DTXMXSZRQ_ {
    pub const MAX_BYTES_NUM_REQ: u32 = 0b0111_1111_1111;
}

pub const EEC: usize = 0x10010 / 4;
pub mod EEC_ {
    pub const EE_PRES: u32 = 1 << 8;
    pub const AUTO_RD: u32 = 1 << 9;
}

pub fn EIMC(n: usize) -> usize {
    (if n == 0 { 0x00888 } else { 0x00AB0 + 4 * (n - 1) }) / 4
}

pub const FCCFG: usize = 0x03D00 / 4;
pub mod FCCFG_ {
    pub const TFCE: u32 = 0b0001_1000;
}

pub fn FCRTH(n: usize) -> usize {
    (0x03260 + 4 * n) / 4
}
pub mod FCRTH_ {
    pub const RTH: u32 = 0b0111_1111_1111_1110_0000;
}

pub const FCTRL: usize = 0x05080 / 4;
pub mod FCTRL_ {
    pub const MPE: u32 = 1 << 8;
    pub const FCTRL_UPE: u32 = 1 << 9;
}

pub fn FTQF(n: usize) -> usize {
    (0x0E600 + 4 * n) / 4
}
pub mod FTQF_ {
    pub const QUEUE_ENABLE: u32 = 1 << 31;
}

pub const FWSM: usize = 0x10148 / 4;
pub mod FWSM_ {
    pub const EXT_ERR_IND: u32 = 0b0001_1111_1000_0000_0000_0000_0000;
}

pub const GCREXT: usize = 0x11050 / 4;
pub mod GCREXT_ {
    pub const BUFFERS_CLEAR_FUNC: u32 = 1 << 30;
}

pub const HLREG0: usize = 0x04240 / 4;
pub mod HLREG0_ {
    pub const LPBK: u32 = 1 << 15;
}

pub const MFLCN: usize = 0x04294 / 4;
pub mod MFLCN_ {
    pub const RFCE: u32 = 1 << 3;
}

pub fn MPSAR(n: usize) -> usize {
    (0x0A600 + 4 * n) / 4
}

pub fn MTA(n: usize) -> usize {
    (0x05200 + 4 * n) / 4
}

pub fn PFUTA(n: usize) -> usize {
    (0x0F400 + 4 * n) / 4
}

pub fn PFVLVF(n: usize) -> usize {
    (0x0F100 + 4 * n) / 4
}

pub fn PFVLVFB(n: usize) -> usize {
    (0x0F200 + 4 * n) / 4
}

pub const RDRXCTL: usize = 0x02F00 / 4;
pub mod RDRXCTL_ {
    pub const CRC_STRIP: u32 = 1 << 1;
    pub const DMAIDONE: u32 = 1 << 3;
    pub const RSCFRSTSIZE: u32 = 0b0011_1110_0000_0000_0000_0000;
    pub const RSCACKC: u32 = 1 << 25;
    pub const FCOE_WRFIX: u32 = 1 << 26;
}

pub const RTTDCS: usize = 0x04900 / 4;
pub mod RTTDCS_ {
    pub const ARBDIS: u32 = 1 << 6;
}

pub const RTTDQSEL: usize = 0x04904 / 4;

pub const RTTDT1C: usize = 0x04908 / 4;

pub const RXCTRL: usize = 0x03000 / 4;
pub mod RXCTRL_ {
    pub const RXEN: u32 = 1 << 0;
}

pub fn RXPBSIZE(n: usize) -> usize {
    (0x03C00 + 4 * n) / 4
}

pub const SECRXCTRL: usize = 0x08D00 / 4;
pub mod SECRXCTRL_ {
    pub const RX_DIS: u32 = 1 << 1;
}

pub const SECRXSTAT: usize = 0x08D04 / 4;
pub mod SECRXSTAT_ {
    pub const SECRX_RDY: u32 = 1 << 0;
}

pub const STATUS: usize = 0x00008 / 4;
pub mod STATUS_ {
    pub const PCIE_MASTER_ENABLE_STATUS: u32 = 1 << 19;
}

pub fn TXPBSIZE(n: usize) -> usize {
    (0x0CC00 + 4 * n) / 4
}

pub fn TXPBTHRESH(n: usize) -> usize {
    (0x04950 + 4 * n) / 4
}
pub mod TXPBTHRESH_ {
    pub const THRESH: u32 = 0b11_1111_1111;
}

// --- RX ---

pub fn RX_ZONE_BASE(n: usize) -> usize {
    (if n <= 63 { 0x01000 + 0x40 * n } else { 0x0D000 + 0x40 * (n - 64) }) / 4
}
pub const RX_ZONE_LEN: usize = 0x40;

pub const RDBAH: usize = 0x04 / 4;

pub const RDBAL: usize = 0x00 / 4;

pub const RDLEN: usize = 0x08 / 4;

pub const RDT: usize = 0x18 / 4;

pub const RXDCTL: usize = 0x28 / 4;
pub mod RXDCTL_ {
    pub const ENABLE: u32 = 1 << 25;
}

pub const SRRCTL: usize = 0x14 / 4;
pub mod SRRCTL_ {
    pub const BSIZEPACKET: u32 = 0b0001_1111;
    pub const DROP_EN: u32 = 1 << 28;
}

pub const DCARXCTRL: usize = 0x0C / 4;
pub mod DCARXCTRL_ {
    pub const UNKNOWN: u32 = 1 << 12; // This bit is reserved, has no name, but must be used anyway
}

// --- TX ---

pub fn TX_ZONE_BASE(n: usize) -> usize {
    (0x06000 + 0x40 * n) / 4
}
pub const TX_ZONE_LEN: usize = 0x40;

pub const DCATXCTRL: usize = 0x0C / 4;
pub mod DCATXCTRL_ {
    pub const TX_DESC_WB_RO_EN: u32 = 1 << 11;
}

pub const TDBAH: usize = 0x04 / 4;

pub const TDBAL: usize = 0x00 / 4;

pub const TDLEN: usize = 0x08 / 4;

pub const TDT: usize = 0x18 / 4;

pub const TDWBAH: usize = 0x3C / 4;

pub const TDWBAL: usize = 0x38 / 4;

pub const TXDCTL: usize = 0x28 / 4;
pub mod TXDCTL_ {
    pub const PTHRESH: u32 = 0b0111_1111;
    pub const HTHRESH: u32 = 0b0111_1111_0000_0000;
    pub const ENABLE: u32 = 1 << 25;
}
