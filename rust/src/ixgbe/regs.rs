#![allow(non_snake_case)]
#![allow(clippy::eq_op)]
#![allow(clippy::erasing_op)]

// TODO move the /4 to match the C code for indexed regs
// TODO reorder to match the C code

use crate::lifed::LifedSlice;

// Regs are usize so they can index a slice without ceremony

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

pub const fn EIMC(n: usize) -> usize {
    (if n == 0 { 0x00888 } else { 0x00AB0 + 4 * (n - 1) }) / 4
}

pub const FCCFG: usize = 0x03D00 / 4;
pub mod FCCFG_ {
    pub const TFCE: u32 = 0b0001_1000;
}

pub const fn FCRTH(n: usize) -> usize {
    (0x03260 + 4 * n) / 4
}
pub mod FCRTH_ {
    pub const RTH: u32 = 0b0111_1111_1111_1110_0000;
}

pub const FCTRL: usize = 0x05080 / 4;
pub mod FCTRL_ {
    pub const MPE: u32 = 1 << 8;
    pub const UPE: u32 = 1 << 9;
}

pub const fn FTQF(n: usize) -> usize {
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

pub const fn MPSAR(n: usize) -> usize {
    (0x0A600 + 4 * n) / 4
}

pub const fn MTA(n: usize) -> usize {
    (0x05200 + 4 * n) / 4
}

pub const fn PFUTA(n: usize) -> usize {
    (0x0F400 + 4 * n) / 4
}

pub const fn PFVLVF(n: usize) -> usize {
    (0x0F100 + 4 * n) / 4
}

pub const fn PFVLVFB(n: usize) -> usize {
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

pub const fn RXPBSIZE(n: usize) -> usize {
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

pub const fn TXPBSIZE(n: usize) -> usize {
    (0x0CC00 + 4 * n) / 4
}

pub const fn TXPBTHRESH(n: usize) -> usize {
    (0x04950 + 4 * n) / 4
}
pub mod TXPBTHRESH_ {
    pub const THRESH: u32 = 0b11_1111_1111;
}

// --- RX ---

pub const fn RDBAL(n: usize) -> usize {
    (if n <= 63 { 0x01000 + 0x40 * n } else { 0x0D000 + 0x40 * (n - 64) }) / 4
}

pub const fn RDBAH(n: usize) -> usize {
    (if n <= 63 { 0x01004 + 0x40 * n } else { 0x0D004 + 0x40 * (n - 64) }) / 4
}

pub const fn RDLEN(n: usize) -> usize {
    (if n <= 63 { 0x01008 + 0x40 * n } else { 0x0D008 + 0x40 * (n - 64) }) / 4
}

pub const fn RDT(n: usize) -> usize {
    (if n <= 63 { 0x01018 + 0x40 * n } else { 0x0D018 + 0x40 * (n - 64) }) / 4
}

pub const fn RXDCTL(n: usize) -> usize {
    (if n <= 63 { 0x01028 + 0x40 * n } else { 0x0D028 + 0x40 * (n - 64) }) / 4
}
pub mod RXDCTL_ {
    pub const ENABLE: u32 = 1 << 25;
}

pub const fn SRRCTL(n: usize) -> usize {
    (if n <= 63 { 0x01014 + 0x40 * n } else { 0x0D014 + 0x40 * (n - 64) }) / 4
}
pub mod SRRCTL_ {
    pub const BSIZEPACKET: u32 = 0b0001_1111;
    pub const DROP_EN: u32 = 1 << 28;
}

pub const fn DCARXCTRL(n: usize) -> usize {
    (if n <= 63 { 0x0100C + 0x40 * n } else { 0x0D00C + 0x40 * (n - 64) }) / 4
}
pub mod DCARXCTRL_ {
    pub const UNKNOWN: u32 = 1 << 12; // This bit is reserved, has no name, but must be used anyway
}

// --- TX ---

pub const fn DCATXCTRL(n: usize) -> usize {
    (0x0600C + 0x40 * n) / 4
}
pub mod DCATXCTRL_ {
    pub const TX_DESC_WB_RO_EN: u32 = 1 << 11;
}

pub const fn TDBAH(n: usize) -> usize {
    (0x06004 + 0x40 * n) / 4
}

pub const fn TDBAL(n: usize) -> usize {
    (0x06000 + 0x40 * n) / 4
}

pub const fn TDLEN(n: usize) -> usize {
    (0x06008 + 0x40 * n) / 4
}

pub const fn TDT(n: usize) -> usize {
    (0x06018 + 0x40 * n) / 4
}

pub const fn TDWBAH(n: usize) -> usize {
    (0x0603C + 0x40 * n) / 4
}

pub const fn TDWBAL(n: usize) -> usize {
    (0x06038 + 0x40 * n) / 4
}

pub const fn TXDCTL(n: usize) -> usize {
    (0x06028 + 0x40 * n) / 4
}
pub mod TXDCTL_ {
    pub const PTHRESH: u32 = 0b0111_1111;
    pub const HTHRESH: u32 = 0b0111_1111_0000_0000;
    pub const ENABLE: u32 = 1 << 25;
}


pub fn read(buffer: LifedSlice<'_, u32>, reg: usize) -> u32 {
    u32::from_le(buffer.index(reg).read_volatile())
}

pub fn read_field(buffer: LifedSlice<'_, u32>, reg: usize, field: u32) -> u32 {
    let value = read(buffer, reg);
    let shift = field.trailing_zeros();
    (value & field) >> shift
}

pub fn write(buffer: LifedSlice<'_, u32>, reg: usize, value: u32) {
    buffer.index(reg).write_volatile(u32::to_le(value));
}

pub fn write_field(buffer: LifedSlice<'_, u32>, reg: usize, field: u32, field_value: u32) {
    let old_value = read(buffer, reg);
    let shift = field.trailing_zeros();
    let new_value = (old_value & !field) | (field_value << shift);
    write(buffer, reg, new_value);
}

pub fn clear(buffer: LifedSlice<'_, u32>, reg: usize) {
    write(buffer, reg, 0);
}

pub fn clear_field(buffer: LifedSlice<'_, u32>, reg: usize, field: u32) {
    write_field(buffer, reg, field, 0);
}

pub fn set_field(buffer: LifedSlice<'_, u32>, reg: usize, field: u32) {
    let old_value = read(buffer, reg);
    let new_value = old_value | field;
    write(buffer, reg, new_value);
}

pub fn is_field_cleared(buffer: LifedSlice<'_, u32>, reg: usize, field: u32) -> bool {
    read_field(buffer, reg, field) == 0
}
