#![allow(non_snake_case)]

pub fn read(buffer: &[u32], reg: u32) -> u32 {
    u32::from_le(buffer[reg as usize / 4])
}

pub fn read_field(buffer: &[u32], reg: u32, field: u32) -> u32 {
    let value = read(buffer, reg);
    let shift = field.trailing_zeros();
    (value & field) >> shift
}

pub fn write(buffer: &mut [u32], reg: u32, value: u32) {
    buffer[reg as usize / 4] = u32::to_le(value);
}

pub fn write_field(buffer: &mut [u32], reg: u32, field: u32, field_value: u32) {
    let old_value = read(buffer, reg);
    let shift = field.trailing_zeros();
    let new_value = (old_value & !field) | (field_value << shift);
    write(buffer, reg, new_value);
}

pub fn clear(buffer: &mut [u32], reg: u32) {
    write(buffer, reg, 0);
}

pub fn clear_field(buffer: &mut [u32], reg: u32, field: u32) {
    write_field(buffer, reg, field, 0);
}

pub fn set_field(buffer: &mut [u32], reg: u32, field: u32) {
    let old_value = read(buffer, reg);
    let new_value = old_value | field;
    write(buffer, reg, new_value);
}

pub fn is_field_cleared(buffer: &mut [u32], reg: u32, field: u32) -> bool {
    read_field(buffer, reg, field) == 0
}


pub const CTRL: u32 = 0x00000;
pub mod CTRL_ {
    pub const MASTER_DISABLE: u32 = 1 << 2;
    pub const RST: u32 = 1 << 26;
}

pub const CTRLEXT: u32 = 0x00018;
pub mod CTRLEXT_ {
    pub const NSDIS: u32 = 1 << 16;
}

pub fn DCARXCTRL(n: u32) -> u32 {
    if n <= 63 { 0x0100C + 0x40 * n } else { 0x0D00C + 0x40 * (n - 64) }
}
pub mod DCARXCTRL_ {
    pub const UNKNOWN: u32 = 1 << 12; // This bit is reserved, has no name, but must be used anyway
}

pub fn DCATXCTRL(n: u32) -> u32 {
    0x0600C + 0x40 * n
}
pub mod DCATXCTRL_ {
    pub const TX_DESC_WB_RO_EN: u32 = 1 << 11;
}

pub const DMATXCTL: u32 = 0x04A80;
pub mod DMATXCTL_ {
    pub const TE: u32 = 1 << 0;
}

pub const DTXMXSZRQ: u32 = 0x08100;
pub mod DTXMXSZRQ_ {
    pub const MAX_BYTES_NUM_REQ: u32 = 0b0111_1111_1111;
}

pub const EEC: u32 = 0x10010;
pub mod EEC_ {
    pub const EE_PRES: u32 = 1 << 8;
    pub const AUTO_RD: u32 = 1 << 9;
}

pub fn EIMC(n: u32) -> u32 {
    if n == 0 { 0x00888 } else { 0x00AB0 + 4 * (n - 1) }
}

pub const FCCFG: u32 = 0x03D00;
pub mod FCCFG_ {
    pub const TFCE: u32 = 0b0001_1000;
}

pub fn FCRTH(n: u32) -> u32 {
    0x03260 + 4 * n
}
pub mod FCRTH_ {
    pub const RTH: u32 = 0b0111_1111_1111_1110_0000;
}

pub const FCTRL: u32 = 0x05080;
pub mod FCTRL_ {
    pub const MPE: u32 = 1 << 8;
    pub const FCTRL_UPE: u32 = 1 << 9;
}

pub fn FTQF(n: u32) -> u32 {
    0x0E600 + 4 * n
}
pub mod FTQF_ {
    pub const QUEUE_ENABLE: u32 = 1 << 31;
}

pub const FWSM: u32 = 0x10148;
pub mod FWSM_ {
    pub const EXT_ERR_IND: u32 = 0b0001_1111_1000_0000_0000_0000_0000;
}

pub const GCREXT: u32 = 0x11050;
pub mod GCREXT_ {
    pub const BUFFERS_CLEAR_FUNC: u32 = 1 << 30;
}

pub const HLREG0: u32 = 0x04240;
pub mod HLREG0_ {
    pub const LPBK: u32 = 1 << 15;
}

pub const MFLCN: u32 = 0x04294;
pub mod MFLCN_ {
    pub const RFCE: u32 = 1 << 3;
}

pub fn MPSAR(n: u32) -> u32 {
     0x0A600 + 4 * n
}

pub fn MTA(n: u32) -> u32 {
     0x05200 + 4 * n
}

pub fn PFUTA(n: u32) -> u32 {
    0x0F400 + 4 * n
}

pub fn PFVLVF(n: u32) -> u32 {
    0x0F100 + 4 * n
}

pub fn PFVLVFB(n: u32) -> u32 {
    0x0F200 + 4 * n
}

pub fn RDBAH(n: u32) -> u32 {
    if n <= 63 { 0x01004 + 0x40 * n } else { 0x0D004 + 0x40 * (n - 64) }
}

pub fn RDBAL(n: u32) -> u32 {
    if n <= 63 { 0x01000 + 0x40 * n } else { 0x0D000 + 0x40 * (n - 64) }
}

pub fn RDLEN(n: u32) -> u32 {
    if n <= 63 { 0x01008 + 0x40 * n } else { 0x0D008 + 0x40 * (n - 64) }
}

pub const RDRXCTL: u32 = 0x02F00;
pub mod RDRXCTL_ {
    pub const CRC_STRIP: u32 = 1 << 1;
    pub const DMAIDONE: u32 = 1 << 3;
    pub const RSCFRSTSIZE: u32 = 0b0011_1110_0000_0000_0000_0000;
    pub const RSCACKC: u32 = 1 << 25;
    pub const FCOE_WRFIX: u32 = 1 << 26;
}

pub fn RDT(n: u32) -> u32 {
    if n <= 63 { 0x01018 + 0x40 * n } else { 0x0D018 + 0x40 * (n - 64) }
}

pub const RTTDCS: u32 = 0x04900;
pub mod RTTDCS_ {
    pub const ARBDIS: u32 = 1 << 6;
}

pub const RTTDQSEL: u32 = 0x04904;

pub const RTTDT1C: u32 = 0x04908;

pub const RXCTRL: u32 = 0x03000;
pub mod RXCTRL_ {
    pub const RXEN: u32 = 1 << 0;
}

pub fn RXDCTL(n: u32) -> u32 {
    if n <= 63 { 0x01028 + 0x40 * n } else { 0x0D028 + 0x40 * (n - 64) }
}
pub mod RXDCTL_ {
    pub const ENABLE: u32 = 1 << 25;
}

pub fn RXPBSIZE(n: u32) -> u32 {
    0x03C00 + 4 * n
}

pub const SECRXCTRL: u32 = 0x08D00;
pub mod SECRXCTRL_ {
    pub const RX_DIS: u32 = 1 << 1;
}

pub const SECRXSTAT: u32 = 0x08D04;
pub mod SECRXSTAT_ {
    pub const SECRX_RDY: u32 = 1 << 0;
}

pub fn SRRCTL(n: u32) -> u32 {
    if n <= 63 { 0x01014 + 0x40 * n } else { 0x0D014 + 0x40 * (n - 64) }
}

pub mod SRRCTL_ {
    pub const BSIZEPACKET: u32 = 0b0001_1111;
    pub const DROP_EN: u32 = 1 << 28;
}

pub const STATUS: u32 = 0x00008;
pub mod STATUS_ {
    pub const PCIE_MASTER_ENABLE_STATUS: u32 = 1 << 19;
}

pub fn TDBAH(n: u32) -> u32 {
    0x06004 + 0x40 * n
}

pub fn TDBAL(n: u32) -> u32 {
    0x06000 + 0x40 * n
}

pub fn TDLEN(n: u32) -> u32 {
    0x06008 + 0x40 * n
}

pub fn TDT(n: u32) -> u32 {
    0x06018 + 0x40 * n
}

pub fn TDWBAH(n: u32) -> u32 {
    0x0603C + 0x40 * n
}

pub fn TDWBAL(n: u32) -> u32 {
    0x06038 + 0x40 * n
}

pub fn TXDCTL(n: u32) -> u32 {
    0x06028 + 0x40 * n
}
pub mod TXDCTL_ {
    pub const PTHRESH: u32 = 0b0111_1111;
    pub const HTHRESH: u32 = 0b0111_1111_0000_0000;
    pub const ENABLE: u32 = 1 << 25;
}

pub fn TXPBSIZE(n: u32) -> u32 {
    0x0CC00 + 4 * n
}

pub fn TXPBTHRESH(n: u32) -> u32 {
    0x04950 + 4 * n
}
pub mod TXPBTHRESH_ {
    pub const THRESH: u32 = 0b11_1111_1111;
}
