#![allow(non_snake_case)]

use crate::env::Environment;
use crate::pci::PciAddress;

pub fn read_field<'a>(env: &impl Environment<'a>, addr: PciAddress, reg: u8, field: u32) -> u32 {
    let value = env.pci_read(addr, reg);
    let shift = field.trailing_zeros();
    (value & field) >> shift
}

pub fn is_field_cleared<'a>(env: &impl Environment<'a>, addr: PciAddress, reg: u8, field: u32) -> bool {
    read_field(env, addr, reg, field) == 0
}

pub fn set_field<'a>(env: &impl Environment<'a>, addr: PciAddress, reg: u8, field: u32) {
    let old_value = env.pci_read(addr, reg);
    let new_value = old_value | field;
    env.pci_write(addr, reg, new_value);
}

pub const BAR0_LOW: u8 = 0x10;
pub const BAR0_HIGH: u8 = 0x14;

pub const COMMAND: u8 = 0x04;
pub mod COMMAND_ {
    pub const MEMORY_ACCESS_ENABLE: u32 = 1 << 1;
    pub const BUS_MASTER_ENABLE: u32 = 1 << 2;
    pub const INTERRUPT_DISABLE: u32 = 1 << 10;
}

pub const DEVICESTATUS: u8 = 0xAA;
pub mod DEVICESTATUS_ {
    pub const TRANSACTIONPENDING: u32 = 1 << 5;
}

pub const ID: u8 = 0x00;

pub const PMCSR: u8 = 0x44;
pub mod PMCSR_ {
    pub const POWER_STATE: u32 = 0b0011;
}
