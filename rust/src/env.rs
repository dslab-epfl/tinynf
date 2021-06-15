use std::time::Duration;

use crate::pci::PciAddress;

pub trait Environment {
    fn allocate<T>(&self, size: usize) -> &mut [T];
    fn map_physical_memory<T>(&self, addr: u64, size: usize) -> &mut [T];
    fn get_physical_address<T: ?Sized>(&self, value: &mut T) -> usize;

    fn pci_read(&self, addr: PciAddress, register: u8) -> u32;
    fn pci_write(&self, addr: PciAddress, register: u8, value: u32);

    fn sleep(&self, duration: Duration);
}
