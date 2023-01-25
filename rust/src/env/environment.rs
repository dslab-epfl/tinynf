use std::time::Duration;

use super::pci;

pub trait Environment<'a> {
    // TODO require initialization of these T by a function, currently we expose zeroed memory
    fn allocate<T, const COUNT: usize>(&self) -> &'a mut [T; COUNT];
    fn allocate_slice<T>(&self, count: usize) -> &'a mut [T];
    fn map_physical_memory<T>(&self, addr: u64, count: usize) -> &'static mut [T]; // addr is u64, not usize, because PCI BARs are 64-bit
    fn get_physical_address<T>(&self, value: *mut T) -> usize; // mut to emphasize that gaining the phys addr might allow HW to write

    fn pci_read(&self, addr: pci::PciAddress, register: u8) -> u32;
    fn pci_write(&self, addr: pci::PciAddress, register: u8, value: u32);

    fn sleep(&self, duration: Duration);
}
