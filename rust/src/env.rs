use std::time::Duration;
use std::thread;

use libc::ioperm;
use x86_64::instructions::port::Port;

use crate::pci::PciAddress;

pub trait Environment {
    fn allocate<T, const COUNT: usize>(&self) -> &mut [T; COUNT];
    fn allocate_slice<T>(&self, count: usize) -> &mut [T];
    fn map_physical_memory<T>(&self, addr: u64, size: usize) -> &mut [T];
    fn get_physical_address<T: ?Sized>(&self, value: &mut T) -> usize;

    fn pci_read(&self, addr: PciAddress, register: u8) -> u32;
    fn pci_write(&self, addr: PciAddress, register: u8, value: u32);

    fn sleep(&self, duration: Duration);
}


const PCI_CONFIG_ADDR: u16 = 0xCF8;
const PCI_CONFIG_DATA: u16 = 0xCFC;

fn port_out_32(port: u16, value: u32) {
    if ioperm(port.into(), 4, 1) < 0 || ioperm(0x80, 1, 1) < 0 {
        panic!("Could not ioperm, are you root?");
    }
    Port::new(port).write(value);
    Port::new(0x80).write(0u8);
}

fn port_in_32(port: u16) -> u32 {
    if ioperm(port.into(), 4, 1) < 0 {
        panic!("Could not ioperm, are you root?");
    }
    Port::new(port).read()
}

fn pci_target(address: PciAddress, register: u8) {
    port_out_32(PCI_CONFIG_ADDR, 0x80000000 | ((address.bus as u32) << 16) | ((address.device as u32) << 11) | ((address.function as u32) << 8) | register as u32);
}


pub struct LinuxEnvironment {}

impl Environment for LinuxEnvironment {
     fn pci_read(&self, addr: PciAddress, register: u8) -> u32 {
         pci_target(addr, register);
         port_in_32(PCI_CONFIG_DATA)
     }

     fn pci_write(&self, addr: PciAddress, register: u8, value: u32) {
         pci_target(addr, register);
         port_out_32(PCI_CONFIG_DATA, value);
     }

    fn sleep(&self, duration: Duration) {
        thread::sleep(duration);
    }
}
