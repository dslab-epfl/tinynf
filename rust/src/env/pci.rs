use x86_64::instructions::port::Port;

#[derive(Copy, Clone)]
pub struct PciAddress {
    pub bus: u8,
    pub device: u8,
    pub function: u8,
}

pub const PCI_CONFIG_ADDR: u16 = 0xCF8;
pub const PCI_CONFIG_DATA: u16 = 0xCFC;

pub fn port_out_32(port: u16, value: u32) {
    unsafe {
        if libc::ioperm(port.into(), 4, 1) < 0 || libc::ioperm(0x80, 1, 1) < 0 {
            panic!("Could not ioperm, are you root?");
        }
        Port::new(port).write(value);
        Port::new(0x80).write(0u8);
    }
}

pub fn port_in_32(port: u16) -> u32 {
    unsafe {
        if libc::ioperm(port.into(), 4, 1) < 0 {
            panic!("Could not ioperm, are you root?");
        }
        Port::new(port).read()
    }
}

pub fn pci_target(address: PciAddress, register: u8) {
    port_out_32(
        PCI_CONFIG_ADDR,
        0x80000000 | ((address.bus as u32) << 16) | ((address.device as u32) << 11) | ((address.function as u32) << 8) | register as u32,
    );
}
