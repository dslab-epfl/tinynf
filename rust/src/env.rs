use std::convert::TryInto;
use std::io::{self, Read, Seek};
use std::fs;
use std::mem::size_of;
use std::ptr;
use std::slice;
use std::time::Duration;
use std::thread;

use libc;
use memmap;
use x86_64::instructions::port::Port;

use crate::pci::PciAddress;

// TODO might be worth splitting this file into a proper module

pub trait Environment {
    fn allocate<T, const COUNT: usize>(&mut self) -> &'static mut [T; COUNT];
    fn allocate_slice<T>(&mut self, count: usize) -> &'static mut [T];
    fn map_physical_memory<T>(&self, addr: u64, size: usize) -> &mut [T];
    fn get_physical_address<T: ?Sized>(&self, value: &mut T) -> usize;

    fn pci_read(&self, addr: PciAddress, register: u8) -> u32;
    fn pci_write(&self, addr: PciAddress, register: u8, value: u32);

    fn sleep(&self, duration: Duration);
}


// --- PCI ---

const PCI_CONFIG_ADDR: u16 = 0xCF8;
const PCI_CONFIG_DATA: u16 = 0xCFC;

fn port_out_32(port: u16, value: u32) {
    unsafe {
        if libc::ioperm(port.into(), 4, 1) < 0 || libc::ioperm(0x80, 1, 1) < 0 {
            panic!("Could not ioperm, are you root?");
        }
        Port::new(port).write(value);
        Port::new(0x80).write(0u8);
    }
}

fn port_in_32(port: u16) -> u32 {
    unsafe {
        if libc::ioperm(port.into(), 4, 1) < 0 {
            panic!("Could not ioperm, are you root?");
        }
        Port::new(port).read()
    }
}

fn pci_target(address: PciAddress, register: u8) {
    port_out_32(PCI_CONFIG_ADDR, 0x80000000 | ((address.bus as u32) << 16) | ((address.device as u32) << 11) | ((address.function as u32) << 8) | register as u32);
}


// --- Linux ---

const HUGEPAGE_LOG: usize = 30; // 1 GB hugepages
const HUGEPAGE_SIZE: usize = 1 << HUGEPAGE_LOG;

// this is a terrible idea but I don't feel like making map_physical_memory &mut self right now, too much pain for no gain in a research prototype
static mut MAPS: Vec<memmap::MmapMut> = Vec::new();

pub struct LinuxEnvironment {
    allocated_page: *mut u8,
    used_bytes: usize
}

impl LinuxEnvironment {
    pub fn new() -> LinuxEnvironment {
        unsafe {
            let page = libc::mmap(
                ptr::null_mut(),
                HUGEPAGE_SIZE,
                libc::PROT_READ | libc::PROT_WRITE,
                libc::MAP_HUGETLB | (HUGEPAGE_LOG << libc::MAP_HUGE_SHIFT) as i32 | libc::MAP_ANONYMOUS | libc::MAP_SHARED | libc::MAP_POPULATE,
                -1,
                0
            );
            if page == libc::MAP_FAILED {
                panic!("Mmap failed");
            }

            LinuxEnvironment {
                allocated_page: page as *mut u8,
                used_bytes: 0
            }
        }
    }
}

impl Environment for LinuxEnvironment {
    fn allocate<T, const COUNT: usize>(&mut self) -> &'static mut [T; COUNT] {
        self.allocate_slice(COUNT).try_into().unwrap()
    }

    fn allocate_slice<T>(&mut self, count: usize) -> &'static mut [T] {
        let mut full_size = count * size_of::<T>();
        while full_size % 64 != 0 {
            full_size = full_size + size_of::<T>();
        }

        let align_diff = self.used_bytes % full_size;
        if align_diff + self.used_bytes >= HUGEPAGE_SIZE {
            panic!("Not enough space for alignment");
        }

        unsafe {        
            self.allocated_page = self.allocated_page.add(align_diff);
        }
        self.used_bytes = self.used_bytes + align_diff;

        if full_size + self.used_bytes >= HUGEPAGE_SIZE {
            panic!("Not enough space for allocation");
        }

        let result = self.allocated_page;
        unsafe {
            self.allocated_page = self.allocated_page.add(full_size);
        }
        self.used_bytes = self.used_bytes + full_size;

        unsafe {
            slice::from_raw_parts_mut(result as *mut T, full_size)
        }
    }

    fn map_physical_memory<T>(&self, addr: u64, size: usize) -> &'static mut [T] {
        let full_size = size * size_of::<T>();
        unsafe {
            let map = memmap::MmapOptions::new().offset(addr).len(full_size).map_mut(&fs::File::open("/dev/mem").unwrap()).unwrap();
            MAPS.push(map);
            let result = &mut MAPS[MAPS.len()-1][..];
            let (_prefix, result, _suffix) = result.align_to_mut::<T>();
            result
        }
    }

    fn get_physical_address<T: ?Sized>(&self, value: &mut T) -> usize {
        unsafe {
            let page_size = libc::sysconf(libc::_SC_PAGE_SIZE) as usize;
            let addr = value as *const T as *const () as usize; // yes, the casts are necessary
            let page = addr / page_size;
            let map_offset = page * size_of::<u64>();

            let mut pagemap = fs::OpenOptions::new().read(true).open("/proc/self/pagemap").unwrap();
            pagemap.seek(io::SeekFrom::Start(map_offset as u64)).unwrap();
        
            let mut buffer = [0; size_of::<u64>()];
            pagemap.read_exact(&mut buffer).unwrap();

            let metadata = u64::from_ne_bytes(buffer);
            if (metadata & 0x8000000000000000) == 0 {
                panic!("Page not present");
            }

            let pfn = metadata & 0x7FFFFFFFFFFFFF;
            if pfn == 0 {
                panic!("Page not mapped");
            }

            let addr_offset = addr % page_size;
            pfn as usize * page_size + addr_offset
        }
    }

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
