pub(super) mod descriptor;
pub(super) mod device_limits;
pub(super) mod driver_constants;
pub(super) mod pci_regs;
pub(super) mod regs;
pub(super) mod transmit_head;

pub const MAX_OUTPUTS: usize = driver_constants::MAX_OUTPUTS;
pub const PACKET_SIZE: usize = driver_constants::PACKET_SIZE;

pub mod agent;
pub mod device;
