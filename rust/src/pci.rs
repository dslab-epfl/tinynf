#[derive(Copy, Clone)]
pub struct PciAddress {
    pub bus: u8,
    pub device: u8,
    pub function: u8
}
