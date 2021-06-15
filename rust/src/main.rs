mod env;
mod pci;
mod volatile;

mod ixgbe;
use ixgbe::agent::Agent;
use ixgbe::device::Device;

fn proc(data: &mut [u8; ixgbe::PACKET_SIZE], length: u16, output_lengths: [u16; ixgbe::MAX_OUTPUTS]) {
    if data[0] == 42 {
        output_lengths[0] = length;
    }
}

fn main() {
}
