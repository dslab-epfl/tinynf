mod env;
mod pci;

mod ixgbe;
use ixgbe::pci_regs;
use ixgbe::regs;
use ixgbe::driver_constants;
use ixgbe::device_limits;
use ixgbe::transmit_head;

#[derive(Debug, Copy, Clone)] // todo remove
struct Descriptor {
    pub buffer: u64,
    pub metadata: u64
}
#[derive(Debug, Copy, Clone)] // todo remove
struct TransmitHead {
    pub value: u32,
    pub padding: [u32; 15] // on its own cache line
}
#[derive(Debug, Copy, Clone)] // todo remove
struct PacketData {
    pub data: [u8; 2048]
}

struct Agent<'a> {
    packets: &'a mut [PacketData; 256],
    ring: &'a mut [Descriptor; 256],
    receive_tail: &'a mut u32,
    transmit_heads: Vec<TransmitHead>,
    transmit_tails: Vec<&'a mut u32>,
    process_delimiter: u8
}

impl Agent<'_> {
    pub fn run(mut self, processor: fn(&mut PacketData, usize) -> usize) {
        let mut n: usize = 0;
        let needs_flushing = loop {
            if n >= 8 {
                break true;
            }
            
            let receive_metadata: u64 = self.ring[self.process_delimiter as usize].metadata;
            if (receive_metadata & (1 << 32)) == 0 {
                break n != 0;
            }
            
            let length: usize = (receive_metadata & 0xFFFF) as usize;
            let transmit_length: usize = processor(&mut self.packets[self.process_delimiter as usize], length);
            
            let rs_bit: u64 = if self.process_delimiter % 64 == 63 { 1 << 24+3 } else { 0 };
            self.ring[self.process_delimiter as usize].metadata = transmit_length as u64 | (1 << 24+1) | (1 << 24) | rs_bit;

            if rs_bit != 0 {
                let mut earliest_transmit_head = self.process_delimiter as u32;
                let mut min_diff = 0xFF_FF_FF_FF_FF_FF_FF_FF;
                for head_ref in &self.transmit_heads {
                    let head = head_ref.value;
                    let diff = head as u64 - self.process_delimiter as u64;
                    if diff <= min_diff {
                        earliest_transmit_head = head;
                        min_diff = diff;
                    }
                }
                
                *self.receive_tail = (earliest_transmit_head - 1) % 256;
            }
            n = n + 1;
        };
        if needs_flushing {
            for tail_ref in self.transmit_tails {
                *tail_ref = self.process_delimiter as u32;
            }
        }
    }
}

fn proc(data: &mut PacketData, size: usize) -> usize {
    if data.data[0] == 42 {
        return size;
    }
    return 0;
}

fn main() {
    let mut x: u32 = 0;
    let mut y: u32 = 0;
    let mut z: u32 = 0;
    let agent = Agent {
        packets: &mut [PacketData{ data: [0; 2048]}; 256],
        ring: &mut [Descriptor{buffer:0,metadata:0}; 256],
        receive_tail: &mut x,
        transmit_heads: vec![TransmitHead{value: 0, padding: [0;15]}],
        transmit_tails: vec![&mut z, &mut y],
        process_delimiter: 0
    };
    agent.run(proc)
}
