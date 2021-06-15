use crate::env::Environment;
use crate::volatile;

use super::MAX_OUTPUTS;
use super::PACKET_SIZE;
use super::driver_constants;
use super::transmit_head::TransmitHead;
use super::descriptor::Descriptor;
use super::device::Device;


pub struct Agent<'a> {
    packets: &'a mut [[u8; PACKET_SIZE]; driver_constants::RING_SIZE],
    first_ring: &'a mut [Descriptor; driver_constants::RING_SIZE],
    receive_tail: &'a mut u32,
    other_rings: Vec<&'a mut [Descriptor; driver_constants::RING_SIZE]>,
    transmit_heads: &'a [TransmitHead],
    transmit_tails: Vec<&'a mut u32>,
    outputs: &'a mut [u16; driver_constants::MAX_OUTPUTS],
    process_delimiter: u8
}

impl Agent<'_> {
    pub fn create<'a>(env: &'a impl Environment, input_device: &'a mut Device, output_devices: &'a mut [&'a mut Device]) -> Agent<'a> {
        if output_devices.len() > driver_constants::MAX_OUTPUTS {
            panic!("Too many outputs");
        }
    
        let packets = env.allocate::<[u8; PACKET_SIZE], { driver_constants::RING_SIZE }>();

        let first_ring = env.allocate::<Descriptor, { driver_constants::RING_SIZE }>();
        for n in 0..driver_constants::RING_SIZE {
            first_ring[n as usize].buffer = u64::to_le(env.get_physical_address(&mut packets[n as usize]) as u64);
        }
        let mut other_rings: Vec<&'a mut [Descriptor; driver_constants::RING_SIZE]> = (0..output_devices.len()-1).map(|_| env.allocate::<Descriptor, { driver_constants::RING_SIZE }>()).collect();
        for ring in other_rings.iter_mut() {
            for n in 0..driver_constants::RING_SIZE {
                ring[n as usize].buffer = first_ring[n as usize].buffer;
            }
        }
        
        let receive_tail = input_device.set_input(env, first_ring);

        let transmit_heads = env.allocate_slice::<TransmitHead>(output_devices.len());

        let mut transmit_tails = Vec::new();
        transmit_tails.push(output_devices[0].add_output(env, first_ring, &mut transmit_heads[0].value));
        for n in 1..transmit_heads.len() {
            transmit_tails.push(output_devices[n].add_output(env, other_rings[n-1], &mut transmit_heads[n].value));
        }

        Agent {
            packets,
            first_ring,
            receive_tail,
            other_rings,
            transmit_heads,
            transmit_tails,
            outputs: env.allocate::<u16, { MAX_OUTPUTS }>(),
            process_delimiter: 0
        }
    }

    pub fn run(&mut self, processor: fn(&mut [u8; PACKET_SIZE], u16, &mut [u16; MAX_OUTPUTS])) {
        let mut n: usize = 0;
        let needs_flushing = loop {
            if n >= 8 {
                break true;
            }
            
            let receive_metadata = u64::from_le(volatile::read(&self.first_ring[self.process_delimiter as usize].metadata));
            if (receive_metadata & (1 << 32)) == 0 {
                break n != 0;
            }
            
            let length = receive_metadata as u16;
            processor(&mut self.packets[self.process_delimiter as usize], length, self.outputs);
            
            let rs_bit: u64 = if self.process_delimiter % driver_constants::FLUSH_PERIOD == (driver_constants::FLUSH_PERIOD - 1) { 1 << 24+3 } else { 0 };
            volatile::write(&mut self.first_ring[self.process_delimiter as usize].metadata, u64::to_le(self.outputs[0] as u64 | (1 << 24+1) | (1 << 24) | rs_bit));
            self.outputs[0] = 0;
            for n in 0..self.other_rings.len() {
                volatile::write(&mut self.other_rings[n as usize][self.process_delimiter as usize].metadata, u64::to_le(self.outputs[(n + 1) as u8 as usize] as u64 | (1 << 24+1) | (1 << 24) | rs_bit));
                self.outputs[(n + 1) as u8 as usize] = 0;
            }

            if rs_bit != 0 {
                let mut earliest_transmit_head = self.process_delimiter as u32;
                let mut min_diff = 0xFF_FF_FF_FF_FF_FF_FF_FF;
                for head_ref in self.transmit_heads {
                    let head = u32::from_le(volatile::read(&head_ref.value));
                    let diff = head as u64 - self.process_delimiter as u64;
                    if diff <= min_diff {
                        earliest_transmit_head = head;
                        min_diff = diff;
                    }
                }
                
                volatile::write::<u32>(&mut self.receive_tail, u32::to_le((earliest_transmit_head - 1) % driver_constants::RING_SIZE as u32));
            }
            n = n + 1;
        };
        if needs_flushing {
            for tail in self.transmit_tails.iter_mut() {
                volatile::write::<u32>(tail, u32::to_le(self.process_delimiter as u32));
            }
        }
    }
}
