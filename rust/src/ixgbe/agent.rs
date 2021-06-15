use crate::env::Environment;
use crate::volatile;

use super::MAX_OUTPUTS;
use super::PACKET_SIZE;
use super::driver_constants;
use super::transmit_head::TransmitHead;
use super::descriptor::Descriptor;
use super::device::Device;


pub struct Agent<'a> {
    packets: &'a mut [[u8; PACKET_SIZE]; driver_constants::RING_SIZE as usize],
    receive_ring: &'a [Descriptor; driver_constants::RING_SIZE as usize],
    receive_tail: &'a mut u32,
    transmit_rings: &'a mut [[Descriptor; driver_constants::RING_SIZE as usize]],
    transmit_heads: &'a [TransmitHead],
    transmit_tails: &'a mut [&'a mut u32], // the slice itself must be mutable, which is weird because conceptually it isn't
    outputs: &'a mut [u16; driver_constants::MAX_OUTPUTS],
    process_delimiter: u8
}

impl Agent<'_> {
    pub fn create<'a>(env: &impl Environment, input_device: &'a mut Device, output_devices: &[&'a mut Device]) -> Agent<'a> {
        if output_devices.len() > driver_constants::MAX_OUTPUTS {
            panic!("Too many outputs");
        }
    
        let packets = env.allocate::<[u8; PACKET_SIZE], { driver_constants::RING_SIZE as usize }>();

        let rings = output_devices.map(|_| env.allocate::<[Descriptor; driver_constants::RING_SIZE], { driver_constants::RING_SIZE as usize }>()).collect();
        for ring in rings {
            for n in 0..driver_constants::RING_SIZE {
                ring[n as usize].buffer = u64::to_le(env.get_physical_address(&mut packets[n as usize]) as u64);
            }
        }
        
        let receive_tail = input_device.set_input(env, &mut rings[0]);

        let transmit_heads = env.allocate_slice(output_devices.len());

        let transmit_tails = output_devices.zip(rings).zip(transmit_heads).map(|((d, r), h)| d.add_output(env, &mut r, &mut h)).collect();

        Agent {
            packets,
            receive_ring: &rings[0],
            receive_tail,
            transmit_rings: rings,
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
            
            let receive_metadata = u64::from_le(volatile::read(&self.receive_ring[self.process_delimiter as usize].metadata));
            if (receive_metadata & (1 << 32)) == 0 {
                break n != 0;
            }
            
            let length = receive_metadata as u16;
            processor(&mut self.packets[self.process_delimiter as usize], length, self.outputs);
            
            let rs_bit: u64 = if self.process_delimiter % driver_constants::FLUSH_PERIOD == (driver_constants::FLUSH_PERIOD - 1) { 1 << 24+3 } else { 0 };
            for n in 0..self.transmit_rings.len() {
                volatile::write(&mut self.transmit_rings[n as usize][self.process_delimiter as usize].metadata, u64::to_le(self.outputs[n as u8 as usize] as u64 | (1 << 24+1) | (1 << 24) | rs_bit));
                self.outputs[n as u8 as usize] = 0;
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
                
                volatile::write(&mut self.receive_tail, u32::to_le((earliest_transmit_head - 1) % driver_constants::RING_SIZE));
            }
            n = n + 1;
        };
        if needs_flushing {
            for &mut tail in self.transmit_tails {
                volatile::write(&mut tail, u32::to_le(self.process_delimiter as u32));
            }
        }
    }
}
