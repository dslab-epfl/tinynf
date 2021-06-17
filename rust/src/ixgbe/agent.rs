use crate::env::Environment;
use crate::volatile;

use super::descriptor::Descriptor;
use super::device::{DeviceInput, DeviceOutput};
use super::driver_constants;
use super::transmit_head::TransmitHead;
use super::MAX_OUTPUTS;
use super::PACKET_SIZE;

pub struct Agent<'a> {
    packets: &'a mut [[u8; PACKET_SIZE]; driver_constants::RING_SIZE],
    first_ring: &'a mut [Descriptor; driver_constants::RING_SIZE],
    receive_tail: &'a mut u32,
    other_rings: Vec<&'a mut [Descriptor; driver_constants::RING_SIZE]>,
    transmit_heads: &'a [TransmitHead],
    transmit_tails: Vec<&'a mut u32>,
    outputs: &'a mut [u16; MAX_OUTPUTS],
    process_delimiter: u8,
}

impl Agent<'_> {
    pub fn create<'a, 'b>(env: &'b mut impl Environment, input: &'a mut DeviceInput<'_>, outputs: &'a mut [&'a mut DeviceOutput<'_>]) -> Agent<'a> {
        if outputs.len() > MAX_OUTPUTS {
            panic!("Too many outputs");
        }

        let packets = env.allocate::<[u8; PACKET_SIZE], { driver_constants::RING_SIZE }>();

        let first_ring = env.allocate::<Descriptor, { driver_constants::RING_SIZE }>();
        for n in 0..driver_constants::RING_SIZE {
            first_ring[n as usize].buffer = u64::to_le(env.get_physical_address(&mut packets[n as usize]) as u64);
        }

        let mut other_rings = Vec::new();
        for _n in 0..outputs.len() - 1 {
            other_rings.push(env.allocate::<Descriptor, { driver_constants::RING_SIZE }>());
        }
        for ring in other_rings.iter_mut() {
            for n in 0..driver_constants::RING_SIZE {
                ring[n as usize].buffer = first_ring[n as usize].buffer;
            }
        }

        let receive_tail = input.associate(env, first_ring);

        let transmit_heads = env.allocate_slice::<TransmitHead>(outputs.len());

        let mut transmit_tails = Vec::new();
        for out in outputs.iter_mut() {
            let n = transmit_tails.len();
            transmit_tails.push(out.associate(env, if n == 0 { first_ring } else { other_rings[n - 1] }, &mut transmit_heads[n].value));
        }

        Agent {
            packets,
            first_ring,
            receive_tail,
            other_rings,
            transmit_heads,
            transmit_tails,
            outputs: env.allocate::<u16, { MAX_OUTPUTS }>(),
            process_delimiter: 0,
        }
    }

    pub fn run(&mut self, processor: fn(&mut [u8; PACKET_SIZE], u16, &mut [u16; MAX_OUTPUTS])) {
        let mut n: usize = 0;
        let needs_flushing = loop {
            if n == driver_constants::FLUSH_PERIOD {
                break true;
            }

            let receive_metadata = u64::from_le(volatile::read(&self.first_ring[self.process_delimiter as usize].metadata));
            if (receive_metadata & (1 << 32)) == 0 {
                break n != 0;
            }

            let length = receive_metadata as u16;
            processor(&mut self.packets[self.process_delimiter as usize], length, self.outputs);
            print!("Got packet, length = {}, output length = {}\n", length, self.outputs[0]);

            let rs_bit: u64 = if self.process_delimiter % driver_constants::RECYCLE_PERIOD == (driver_constants::RECYCLE_PERIOD - 1) {
                1 << 24 + 3
            } else {
                0
            };
            // This is rather awkward, we can't have transmit_rings[0] as the "main" ring because then we'd incur a bounds check when using it for RX,
            // but we also can't have a reference to transmit_rings[0] to use without a bounds check since we'd then have one mut ref inside transmit_rings and another ref for reading
            // which is illegal, so... we use first_ring separately and copy the code
            volatile::write(
                &mut self.first_ring[self.process_delimiter as usize].metadata,
                u64::to_le(self.outputs[0] as u64 | (1 << 24 + 1) | (1 << 24) | rs_bit),
            );
            self.outputs[0] = 0;
            let mut o: u8 = 1;
            for r in &mut self.other_rings { // I tried an explicit for n in 0..self.other_rings.len() but there was still a bounds check :/
                volatile::write(
                    &mut r[self.process_delimiter as usize].metadata,
                    u64::to_le(self.outputs[o as usize] as u64 | (1 << 24 + 1) | (1 << 24) | rs_bit),
                );
                self.outputs[o as usize] = 0;
                o = o + 1;
            }

            self.process_delimiter = self.process_delimiter + 1;

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

                volatile::write(self.receive_tail, u32::to_le((earliest_transmit_head - 1) % driver_constants::RING_SIZE as u32));
                print!("rx tail, which is at {:p}, is now {}\n", self.receive_tail, volatile::read(self.receive_tail));
            }
            n = n + 1;
        };
        if needs_flushing {
            for tail in self.transmit_tails.iter_mut() {
                volatile::write(*tail, u32::to_le(self.process_delimiter as u32));
                print!("tail, which is at {:p}, is now {}\n", *tail, volatile::read(*tail));
                unsafe {
                    let hd = (*tail as *mut u32).sub(2);
                    print!("corresponding head, at {:p}, is now {}\n", hd, *hd);
                }
            }
        }
    }
}
