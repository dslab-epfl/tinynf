use crate::env::Environment;
use crate::volatile;

use super::device::{Descriptor, DeviceInput, DeviceOutput, PacketData, TransmitHead, RING_SIZE};

pub const FLUSH_PERIOD: usize = 8;

pub const RECYCLE_PERIOD: u8 = 64;

pub struct Agent<'a, 'b, const OUTPUTS: usize> {
    packets: &'b mut [PacketData; RING_SIZE],
    receive_tail: &'a mut u32,
    rings: &'b mut [&'b mut [Descriptor; RING_SIZE]; OUTPUTS],
    transmit_heads: &'b [TransmitHead; OUTPUTS],
    transmit_tails: &'b mut [&'a mut u32; OUTPUTS],
    outputs: &'b mut [u16; OUTPUTS],
    process_delimiter: u8,
}

impl<'a, 'b, const OUTPUTS: usize> Agent<'a, 'b, OUTPUTS> {
    pub fn create(env: &'b impl Environment<'b>, input: &'a mut DeviceInput<'a>, outputs: [&'a mut DeviceOutput<'a>; OUTPUTS]) -> Agent<'a, 'b, OUTPUTS> {
        let packets = env.allocate::<PacketData, { RING_SIZE }>();

        let mut rings = env.allocate::<&'b mut [Descriptor; RING_SIZE], { OUTPUTS }>();
        rings[0] = env.allocate::<Descriptor, { RING_SIZE }>();
        for n in 0..RING_SIZE {
            rings[0][n as usize].buffer = u64::to_le(env.get_physical_address(&mut packets[n as usize]) as u64);
        }
        for o in 1..OUTPUTS {
            rings[o] = env.allocate::<Descriptor, { RING_SIZE }>();
            for n in 0..RING_SIZE {
                rings[o][n as usize].buffer = rings[0][n as usize].buffer;
            }
        }

        let receive_tail = input.associate(env, rings[0]);

        let transmit_heads = env.allocate::<TransmitHead, { OUTPUTS }>();

        let transmit_tails = env.allocate::<&'a mut u32, { OUTPUTS }>();
        let mut t = 0;
        for out in outputs {
            transmit_tails[t] = out.associate(env, rings[t], &mut transmit_heads[t].value);
            t = t + 1;
        }

        Agent {
            packets,
            receive_tail,
            rings,
            transmit_heads,
            transmit_tails,
            outputs: env.allocate::<u16, { OUTPUTS }>(),
            process_delimiter: 0,
        }
    }

    pub fn run(&mut self, processor: fn(&mut PacketData, u16, &mut [u16; OUTPUTS])) {
        let mut n: usize = 0;
        while n < FLUSH_PERIOD {
            let receive_metadata = u64::from_le(volatile::read(&self.rings[0][self.process_delimiter as usize].metadata));
            if (receive_metadata & (1 << 32)) == 0 {
                break;
            }

            let length = receive_metadata as u16;
            processor(&mut self.packets[self.process_delimiter as usize], length, self.outputs);

            let rs_bit: u64 = if self.process_delimiter % RECYCLE_PERIOD == (RECYCLE_PERIOD - 1) { 1 << (24 + 3) } else { 0 };
            //            let mut o: u8 = 0;
            // TODO: check?
            // I tried an explicit for n in 0..self.rings.len() but there was still a bounds check :/
            //            for r in self.rings {
            for o in 0..OUTPUTS {
                volatile::write(
                    &mut self.rings[o][self.process_delimiter as usize].metadata,
                    u64::to_le(self.outputs[o] as u64 | rs_bit | (1 << (24 + 1)) | (1 << 24)),
                );
                self.outputs[o] = 0;
                //                o += 1;
            }

            self.process_delimiter += 1;

            if rs_bit != 0 {
                let mut earliest_transmit_head = self.process_delimiter as u32;
                let mut min_diff = u64::MAX;
                for head in self.transmit_heads {
                    let head_value = u32::from_le(volatile::read(&head.value));
                    let diff = (head_value as u64).wrapping_sub(self.process_delimiter as u64);
                    if diff <= min_diff {
                        earliest_transmit_head = head_value;
                        min_diff = diff;
                    }
                }

                volatile::write(self.receive_tail, u32::to_le(earliest_transmit_head.wrapping_sub(1) % RING_SIZE as u32));
            }
            n += 1;
        }
        if n != 0 {
            for tail in self.transmit_tails.into_iter() {
                volatile::write(*tail, u32::to_le(self.process_delimiter as u32));
            }
        }
    }
}
