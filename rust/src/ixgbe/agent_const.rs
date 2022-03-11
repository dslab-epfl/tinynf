use crate::env::Environment;
use crate::lifed::{LifedArray, LifedPtr};

use super::device::{Descriptor, Device, PacketData, TransmitHead, RING_SIZE};

const FLUSH_PERIOD: u8 = 8;
const RECYCLE_PERIOD: u8 = 64;

pub struct AgentConst<'a, const OUTPUTS: usize> {
    packets: &'a mut [PacketData; RING_SIZE],
    receive_tail: LifedPtr<'a, u32>,
    rings: &'a mut [LifedArray<'a, Descriptor, { RING_SIZE }>; OUTPUTS],
    transmit_heads: LifedArray<'a, TransmitHead, { OUTPUTS }>,
    transmit_tails: &'a mut [LifedPtr<'a, u32>; OUTPUTS],
    outputs: &'a mut [u64; OUTPUTS],
    process_delimiter: u8,
}

impl<'a, const OUTPUTS: usize> AgentConst<'a, OUTPUTS> {
    pub fn create(env: &impl Environment<'a>, input: &Device<'a>, outputs: [&Device<'a>; OUTPUTS]) -> AgentConst<'a, OUTPUTS> {
        let packets = env.allocate::<PacketData, { RING_SIZE }>();

        let rings = env.allocate::<LifedArray<'a, Descriptor, { RING_SIZE }>, { OUTPUTS }>();
        for r in 0..rings.len() {
            rings[r] = LifedArray::new(env.allocate::<Descriptor, { RING_SIZE }>());
        }
        for n in 0..RING_SIZE {
            let packet_phys_addr = u64::to_le(env.get_physical_address(&mut packets[n as usize]) as u64);
            for r in 0..OUTPUTS {
                rings[r].index(n as usize).write_volatile_part(packet_phys_addr, |d| { &mut d.addr });
            }
        }

        let receive_tail = input.add_input(env, rings[0].index(0));

        let transmit_heads = LifedArray::new(env.allocate::<TransmitHead, { OUTPUTS }>());
        let transmit_tails = env.allocate::<LifedPtr<'a, u32>, { OUTPUTS }>();
        let mut t = 0;
        for out in outputs {
            transmit_tails[t] = out.add_output(env, rings[t].index(0), transmit_heads.index(t));
            t = t + 1;
        }

        AgentConst {
            packets,
            receive_tail,
            rings,
            transmit_heads,
            transmit_tails,
            outputs: env.allocate::<u64, { OUTPUTS }>(),
            process_delimiter: 0,
        }
    }

    #[inline(always)]
    pub fn run(&mut self, processor: fn(&mut PacketData, u64, &mut [u64; OUTPUTS])) {
        let mut n: u8 = 0;
        while n < FLUSH_PERIOD {
            let receive_metadata = u64::from_le(self.rings[0].index(self.process_delimiter as usize).read_volatile_part(|d| { &d.metadata }));
            if (receive_metadata & (1 << 32)) == 0 {
                break;
            }

            let length = receive_metadata & 0xFFFF;
            processor(&mut self.packets[self.process_delimiter as usize], length, self.outputs);

            let rs_bit: u64 = if self.process_delimiter % RECYCLE_PERIOD == (RECYCLE_PERIOD - 1) { 1 << (24 + 3) } else { 0 };
            for o in 0..OUTPUTS {
                self.rings[o].index(self.process_delimiter as usize).write_volatile_part(
                    u64::to_le(self.outputs[o] | rs_bit | (1 << (24 + 1)) | (1 << 24)),
                    |d| { &mut d.metadata }
                );
                self.outputs[o] = 0;
            }

            self.process_delimiter += 1;

            if rs_bit != 0 {
                let mut earliest_transmit_head = self.process_delimiter as u32;
                let mut min_diff = u64::MAX;
                for h in 0..OUTPUTS {
                    let head_value = u32::from_le(self.transmit_heads.index(h).read_volatile_part(|h| { &h.value }));
                    let diff = (head_value as u64).wrapping_sub(self.process_delimiter as u64);
                    if diff <= min_diff {
                        earliest_transmit_head = head_value;
                        min_diff = diff;
                    }
                }

                self.receive_tail.write_volatile(u32::to_le(earliest_transmit_head.wrapping_sub(1) % RING_SIZE as u32));
            }
            n += 1;
        }
        if n != 0 {
            for tail in self.transmit_tails.into_iter() {
                tail.write_volatile(u32::to_le(self.process_delimiter as u32));
            }
        }
    }
}
