use crate::env::Environment;
use crate::lifed::{LifedArray, LifedPtr};

use super::device::{Descriptor, Device, PacketData, TransmitHead, RING_SIZE, RX_METADATA_DD, RX_METADATA_LENGTH, TX_METADATA_EOP, TX_METADATA_IFCS, TX_METADATA_LENGTH, TX_METADATA_RS};

const FLUSH_PERIOD: u8 = 8;
const RECYCLE_PERIOD: u8 = 64;

pub struct AgentConst<'a, const OUTPUTS: usize> {
    buffers: &'a mut [PacketData; RING_SIZE],
    rings: &'a mut [LifedArray<'a, Descriptor, { RING_SIZE }>; OUTPUTS],
    receive_tail_addr: LifedPtr<'a, u32>,
    transmit_heads: LifedArray<'a, TransmitHead, { OUTPUTS }>,
    transmit_tail_addrs: &'a mut [LifedPtr<'a, u32>; OUTPUTS],
    outputs: &'a mut [u64; OUTPUTS],
    processed_delimiter: u8,
}

impl<'a, const OUTPUTS: usize> AgentConst<'a, OUTPUTS> {
    pub fn create(env: &impl Environment<'a>, input: &Device<'a>, outputs: [&Device<'a>; OUTPUTS]) -> AgentConst<'a, OUTPUTS> {
        let buffers = env.allocate::<PacketData, { RING_SIZE }>();

        let rings = env.allocate::<LifedArray<'a, Descriptor, { RING_SIZE }>, { OUTPUTS }>();
        for r in 0..rings.len() {
            rings[r] = LifedArray::new(env.allocate::<Descriptor, { RING_SIZE }>());
        }
        for n in 0..RING_SIZE {
            let packet_phys_addr = u64::to_le(env.get_physical_address(&mut buffers[n as usize]) as u64);
            for r in 0..OUTPUTS {
                rings[r].index(n as usize).write_volatile_part(packet_phys_addr, |d| &mut d.addr);
            }
        }

        let receive_tail_addr = input.set_input(env, rings[0].index(0));

        let transmit_heads = LifedArray::new(env.allocate::<TransmitHead, { OUTPUTS }>());
        let transmit_tail_addrs = env.allocate::<LifedPtr<'a, u32>, { OUTPUTS }>();
        let mut t = 0;
        for out in outputs {
            transmit_tail_addrs[t] = out.add_output(env, rings[t].index(0), transmit_heads.index(t));
            t = t + 1;
        }

        AgentConst {
            buffers,
            receive_tail_addr,
            rings,
            transmit_heads,
            transmit_tail_addrs,
            outputs: env.allocate::<u64, { OUTPUTS }>(),
            processed_delimiter: 0,
        }
    }

    #[inline(always)]
    pub fn run(&mut self, processor: fn(&mut PacketData, u64, &mut [u64; OUTPUTS])) {
        let mut n: u8 = 0;
        while n < FLUSH_PERIOD {
            let receive_metadata = u64::from_le(self.rings[0].index(self.processed_delimiter as usize).read_volatile_part(|d| &d.metadata));
            if (receive_metadata & RX_METADATA_DD) == 0 {
                break;
            }

            let length = RX_METADATA_LENGTH(receive_metadata);
            processor(&mut self.buffers[self.processed_delimiter as usize], length, self.outputs);

            let rs_bit: u64 = if self.processed_delimiter % RECYCLE_PERIOD == (RECYCLE_PERIOD - 1) { TX_METADATA_RS } else { 0 };
            for o in 0..OUTPUTS {
                self.rings[o]
                    .index(self.processed_delimiter as usize)
                    .write_volatile_part(u64::to_le(TX_METADATA_LENGTH(self.outputs[o]) | rs_bit | TX_METADATA_IFCS | TX_METADATA_EOP), |d| &mut d.metadata);
                self.outputs[o] = 0;
            }

            self.processed_delimiter += 1;

            if rs_bit != 0 {
                let mut earliest_transmit_head = self.processed_delimiter as u32;
                let mut min_diff = u64::MAX;
                for h in 0..OUTPUTS {
                    let head_value = u32::from_le(self.transmit_heads.index(h).read_volatile_part(|h| &h.value));
                    let diff = (head_value as u64).wrapping_sub(self.processed_delimiter as u64);
                    if diff <= min_diff {
                        earliest_transmit_head = head_value;
                        min_diff = diff;
                    }
                }

                self.receive_tail_addr.write_volatile(u32::to_le(earliest_transmit_head.wrapping_sub(1) % RING_SIZE as u32));
            }
            n += 1;
        }
        if n != 0 {
            for tail in self.transmit_tail_addrs.into_iter() {
                tail.write_volatile(u32::to_le(self.processed_delimiter as u32));
            }
        }
    }
}
