use crate::env::environment::Environment;
use crate::lifed::{LifedArray, LifedPtr, LifedSlice};

use super::device::{Descriptor, Device, PacketData, TransmitHead, RING_SIZE, RX_METADATA_DD, RX_METADATA_LENGTH, TX_METADATA_EOP, TX_METADATA_IFCS, TX_METADATA_LENGTH, TX_METADATA_RS};

pub const MAX_OUTPUTS: usize = 256; // so that an u8 can index into it without bounds checks

const FLUSH_PERIOD: u8 = 8;
const RECYCLE_PERIOD: u8 = 64;

// OVERHEAD: each of these slices has the same length, but we can't state it in code
pub struct Agent<'a> {
    buffers: &'a mut [PacketData; RING_SIZE],
    rings: LifedSlice<'a, LifedArray<'a, Descriptor, { RING_SIZE }>>,
    receive_tail_addr: LifedPtr<'a, u32>,
    transmit_heads: LifedSlice<'a, TransmitHead>,
    transmit_tail_addrs: LifedSlice<'a, LifedPtr<'a, u32>>,
    outputs: &'a mut [u64; MAX_OUTPUTS],
    processed_delimiter: u8,
}

impl<'a> Agent<'a> {
    pub fn create(env: &impl Environment<'a>, input: LifedPtr<'a, Device<'a>>, outputs: &[LifedPtr<'a, Device<'a>>]) -> Agent<'a> {
        // LifedSlice requires a nonzero length, allowing us to access the shared first ring without any checks
        if outputs.len() == 0 {
            panic!("Cannot have zero outputs");
        }
        if outputs.len() >= MAX_OUTPUTS {
            panic!("Too many outputs");
        }

        let buffers = env.allocate::<PacketData, { RING_SIZE }>();

        let rings = env.allocate_slice::<LifedArray<'a, Descriptor, { RING_SIZE }>>(outputs.len());
        for r in 0..outputs.len() {
            rings[r] = LifedArray::new(env.allocate::<Descriptor, { RING_SIZE }>());
        }
        for n in 0..buffers.len() {
            let packet_phys_addr = u64::to_le(env.get_physical_address(&mut buffers[n as usize]) as u64);
            for r in 0..outputs.len() {
                rings[r].index(n as usize).write_volatile_part(packet_phys_addr, |d| &mut d.addr);
            }
        }

        let receive_tail_addr = input.map(|d| d.set_input(env, rings[0].index(0)));

        let transmit_heads = LifedSlice::new(env.allocate_slice::<TransmitHead>(outputs.len()));
        let transmit_tail_addrs = LifedSlice::new(env.allocate_slice::<LifedPtr<'a, u32>>(outputs.len()));
        for n in 0..outputs.len() {
            transmit_tail_addrs.set(n, outputs[n].map(|d| d.add_output(env, rings[n].index(0), transmit_heads.index(n))));
        }

        Agent {
            buffers,
            rings: LifedSlice::new(rings),
            receive_tail_addr,
            transmit_heads,
            transmit_tail_addrs,
            outputs: env.allocate::<u64, { MAX_OUTPUTS }>(),
            processed_delimiter: 0,
        }
    }

    #[inline(always)] // mimic C "static inline"
    pub fn run(&mut self, processor: fn(&mut PacketData, u64, &mut [u64; MAX_OUTPUTS])) {
        let mut n: u8 = 0;
        while n < FLUSH_PERIOD {
            let receive_metadata = u64::from_le(self.rings.first().index(self.processed_delimiter as usize).read_volatile_part(|d| &d.metadata));
            if (receive_metadata & RX_METADATA_DD) == 0 {
                break;
            }

            let length = RX_METADATA_LENGTH(receive_metadata);
            processor(&mut self.buffers[self.processed_delimiter as usize], length, self.outputs);

            let rs_bit: u64 = if self.processed_delimiter % RECYCLE_PERIOD == (RECYCLE_PERIOD - 1) { TX_METADATA_RS } else { 0 };
            for o in 0..self.rings.len() {
                self.rings
                    .get(o as usize)
                    .index(self.processed_delimiter as usize)
                    .write_volatile_part(u64::to_le(TX_METADATA_LENGTH(self.outputs[o as u8 as usize]) | rs_bit | TX_METADATA_IFCS | TX_METADATA_EOP), |d| {
                        &mut d.metadata
                    });
                self.outputs[o as u8 as usize] = 0;
            }

            self.processed_delimiter = self.processed_delimiter.wrapping_add(1); // modulo ring size implicit since it's an u8

            if rs_bit != 0 {
                let mut earliest_transmit_head = self.processed_delimiter as u32;
                let mut min_diff = u64::MAX;
                for h in 0..self.transmit_heads.len() {
                    let head_value = u32::from_le(self.transmit_heads.index(h).read_volatile_part(|h| &h.value));
                    let diff = (head_value as u64).wrapping_sub(self.processed_delimiter as u64);
                    if diff <= min_diff {
                        earliest_transmit_head = head_value;
                        min_diff = diff;
                    }
                }

                self.receive_tail_addr.write_volatile(u32::to_le(earliest_transmit_head));
            }
            n += 1;
        }
        if n != 0 {
            for t in 0..self.transmit_tail_addrs.len() {
                self.transmit_tail_addrs.get(t).write_volatile(u32::to_le(self.processed_delimiter as u32));
            }
        }
    }
}
