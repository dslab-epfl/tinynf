use crate::env::Environment;
use crate::lifed::{LifedArray, LifedPtr};

use super::device::{Device, Descriptor, TransmitHead, RING_SIZE, RX_METADATA_DD, RX_METADATA_LENGTH};
use super::buffer_pool::{Buffer, BufferPool};

struct QueueRx<'a> {
    ring: LifedArray<'a, Descriptor, { RING_SIZE }>,
    buffers: LifedArray<'a, LifedPtr<'a, Buffer<'a>>, { RING_SIZE }>,
    pool: LifedPtr<'a, BufferPool<'a>>,
    receive_tail_addr: LifedPtr<'a, u32>,
    next: u8,
}

impl<'a> QueueRx<'a> {
    pub fn new(env: &impl Environment<'a>, device: &mut Device<'a>, pool: &'a mut BufferPool<'a>) -> QueueRx<'a> {
        let ring = LifedArray::new(env.allocate::<Descriptor, { RING_SIZE }>());
        let buffers = LifedArray::new(env.allocate::<LifedPtr<'a, Buffer<'a>>, { RING_SIZE }>());

        for n in 0..RING_SIZE {
            let buffer = pool.take().unwrap(); // panic if the pool does not have enough buffers
            ring.index(n).write_volatile_part(buffer.read_volatile_part(|d| { &d.phys_addr }) as u64, |d| { &mut d.addr });
            ring.index(n).write_volatile_part(0, |d| { &mut d.metadata });
            buffers.set(n, buffer);
        }

        let receive_tail_addr = device.add_input(env, ring.index(0));
        receive_tail_addr.write_volatile(RING_SIZE as u32 - 1);

        QueueRx {
            ring,
            buffers,
            pool: LifedPtr::new(pool),
            receive_tail_addr,
            next: 0
        }
    }

    #[inline(always)]
    pub fn batch(&mut self, buffers: &mut [LifedPtr<'a, Buffer<'a>>]) -> usize {
        let mut rx_count: usize = 0;
        while rx_count < buffers.len() {
            let metadata = u64::from_le(self.ring.index(self.next as usize).read_volatile_part(|d| { &d.metadata }));
            if (metadata & RX_METADATA_DD) == 0 {
                break;
            }

            let new_buffer = match self.pool.map(|p| {p.take()}) {
                Some(b) => b,
                None => { break; }
            };

            buffers[rx_count] = self.buffers.get(self.next as usize);
            buffers[rx_count].write_part(RX_METADATA_LENGTH(metadata), |b| { &mut b.length });

            self.buffers.set(self.next as usize, new_buffer);
            self.ring.index(self.next as usize).write_volatile(Descriptor {
                addr: u64::to_le(new_buffer.read_part(|b| { &b.phys_addr }) as u64),
                metadata: u64::to_le(0) }
            );

            self.next = self.next.wrapping_add(1); // modulo RING_SIZE implicit since it's an u8
            rx_count = rx_count.wrapping_add(1);
        }
        if rx_count > 0 {
            self.receive_tail_addr.write_volatile(u32::to_le(self.next.wrapping_sub(1) as u32)); // same, implicit modulo
        }
        rx_count
    }
}
