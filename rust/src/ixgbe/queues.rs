use crate::env::Environment;
use crate::lifed::{LifedArray, LifedPtr};

use super::buffer_pool::{Buffer, BufferPool};
use super::device::{Descriptor, Device, TransmitHead, RING_SIZE, RX_METADATA_DD, RX_METADATA_LENGTH, TX_METADATA_EOP, TX_METADATA_IFCS, TX_METADATA_LENGTH, TX_METADATA_RS};

pub struct QueueRx<'a> {
    ring: LifedArray<'a, Descriptor, { RING_SIZE }>,
    buffers: LifedArray<'a, LifedPtr<'a, Buffer<'a>>, { RING_SIZE }>,
    pool: LifedPtr<'a, BufferPool<'a>>,
    receive_tail_addr: LifedPtr<'a, u32>,
    next: u8,
}

impl<'a> QueueRx<'a> {
    pub fn create(env: &impl Environment<'a>, device: &Device<'a>, pool: LifedPtr<'a, BufferPool<'a>>) -> QueueRx<'a> {
        let ring = LifedArray::new(env.allocate::<Descriptor, { RING_SIZE }>());
        let buffers = LifedArray::new(env.allocate::<LifedPtr<'a, Buffer<'a>>, { RING_SIZE }>());

        for n in 0..RING_SIZE {
            let buffer = pool.map(|p| p.take()).unwrap(); // panic if the pool does not have enough buffers
            ring.index(n).write_volatile_part(buffer.read_volatile_part(|d| &d.phys_addr) as u64, |d| &mut d.addr);
            ring.index(n).write_volatile_part(0, |d| &mut d.metadata);
            buffers.set(n, buffer);
        }

        let receive_tail_addr = device.add_input(env, ring.index(0));
        receive_tail_addr.write_volatile(RING_SIZE as u32 - 1);

        QueueRx {
            ring,
            buffers,
            pool,
            receive_tail_addr,
            next: 0,
        }
    }

    #[inline(always)]
    pub fn batch(&mut self, buffers: &mut [LifedPtr<'a, Buffer<'a>>]) -> u8 {
        let mut rx_count: u8 = 0;
        while (rx_count as usize) < buffers.len() {
            let metadata = u64::from_le(self.ring.index(self.next as usize).read_volatile_part(|d| &d.metadata));
            if (metadata & RX_METADATA_DD) == 0 {
                break;
            }

            let new_buffer = match self.pool.map(|p| p.take()) {
                Some(b) => b,
                None => {
                    break;
                }
            };

            buffers[rx_count as usize] = self.buffers.get(self.next as usize);
            buffers[rx_count as usize].write_part(RX_METADATA_LENGTH(metadata), |b| &mut b.length);

            self.buffers.set(self.next as usize, new_buffer);
            self.ring.index(self.next as usize).write_volatile(Descriptor {
                addr: u64::to_le(new_buffer.map(|b| b.phys_addr) as u64),
                metadata: u64::to_le(0),
            });

            self.next = self.next.wrapping_add(1); // modulo RING_SIZE implicit since it's an u8
            rx_count = rx_count.wrapping_add(1);
        }
        if rx_count > 0 {
            // same, implicit modulo
            self.receive_tail_addr.write_volatile(u32::to_le(self.next.wrapping_sub(1) as u32));
        }
        rx_count
    }
}

const TX_RECYCLE_PERIOD: u8 = 32;

pub struct QueueTx<'a> {
    ring: LifedArray<'a, Descriptor, { RING_SIZE }>,
    buffers: LifedArray<'a, LifedPtr<'a, Buffer<'a>>, { RING_SIZE }>,
    pub pool: LifedPtr<'a, BufferPool<'a>>,
    transmit_head_addr: LifedPtr<'a, TransmitHead>,
    transmit_tail_addr: LifedPtr<'a, u32>,
    recycled_head: u8,
    next: u8,
}

impl<'a> QueueTx<'a> {
    pub fn create(env: &impl Environment<'a>, device: &Device<'a>, pool: LifedPtr<'a, BufferPool<'a>>) -> QueueTx<'a> {
        let ring = LifedArray::new(env.allocate::<Descriptor, { RING_SIZE }>());
        let transmit_head_addr = LifedPtr::new(&mut env.allocate::<TransmitHead, 1>()[0]);
        QueueTx {
            ring,
            buffers: LifedArray::new(env.allocate::<LifedPtr<'a, Buffer<'a>>, { RING_SIZE }>()),
            pool,
            transmit_head_addr,
            transmit_tail_addr: device.add_output(env, ring.index(0), transmit_head_addr),
            recycled_head: 0,
            next: 0,
        }
    }

    #[inline(always)]
    pub fn batch(&mut self, buffers: &mut [LifedPtr<'a, Buffer<'a>>]) -> u8 {
        if self.next.wrapping_sub(self.recycled_head) >= 2 * TX_RECYCLE_PERIOD {
            let actual_transmit_head = self.transmit_head_addr.read_volatile_part(|h| &h.value);
            while self.recycled_head as u32 != actual_transmit_head {
                if !self.pool.map(|p| p.give(self.buffers.get(self.recycled_head as usize))) {
                    break;
                }
                self.recycled_head = self.recycled_head.wrapping_add(1); // implicit modulo RING_SIZE, u8
            }
        }

        let mut tx_count: u8 = 0;
        while (tx_count as usize) < buffers.len() {
            if self.next == self.recycled_head.wrapping_sub(1) {
                break;
            }

            let rs_bit = if (self.next % TX_RECYCLE_PERIOD) == TX_RECYCLE_PERIOD - 1 { TX_METADATA_RS } else { 0 };
            self.ring.index(self.next as usize).write_volatile(Descriptor {
                addr: u64::to_le(buffers[tx_count as usize].map(|b| b.phys_addr) as u64),
                metadata: u64::to_le(TX_METADATA_LENGTH(buffers[tx_count as usize].map(|b| b.length)) | rs_bit | TX_METADATA_IFCS | TX_METADATA_EOP),
            });

            self.buffers.set(self.next as usize, buffers[tx_count as usize]);

            self.next = self.next.wrapping_add(1); // implicit modulo
            tx_count = tx_count.wrapping_add(1);
        }
        if tx_count > 0 {
            self.transmit_tail_addr.write_volatile(u32::to_le(self.next as u32));
        }
        tx_count
    }
}
