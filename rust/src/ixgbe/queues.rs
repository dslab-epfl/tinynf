use crate::env::Environment;
use crate::lifed::{LifedArray, LifedPtr};

use super::device::{Device, Descriptor, TransmitHead, RING_SIZE};
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
}
