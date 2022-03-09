use crate::device::{Descriptor, TransmitHead, RING_SIZE};
use crate::buffer_pool::{Buffer, BufferPool};

struct QueueRx<'a> {
    ring: &'a mut [Descriptor; RING_SIZE],

    receive_tail: &'a mut u32,
    next: u8,
}
