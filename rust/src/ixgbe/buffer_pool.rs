use crate::env::environment::Environment;
use crate::lifed::{LifedPtr, LifedSlice};
use crate::PacketData;

pub struct Buffer<'a> {
    pub data: LifedPtr<'a, PacketData>,
    pub phys_addr: usize,
    pub length: u64,
}

pub struct BufferPool<'a> {
    buffers: LifedSlice<'a, LifedPtr<'a, Buffer<'a>>>,
    index: usize,
}

impl<'a> BufferPool<'a> {
    pub fn allocate(env: &impl Environment<'a>, size: usize) -> BufferPool<'a> {
        let buffers = env.allocate_slice::<LifedPtr<'a, Buffer<'a>>>(size);
        let buffers_data = LifedSlice::new(env.allocate_slice::<PacketData>(size));
        for n in 0..size {
            let phys_addr = buffers_data.index(n).get_physical_address(env);
            let buffer = env.allocate::<Buffer<'a>, 1>();
            buffer[0] = Buffer {
                data: buffers_data.index(n),
                phys_addr: phys_addr,
                length: 0,
            };
            buffers[n] = LifedPtr::new(&mut buffer[0]);
        }

        BufferPool {
            buffers: LifedSlice::new(buffers),
            index: size.wrapping_sub(1),
        }
    }

    pub fn give(&mut self, buffer: LifedPtr<'a, Buffer<'a>>) -> bool {
        self.index = self.index.wrapping_add(1);
        if self.index < self.buffers.len() {
            self.buffers.set(self.index, buffer);
            return true;
        }

        self.index = self.index.wrapping_sub(1);
        return false;
    }

    // Note that Rust has some compiler support for representing "None" as NULL for Options of non-null pointers, avoiding overhead
    pub fn take(&mut self) -> Option<LifedPtr<'a, Buffer<'a>>> {
        if self.index < self.buffers.len() {
            let buffer = self.buffers.get(self.index);
            self.index = self.index.wrapping_sub(1);
            return Some(buffer);
        }

        return None;
    }
}
