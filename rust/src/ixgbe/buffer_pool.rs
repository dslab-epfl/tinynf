use crate::PacketData;
use crate::env::Environment;

pub struct Buffer<'a> {
    data: &'a mut PacketData,
    phys_addr: usize,
    length: u16,
}

pub struct BufferPool<'a> {
    buffers: &'a mut [Box<Buffer<'a>>],
    index: usize,
}

impl<'a> BufferPool<'a> {
    pub fn allocate(env: &'a impl Environment<'a>, size: usize) -> BufferPool<'a> {
        let buffers = env.allocate_slice::<Box<Buffer<'a>>>(size);
        let buffers_data = env.allocate_slice::<PacketData>(size);
        let mut n = 0;
        for data in buffers_data {
            let phys_addr = env.get_physical_address(data);
            buffers[n] = Box::new(Buffer { data: data, phys_addr: phys_addr, length: 0 });
            n = n + 1;
        }

        BufferPool {
            buffers: buffers,
            index: size.wrapping_sub(1)
        }
    }

    pub fn give(&mut self, buffer: Box<Buffer<'a>>) -> bool {
        self.index = self.index.wrapping_add(1);
        if self.index < self.buffers.len() {
            self.buffers[self.index] = buffer;
            return true;
        }

        self.index = self.index.wrapping_sub(1);
        return false;
    }

    // Note that Rust has some compiler support for representing "None" as NULL for Options of pointers, avoiding overhead
    pub fn take(&mut self) -> Option<Box<Buffer<'a>>> {
        if self.index < self.buffers.len() {
            let result = self.buffers[self.index];
            self.index = self.index.wrapping_add(1);
            return Some(result);
        }

        return None;
    }
}
