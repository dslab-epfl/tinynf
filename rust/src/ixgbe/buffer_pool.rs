use crate::PacketData;
use crate::env::Environment;

pub struct Buffer<'a> {
    data: &'a mut PacketData,
    phys_addr: usize,
    length: u16,
}

// This implementation is doing what the C impl does manually: a bounded stack.
// (Internally, Rust's Vec type is a (data ptr, capacity, length) triple)

pub struct BufferPool<'a> {
    buffers: Vec<&'a mut Buffer<'a>>,
}

impl<'a> BufferPool<'a> {
    pub fn allocate(env: &'a impl Environment<'a>, size: usize) -> BufferPool<'a> {
        let mut buffers = Vec::with_capacity(size);
        let buffers_data = env.allocate_slice::<PacketData>(size);
        let mut n = 0;
        for data in buffers_data {
            let phys_addr = env.get_physical_address(data);
            // allocate the data and then just keep it around forever :-)
            buffers[n] = Box::leak(Box::new(Buffer { data: data, phys_addr: phys_addr, length: 0 }));
            n = n + 1;
        }

        BufferPool {
            buffers: buffers
        }
    }

    pub fn give(&mut self, buffer: &'a mut Buffer<'a>) -> bool {
        if self.buffers.len() < self.buffers.capacity() {
            self.buffers.push(buffer);
            return true;
        }
        return false;
    }

    // Note that Rust has some compiler support for representing "None" as NULL for Options of pointers, avoiding overhead
    pub fn take(&mut self) -> Option<&'a mut Buffer<'a>> {
        return self.buffers.pop();
    }
}
