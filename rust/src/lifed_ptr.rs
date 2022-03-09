use std::marker::PhantomData;
use std::ptr;
use std::ptr::NonNull;

pub struct LifedPtr<'a, T: ?Sized + Copy> {
    ptr: NonNull<T>,
    _lifetime: PhantomData<&'a mut T>,
}

// All unsafe{} blocks here are safe because the ptr must be valid over lifetime 'a

impl<'a, T: ?Sized + Copy> LifedPtr<'a, T> {
    pub fn new(src: &'a mut T) -> LifedPtr<'a, T> {
        let nonnull_src = NonNull::new(src).unwrap(); // must succeed since src is a ref not a ptr and thus cannot be null
        LifedPtr {
            ptr: nonnull_src,
            _lifetime: PhantomData
        }
    }

    pub fn read(&self) -> T {
        unsafe {
            *self.ptr.as_ptr()
        }
    }

    pub fn write(&self, value: T) {
        unsafe {
            *self.ptr.as_ptr() = value
        }
    }

    pub fn read_volatile(&self) -> T {
        unsafe {
            ptr::read_volatile(self.ptr.as_ptr())
        }
    }

    pub fn write_volatile(&self, value: T) {
        unsafe {
            ptr::write_volatile(self.ptr.as_ptr(), value);
        }
    }
}
