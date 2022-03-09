use std::marker::PhantomData;
use std::ptr::NonNull;

use crate::lifed_ptr::LifedPtr;

pub struct LifedSlice<'a, T: ?Sized + Copy> {
    ptr: NonNull<T>,
    len: usize,
    _lifetime: PhantomData<&'a mut [T]>,
}

impl<'a, T: ?Sized + Copy> LifedSlice<'a, T> {
    pub fn new(src: &'a mut [T]) -> LifedSlice<'a, T> {
        let nonnull_src = NonNull::new(src.as_mut_ptr()).unwrap();
        LifedSlice {
            ptr: nonnull_src,
            len: src.len(),
            _lifetime: PhantomData
        }
    }

    fn index(&self, index: usize) -> LifedPtr<'a, T> {
        if index < self.len {
            // Safe because we just checked the index (no >=0, it's unsigned) and the value must be valid for the lifetime 'a
            unsafe {
                let ptr = self.ptr.as_ptr().offset(index as isize);
                LifedPtr::new(&mut *ptr)
            }
        } else {
            panic!("Out of bounds")
        }
    }
}
