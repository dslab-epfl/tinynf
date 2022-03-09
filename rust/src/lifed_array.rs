use std::marker::PhantomData;
use std::ptr::NonNull;

use crate::lifed_ptr::LifedPtr;

pub struct LifedArray<'a, T: Copy, const N: usize> {
    ptr: NonNull<T>,
    _lifetime: PhantomData<&'a mut [T; N]>,
}

impl<'a, T: Copy, const N: usize> LifedArray<'a, T, N> {
    pub fn new(src: &'a mut [T; N]) -> LifedArray<'a, T, N> {
        let nonnull_src = NonNull::new(src.as_mut_ptr()).unwrap();
        LifedArray {
            ptr: nonnull_src,
            _lifetime: PhantomData
        }
    }

    fn index(&self, index: usize) -> LifedPtr<'a, T> {
        if index < N {
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
