use std::marker::PhantomData;
use std::ptr;
use std::ptr::NonNull;

use crate::env::Environment;

// All unsafe{} blocks in the impls are safe because the ptr must be valid over lifetime 'a
#[derive(Clone, Copy)]
pub struct LifedPtr<'a, T: ?Sized> {
    ptr: NonNull<T>,
    _lifetime: PhantomData<&'a mut T>,
}

impl <'a, T: ?Sized> LifedPtr<'a, T> {
    #[inline(always)]
    pub fn new(src: &'a mut T) -> LifedPtr<'a, T> {
        let nonnull_src = NonNull::new(src).unwrap(); // must succeed since src is a ref not a ptr and thus cannot be null
        LifedPtr {
            ptr: nonnull_src,
            _lifetime: PhantomData
        }
    }

    // Safe IFF the pointer is non-null and valid for the lifetime 'a
    #[inline(always)]
    fn new_unchecked(src: *mut T) -> LifedPtr<'a, T> {
        unsafe { LifedPtr { ptr: NonNull::new_unchecked(src), _lifetime: PhantomData } }
    }

    // otherwise `instance.read_volatile().field` loads the whole `instance`
    #[inline(always)]
    pub fn read_volatile_part<U: Copy>(&self, f: fn(&T) -> &U) -> U {
        unsafe {
            ptr::read_volatile(f(self.ptr.as_ref()))
        }
    }

    #[inline(always)]
    pub fn write_volatile_part<U: Copy>(&self, value: U, f: fn(&mut T) -> &mut U) {
        unsafe {
            ptr::write_volatile(f(&mut *self.ptr.as_ptr()), value);
        }
    }
}

impl <'a, T> LifedPtr<'a, T> {
    pub fn get_physical_address(&self, env: &impl Environment<'a>) -> usize {
        env.get_physical_address(self.ptr.as_ptr())
    }
}

impl<'a, T: Copy> LifedPtr<'a, T> {
// These are not needed in practice, even during init we need the _part ones for the agent
/*    #[inline(always)]
    pub fn read(&self) -> T {
        unsafe {
            *self.ptr.as_ptr()
        }
    }

    #[inline(always)]
    pub fn write(&self, value: T) {
        unsafe {
            *self.ptr.as_ptr() = value
        }
    }
*/
    #[inline(always)]
    pub fn read_volatile(&self) -> T {
        unsafe {
            ptr::read_volatile(self.ptr.as_ptr())
        }
    }

    #[inline(always)]
    pub fn write_volatile(&self, value: T) {
        unsafe {
            ptr::write_volatile(self.ptr.as_ptr(), value);
        }
    }
}


pub struct LifedArray<'a, T, const N: usize> {
    ptr: NonNull<T>,
    _lifetime: PhantomData<&'a mut T>,
}

impl<'a, T, const N: usize> LifedArray<'a, T, N> {
    pub fn new(src: &'a mut [T; N]) -> LifedArray<'a, T, N> {
        let nonnull_src = NonNull::new(src.as_mut_ptr()).unwrap();
        LifedArray {
            ptr: nonnull_src,
            _lifetime: PhantomData
        }
    }

    #[inline(always)]
    pub fn index(&self, index: usize) -> LifedPtr<'a, T> {
        if index < N {
            // Safe because we just checked the index (no >=0, it's unsigned) and the value must be valid for the lifetime 'a
            unsafe {
                let ptr = self.ptr.as_ptr().offset(index as isize);
                LifedPtr::new_unchecked(ptr)
            }
        } else {
            panic!("Out of bounds")
        }
    }
}
// Manually derive these as using #[derive] doesn't work if T isn't Clone even though this does not matter here
impl<'a, T, const N: usize> Clone for LifedArray<'a, T, N> {
    fn clone(&self) -> Self {
        LifedArray { ptr: self.ptr, _lifetime: self._lifetime }
    }
    fn clone_from(&mut self, source: &Self) {
        self.ptr = source.ptr
    }
}
impl<'a, T, const N: usize> Copy for LifedArray<'a, T, N> { }


#[derive(Clone, Copy)]
pub struct LifedSlice<'a, T> {
    ptr: NonNull<T>,
    len: usize,
    _lifetime: PhantomData<&'a mut T>,
}

impl<'a, T> LifedSlice<'a, T> {
    pub fn new(src: &'a mut [T]) -> LifedSlice<'a, T> {
        let nonnull_src = NonNull::new(src.as_mut_ptr()).unwrap();
        LifedSlice {
            ptr: nonnull_src,
            len: src.len(),
            _lifetime: PhantomData
        }
    }

    #[inline(always)]
    pub fn len(&self) -> usize {
        self.len
    }

    #[inline(always)]
    pub fn index(&self, index: usize) -> LifedPtr<'a, T> {
        if index < self.len {
            // Safe because we just checked the index (no >=0, it's unsigned) and the value must be valid for the lifetime 'a
            unsafe {
                let ptr = self.ptr.as_ptr().offset(index as isize);
                LifedPtr::new_unchecked(ptr)
            }
        } else {
            panic!("Out of bounds")
        }
    }
}

impl<'a, T: Copy> LifedSlice<'a, T> {
    #[inline(always)]
    pub fn get(&self, index: usize) -> T {
        if index < self.len {
            // Safe for the same reason as above
            unsafe {
                *self.ptr.as_ptr().offset(index as isize)
            }
        } else {
            panic!("Out of bounds")
        }
    }

    #[inline(always)]
    pub fn set(&self, index: usize, value: T) {
        if index < self.len {
            // Safe for the same reason as above
            unsafe {
                *self.ptr.as_ptr().offset(index as isize) = value
            }
        } else {
            panic!("Out of bounds")
        }
    }
}
