use std::ptr;

pub fn read<T>(r: &T) -> T {
    unsafe { ptr::read_volatile(r as *const T) }
}

pub fn write<T>(r: &mut T, value: T) {
    unsafe {
        ptr::write_volatile(r as *mut T, value);
    }
}
