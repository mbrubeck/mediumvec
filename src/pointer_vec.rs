//! A vector that is the width of a single pointer.

// Copyright 2017 Matt Brubeck.
// Licensed under the Apache License, Version 2.0 <http://www.apache.org/licenses/LICENSE-2.0> or
// the MIT license <http://opensource.org/licenses/MIT>, at your option. This file may not be
// copied, modified, or distributed except according to those terms.

use std::{cmp, mem, ops, ptr, slice};
use std::marker::PhantomData;

/// A growable vector the width of a single pointer.
///
/// `PointerVec<T>` is similar to the standard `Vec<T>` type, but it stores its length and capacity
/// fields in its heap allocation, rather than inline.  This means that the `PointerVec` struct
/// itself only has a single field, the pointer to the heap.
pub struct PointerVec<T> {
    ptr: *mut Header,
    _data: PhantomData<T>,
}

struct Header {
    cap: usize,
    len: usize,
}

impl<T> PointerVec<T> {
    /// Construct a new, empty vector.
    ///
    /// The vector will not allocate until elements are pushed onto it.
    pub fn new() -> PointerVec<T> {
        PointerVec {
            ptr: ptr::null_mut(),
            _data: PhantomData,
        }
    }

    /// Construct a new, empty (length 0) vector with the specified capacity.
    pub fn with_capacity(capacity: usize) -> PointerVec<T> {
        let ptr = Self::alloc(capacity);
        unsafe {
            ptr::write(ptr, Header { cap: capacity, len: 0 });
        }
        PointerVec {
            ptr: ptr,
            _data: PhantomData,
        }
    }

    /// Returns the number of elements in vector.
    pub fn len(&self) -> usize {
        if self.ptr.is_null() {
            0
        } else {
            unsafe { (*self.ptr).len }
        }
    }

    /// Returns the maximum number of elements the vector can hold without reallocating.
    pub fn capacity(&self) -> usize {
        if self.ptr.is_null() {
            0
        } else {
            unsafe { (*self.ptr).cap }
        }
    }

    /// Append an element to the vector.
    ///
    /// Panics if the number of elements in the vector overflows `usize`.
    pub fn push(&mut self, value: T) {
        let len = self.len();
        if len == self.capacity() {
            self.reserve(1);
        }
        unsafe {
            let end = self.as_mut_ptr().offset(len as isize);
            ptr::write(end, value);
            (*self.ptr).len += 1;
        }
    }

    /// Reserve capacity for at least `additional` more elements to be inserted.
    ///
    /// May reserve more space than requested, to avoid frequent reallocations.
    ///
    /// Panics if the new capacity overflows `usize`.
    ///
    /// Re-allocates only if `self.capacity() < self.len() + additional`.
    pub fn reserve(&mut self, additional: usize) {
        let len = self.len();
        let cap = self.capacity();

        let min_cap = len.checked_add(additional).expect("capacity overflow");
        if min_cap <= cap {
            return
        }

        let double_cap = cap.saturating_mul(2);
        let new_cap = cmp::max(min_cap, double_cap);
        let additional = new_cap - cap;
        self.reserve_exact(additional);
    }

    /// Reserves the minimum capacity for `additional` more elements to be inserted.
    ///
    /// Panics if the new capacity overflows `usize`.
    ///
    /// Re-allocates only if `self.capacity() < self.len() + additional`.
    pub fn reserve_exact(&mut self, additional: usize) {
        unimplemented!()
    }

    /// The position of the data buffer within the allocation, in bytes.
    fn buf_offset() -> usize {
        let head_size = mem::size_of::<Header>();
        let elem_align = mem::align_of::<T>();
        let padding_size = head_size % elem_align;
        head_size + padding_size
    }

    /// Allocate a buffer big enough to hold `Header` plus `count` elements of type `T`
    fn alloc(count: usize) -> *mut Header {
        let head_size = mem::size_of::<Header>();
        let elem_size = mem::size_of::<T>();
        let head_align = mem::align_of::<Header>();
        let elem_align = mem::align_of::<T>();

        let buf_bytes = count.checked_mul(elem_size).expect("capacity overflow");
        let alloc_bytes = Self::buf_offset().checked_add(buf_bytes).expect("capacity overflow");

        if head_align > elem_align {
            let mut vec = Vec::<Header>::with_capacity(div_ceil(alloc_bytes, head_size));
            let ptr = vec.as_mut_ptr();
            mem::forget(vec);
            ptr
        } else {
            let mut vec = Vec::<T>::with_capacity(div_ceil(alloc_bytes, elem_size));
            let ptr = vec.as_mut_ptr() as *mut Header;
            mem::forget(vec);
            ptr
        }
    }
}

/// `x / y` but rounded up instead of down
fn div_ceil(x: usize, y: usize) -> usize {
    1 + ((x - 1) / y)
}

impl<T> ops::Deref for PointerVec<T> {
    type Target = [T];

    fn deref(&self) -> &[T] {
        if self.ptr.is_null() {
            &[]
        } else {
            unsafe {
                let ptr = self.ptr;
                let buf = (ptr as *const u8).offset(Self::buf_offset() as isize);
                slice::from_raw_parts(buf as *const T, (*self.ptr).len)
            }
        }
    }
}

impl<T> ops::DerefMut for PointerVec<T> {
    fn deref_mut(&mut self) -> &mut [T] {
        if self.ptr.is_null() {
            &mut []
        } else {
            unsafe {
                let ptr = self.ptr;
                let buf = (ptr as *mut u8).offset(Self::buf_offset() as isize);
                slice::from_raw_parts_mut(buf as *mut T, (*self.ptr).len)
            }
        }
    }
}
