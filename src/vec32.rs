//! A vector that is indexed by `u32` instead of `usize`.

// Copyright 2017 Matt Brubeck.  Copyright 2014 The Rust Project Developers. See the COPYRIGHT file
// at the top-level directory of this distribution and at http://rust-lang.org/COPYRIGHT.
//
// Licensed under the Apache License, Version 2.0 <http://www.apache.org/licenses/LICENSE-2.0> or
// the MIT license <http://opensource.org/licenses/MIT>, at your option. This file may not be
// copied, modified, or distributed except according to those terms.

#![allow(clippy::identity_conversion)]

use std::convert::TryFrom;
use std::ptr::NonNull;
use std::{cmp, fmt, iter, mem, ops, ptr, slice, vec};

#[cfg(not(any(
    target_pointer_width = "16",
    target_pointer_width = "32",
    target_pointer_width = "64"
)))]
compile_error!("target_pointer_width must be 16, 32, or 64");

#[cfg(target_pointer_width = "16")]
#[allow(non_camel_case_types)]
type usize32 = u16;

#[cfg(not(target_pointer_width = "16"))]
#[allow(non_camel_case_types)]
type usize32 = u32;

/// A vector that is indexed by `u32` instead of `usize`.
///
/// On 16-bit and 32-bit platforms, `Vec32<T>` is mostly identical to the standard library `Vec<T>`.
///
/// On 64-bit platforms, the `Vec32<T>` struct takes up less space than the standard `Vec<T>`
/// struct (16 bytes instead of 24 bytes), but its maximum capacity is `u32::MAX` instead of
/// `usize::MAX`.
///
/// Only 16-bit, 32-bit, and 64-bit platforms are currently supported.
///
/// ## Warning
///
/// This type has not been rigorously tested on 16-bit platforms.
///
/// ## Examples
///
/// ```
/// use mediumvec::Vec32;
///
/// let mut vec = Vec32::new();
/// vec.push(1);
/// vec.push(2);
///
/// assert_eq!(vec.len(), 2);
/// assert_eq!(vec[0], 1);
///
/// assert_eq!(vec.pop(), Some(2));
/// assert_eq!(vec.len(), 1);
///
/// vec[0] = 7;
/// assert_eq!(vec[0], 7);
///
/// vec.extend([1, 2, 3].iter().cloned());
///
/// assert_eq!(vec, [7, 1, 2, 3]);
/// ```
///
/// The `vec32!` macro provides convenient initialization:
///
/// ```
/// #[macro_use] extern crate mediumvec;
///
/// let mut vec = vec32![1, 2, 3];
/// assert_eq!(vec, [1, 2, 3]);
///
/// let vec = vec32![0; 5];
/// assert_eq!(vec, vec32![0, 0, 0, 0, 0]);
/// ```
pub struct Vec32<T> {
    ptr: ptr::NonNull<T>,
    cap: usize32,
    len: usize32,
}

impl<T> Vec32<T> {
    /// Constructs a new, empty vector.
    ///
    /// The vector will not allocate until elements are pushed onto it.
    #[must_use]
    pub fn new() -> Self {
        Self {
            ptr: NonNull::dangling(),
            cap: if mem::size_of::<T>() == 0 {
                usize32::max_value()
            } else {
                0
            },
            len: 0,
        }
    }

    /// Constructs a new, empty (length 0) vector with the specified capacity.
    #[must_use]
    pub fn with_capacity(cap: u32) -> Self {
        let size = usize32::try_from(cap).expect("capacity overflow");
        let mut v = Vec::with_capacity(size as usize);
        let ptr = unsafe {
            // This is safe as long as `Vec<T>` upholds its invariants.
            NonNull::new_unchecked(v.as_mut_ptr())
        };
        mem::forget(v);

        Self {
            ptr,
            cap: size,
            len: 0,
        }
    }

    /// Append an element to the vector.
    ///
    /// Panics if the number of elements in the vector overflows `u32` or `usize`, whichever is smaller.
    pub fn push(&mut self, value: T) {
        if self.len == self.cap {
            self.reserve(1);
        }
        unsafe {
            let end = self.as_mut_ptr().offset(self.len as isize);
            ptr::write(end, value);
            self.len += 1;
        }
    }

    /// Remove the last element from a vector and return it, or `None` if it is empty.
    pub fn pop(&mut self) -> Option<T> {
        if self.len == 0 {
            None
        } else {
            unsafe {
                self.len -= 1;
                Some(ptr::read(self.get_unchecked(self.len as usize)))
            }
        }
    }

    /// Remove and return the element at position `index`, shifting elements after it to the left.
    ///
    /// Panics if `index` is out of bounds.
    ///
    /// ## Examples
    ///
    /// ```
    /// #[macro_use] extern crate mediumvec;
    ///
    /// let mut v = vec32![1, 2, 3];
    /// assert_eq!(v.remove(1), 2);
    /// assert_eq!(v, [1, 3]);
    /// ```
    pub fn remove(&mut self, index: u32) -> T {
        let len = self.len;
        let ind = usize32::try_from(index).expect("index out of bounds");
        assert!(ind < len, "index out of bounds");
        unsafe {
            let ptr = self.as_mut_ptr().offset(ind as isize);
            let ret = ptr::read(ptr);
            ptr::copy(ptr.offset(1), ptr, (len - ind - 1) as usize);
            self.len -= 1;
            ret
        }
    }

    /// Insert an element at position `index`, shifting elements after it to the right.
    ///
    /// Panics if `index` is out of bounds or the length of the vector overflows `u32` or `usize`, whichever is smaller.
    ///
    /// ## Examples
    ///
    /// ```
    /// #[macro_use] extern crate mediumvec;
    /// let mut vec = vec![1, 2, 3];
    /// vec.insert(1, 4);
    /// assert_eq!(vec, [1, 4, 2, 3]);
    /// vec.insert(4, 5);
    /// assert_eq!(vec, [1, 4, 2, 3, 5]);
    /// ```
    pub fn insert(&mut self, index: u32, element: T) {
        let len = self.len;
        let ind = usize32::try_from(index).expect("index out of bounds");
        assert!(ind <= len, "index out of bounds");
        if len == self.cap {
            self.reserve(1);
        }

        unsafe {
            let p = self.as_mut_ptr().offset(ind as isize);
            ptr::copy(p, p.offset(1), (len - ind) as usize);
            ptr::write(p, element);
            self.len += 1;
        }
    }

    /// Reserve capacity for at least `additional` more elements to be inserted.
    ///
    /// May reserve more space than requested, to avoid frequent reallocations.
    ///
    /// Panics if the new capacity overflows `u32` or `usize`, whichever is smaller.
    ///
    /// Re-allocates only if `self.capacity() < self.len() + additional`.
    pub fn reserve(&mut self, additional: u32) {
        let extra = usize32::try_from(additional).expect("capacity overflow");
        let min_cap = self.len.checked_add(extra).expect("capacity overflow");
        if min_cap <= self.cap {
            return;
        }
        let double_cap = self.cap.saturating_mul(2);
        let new_cap = cmp::max(min_cap, double_cap);
        let extra_exact = new_cap - self.len;
        self.reserve_exact(u32::from(extra_exact));
    }

    /// Reserves the minimum capacity for `additional` more elements to be inserted.
    ///
    /// Panics if the new capacity overflows `u32` or `usize`, whichever is smaller.
    ///
    /// Re-allocates only if `self.capacity() < self.len() + additional`.
    pub fn reserve_exact(&mut self, additional: u32) {
        let extra = usize32::try_from(additional).expect("capacity overflow");
        self.as_vec(|v| v.reserve_exact(extra as usize));
    }

    /// Converts a `Vec<T>` to a `Vec32<T>`.
    ///
    /// Panics if the vector's length is greater than `u32::MAX` or `usize::MAX`, whichever is smaller.
    ///
    /// Re-allocates only if the vector's capacity is greater than `u32::MAX`.
    #[must_use]
    pub fn from_vec(mut vec: Vec<T>) -> Self {
        let len = usize32::try_from(vec.len()).expect("capacity overflow");

        if vec.capacity() > usize32::max_value() as usize {
            vec.shrink_to_fit();
        }

        let cap = if mem::size_of::<T>() == 0 {
            usize32::max_value()
        } else {
            usize32::try_from(vec.capacity()).expect("capacity overflow")
        };

        let ptr = unsafe {
            // This is safe as long as `Vec<T>` upholds its invariants.
            NonNull::new_unchecked(vec.as_mut_ptr())
        };
        mem::forget(vec);

        Self { ptr, cap, len }
    }

    /// Convert a `Vec32<T>` into a `Vec<T>` without re-allocating.
    #[must_use]
    pub fn into_vec(self) -> Vec<T> {
        unsafe {
            let v = Vec::from_raw_parts(self.ptr.as_ptr(), self.len as usize, self.cap as usize);
            mem::forget(self);
            v
        }
    }

    /// Convert a `Vec32<T>` into a `Vec<T>`, mutate it, then convert it back.
    ///
    /// This is a convenient way to call `Vec` methods that don't have `Vec32` equivalents.
    ///
    /// Panics if the vector's length increases to greater than `u32::MAX` or `usize::MAX`, whichever is smaller.
    ///
    /// ```
    /// #[macro_use] extern crate mediumvec;
    ///
    /// let mut v = vec32![0, 0, 0, 1, 1, 2, 3, 3, 3];
    /// v.as_vec(|vec| vec.dedup());
    /// assert_eq!(v, [0, 1, 2, 3]);
    /// ```
    pub fn as_vec<F>(&mut self, f: F)
    where
        F: FnOnce(&mut Vec<T>),
    {
        let mut vec = mem::replace(self, Self::new()).into_vec();
        f(&mut vec);
        *self = Self::from_vec(vec);
    }

    /// Returns the maximum number of elements the vector can hold without reallocating.
    #[must_use]
    pub fn capacity(&self) -> u32 {
        u32::from(self.cap)
    }

    /// Clears the vector, removing all values.
    ///
    /// Note that this method has no effect on the allocated capacity
    /// of the vector.
    pub fn clear(&mut self) {
        self.truncate(0)
    }

    /// Shorten the vector, keeping the first `len` elements and dropping the rest.
    ///
    /// If `len` is greater than the vector's current length, this has no effect.
    pub fn truncate(&mut self, len: u32) {
        unsafe {
            // drop any extra elements
            while len < u32::from(self.len) {
                // decrement len before the drop_in_place(), so a panic on Drop
                // doesn't re-drop the just-failed value.
                self.len -= 1;
                let len = self.len as usize;
                ptr::drop_in_place(self.get_unchecked_mut(len));
            }
        }
    }
}

/// Initialize a `Vec32`.
///
/// ## Examples
///
/// ```
/// #[macro_use] extern crate mediumvec;
///
/// let mut vec = vec32![1, 2, 3];
/// vec.push(4);
/// assert_eq!(vec, [1, 2, 3, 4]);
///
/// let vec = vec32![0; 5];
/// assert_eq!(vec, [0, 0, 0, 0, 0]);
/// ```
#[macro_export]
macro_rules! vec32 {
    ($elem:expr; $n:expr) => (
        $crate::Vec32::from_vec(vec![$elem; $n])
    );
    ($($x:expr),*) => (
        $crate::Vec32::from_vec(vec![$($x),*])
    );
    ($($x:expr,)*) => (vec32![$($x),*])
}

// Trait implementations:

impl<T> Default for Vec32<T> {
    #[must_use]
    fn default() -> Self {
        Self::new()
    }
}

impl<T> Drop for Vec32<T> {
    fn drop(&mut self) {
        unsafe {
            ptr::drop_in_place(&mut self[..]);
            Vec::from_raw_parts(self.ptr.as_ptr(), 0, self.cap as usize);
        }
    }
}

unsafe impl<T: Sync> Sync for Vec32<T> {}
unsafe impl<T: Send> Send for Vec32<T> {}

impl<T: Clone> Clone for Vec32<T> {
    #[must_use]
    fn clone(&self) -> Self {
        Self::from_vec(self[..].to_vec())
    }
}

impl<T> ops::Deref for Vec32<T> {
    type Target = [T];

    #[must_use]
    fn deref(&self) -> &[T] {
        unsafe { slice::from_raw_parts(self.ptr.as_ptr(), self.len as usize) }
    }
}

impl<T> ops::DerefMut for Vec32<T> {
    fn deref_mut(&mut self) -> &mut [T] {
        unsafe { slice::from_raw_parts_mut(self.ptr.as_ptr(), self.len as usize) }
    }
}

impl<T> IntoIterator for Vec32<T> {
    type Item = T;
    type IntoIter = vec::IntoIter<T>;

    #[must_use]
    fn into_iter(self) -> vec::IntoIter<T> {
        self.into_vec().into_iter()
    }
}

impl<'a, T> IntoIterator for &'a Vec32<T> {
    type Item = &'a T;
    type IntoIter = slice::Iter<'a, T>;

    #[must_use]
    fn into_iter(self) -> slice::Iter<'a, T> {
        self.iter()
    }
}

impl<'a, T> IntoIterator for &'a mut Vec32<T> {
    type Item = &'a mut T;
    type IntoIter = slice::IterMut<'a, T>;

    fn into_iter(self) -> slice::IterMut<'a, T> {
        self.iter_mut()
    }
}

impl<T> Extend<T> for Vec32<T> {
    fn extend<I: IntoIterator<Item = T>>(&mut self, iter: I) {
        let iterator = iter.into_iter();
        let lower = usize32::try_from(iterator.size_hint().0).expect("capacity overflow");
        assert!(lower != usize32::max_value(), "capacity overflow");
        self.reserve(u32::from(lower));

        for i in iterator {
            self.push(i);
        }
    }
}

impl<T> iter::FromIterator<T> for Vec32<T> {
    fn from_iter<I: IntoIterator<Item = T>>(iter: I) -> Self {
        let iterator = iter.into_iter();
        let lower = usize32::try_from(iterator.size_hint().0).expect("capacity overflow");
        assert!(lower != usize32::max_value(), "capacity overflow");

        let mut v = Self::with_capacity(u32::from(lower));
        for i in iterator {
            v.push(i);
        }
        v
    }
}

impl<T: fmt::Debug> fmt::Debug for Vec32<T> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        fmt::Debug::fmt(&self[..], f)
    }
}

impl<T: PartialOrd> PartialOrd for Vec32<T> {
    #[must_use]
    fn partial_cmp(&self, other: &Self) -> Option<cmp::Ordering> {
        PartialOrd::partial_cmp(&**self, &**other)
    }
}

impl<T: Eq> Eq for Vec32<T> {}

impl<T, U> PartialEq<U> for Vec32<T>
where
    U: for<'a> PartialEq<&'a [T]>,
{
    fn eq(&self, other: &U) -> bool {
        *other == &self[..]
    }
}

#[cfg(test)]
mod tests {
    use super::Vec32;

    #[test]
    fn singledrop() {
        struct SingleDrop(bool);
        impl Drop for SingleDrop {
            fn drop(&mut self) {
                assert!(self.0);
                self.0 = false
            }
        }
        let mut v = vec32![SingleDrop(true)];
        v.push(SingleDrop(true));
    }

    #[test]
    fn it_works() {
        let mut v = vec32![1, 2, 3];
        assert_eq!(v.pop(), Some(3));
        v.push(4);
        assert_eq!(v, vec![1, 2, 4]);
    }

    #[test]
    fn test_size() {
        use std::mem::size_of;
        #[cfg(target_pointer_width = "64")]
        assert_eq!(size_of::<Vec32<()>>(), 16);
        #[cfg(target_pointer_width = "32")]
        assert_eq!(size_of::<Vec32<()>>(), 12);
        #[cfg(target_pointer_width = "16")]
        assert_eq!(size_of::<Vec32<()>>(), 6);
    }
}
