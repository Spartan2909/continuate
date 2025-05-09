
use std::fmt;
use std::marker::PhantomData;
use std::mem;
use std::ops;
use std::ptr;
use std::ptr::NonNull;
use std::slice;

use bytemuck::Pod;

/// An FFI-safe slice.
///
/// The layout of this type is a non-null pointer followed by a `usize`.
#[repr(C)]
pub struct Slice<'a, T> {
    ptr: NonNull<T>,
    len: usize,
    _marker: PhantomData<&'a [T]>,
}

impl<'a, T> Slice<'a, T> {
    #[inline]
    pub const fn new(slice: &'a [T]) -> Slice<'a, T> {
        // SAFETY: The pointer is derived from a reference, and so must be non-null.
        let ptr = unsafe { NonNull::new_unchecked(ptr::from_ref(slice).cast_mut()) };
        Slice {
            ptr: ptr.cast(),
            len: slice.len(),
            _marker: PhantomData,
        }
    }

    /// ## Safety
    ///
    /// `data` must point to a slice of `T` with a length of at least `len`, and the elements of
    /// that slice must not be modified for the duration of `'a`.
    #[inline]
    pub const unsafe fn from_raw_parts(data: *const T, len: usize) -> Slice<'a, T> {
        // SAFETY: Must be ensured by caller.
        let ptr = unsafe { NonNull::new_unchecked(data.cast_mut()) };
        Slice {
            ptr,
            len,
            _marker: PhantomData,
        }
    }

    #[inline(always)]
    pub const fn as_ptr(self) -> *const T {
        self.ptr.as_ptr()
    }

    #[inline(always)]
    pub const fn len(self) -> usize {
        self.len
    }

    #[inline(always)]
    pub const fn is_empty(self) -> bool {
        self.len == 0
    }

    #[inline(always)]
    pub const fn as_slice(self) -> &'a [T] {
        // SAFETY: `self` is always a valid slice.
        unsafe { slice::from_raw_parts(self.ptr.as_ptr(), self.len) }
    }

    #[inline]
    pub const fn as_byte_slice(self) -> Slice<'a, u8>
    where
        T: Pod,
    {
        Slice {
            ptr: self.ptr.cast(),
            len: self.len * mem::size_of::<T>(),
            _marker: PhantomData,
        }
    }
}

impl<T> Clone for Slice<'_, T> {
    #[inline(always)]
    fn clone(&self) -> Self {
        *self
    }
}

impl<T> Copy for Slice<'_, T> {}

impl<T: fmt::Debug> fmt::Debug for Slice<'_, T> {
    #[inline]
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        fmt::Debug::fmt(&**self, f)
    }
}

impl<'a, T> From<&'a [T]> for Slice<'a, T> {
    #[inline]
    fn from(value: &'a [T]) -> Self {
        Slice::new(value)
    }
}

impl<T: PartialEq> PartialEq for Slice<'_, T> {
    #[inline]
    fn eq(&self, other: &Self) -> bool {
        **self == **other
    }
}

impl<T: Eq> Eq for Slice<'_, T> {}

impl<T> ops::Deref for Slice<'_, T> {
    type Target = [T];

    #[inline]
    fn deref(&self) -> &Self::Target {
        self.as_slice()
    }
}

impl<'a, T> IntoIterator for Slice<'a, T> {
    type Item = &'a T;
    type IntoIter = slice::Iter<'a, T>;

    #[inline]
    fn into_iter(self) -> Self::IntoIter {
        self.as_slice().iter()
    }
}

impl<T> ops::Index<usize> for Slice<'_, T> {
    type Output = T;

    #[inline]
    fn index(&self, index: usize) -> &Self::Output {
        &self.as_slice()[index]
    }
}

// SAFETY: `Slice` behaves identically to `&'a [T]`.
unsafe impl<'a, T> Send for Slice<'a, T> where &'a [T]: Send {}

// SAFETY: `Slice` behaves identically to `&'a [T]`.
unsafe impl<'a, T> Sync for Slice<'a, T> where &'a [T]: Sync {}
