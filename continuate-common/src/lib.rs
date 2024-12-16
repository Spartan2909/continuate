#![feature(allocator_api)]
#![warn(clippy::missing_inline_in_public_items)]

use std::alloc::Allocator;
use std::alloc::Layout;
use std::error::Error;
use std::fmt;
use std::io;
use std::marker::PhantomData;
use std::mem;
use std::ops;
use std::ptr::NonNull;
use std::slice;

use bytemuck::Pod;

use tracing_subscriber::filter::LevelFilter;

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
        // SAFETY: `slice.as_ptr()` always returns a non-null pointer.
        let ptr = unsafe { NonNull::new_unchecked(slice.as_ptr().cast_mut()) };
        Slice {
            ptr,
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

    #[allow(clippy::missing_panics_doc)]
    #[inline]
    pub fn allocate_slice<'b, A: Allocator + 'b>(slice: &[T], alloc: &'b A) -> Slice<'b, T>
    where
        T: Copy + 'b,
    {
        let layout = Layout::array::<T>(slice.len()).unwrap();
        let ptr = alloc.allocate(layout).unwrap();
        let ptr: *mut T = ptr.as_ptr().cast();
        // SAFETY: `ptr` was just allocated, and `slice` is still valid.
        unsafe { ptr.copy_from_nonoverlapping(slice.as_ptr(), slice.len()) }
        // SAFETY: `ptr` has just been initialised with a slice.
        unsafe { Slice::from_raw_parts(ptr, slice.len()) }
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

/// The layout of a primitive type, a product type, or a single variant of a sum type.
#[repr(C)]
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct SingleLayout<'a> {
    pub size: u64,
    pub align: u64,
    pub field_locations: Slice<'a, u64>,
    pub gc_pointer_locations: Slice<'a, u64>,
}

impl<'a> SingleLayout<'a> {
    #[inline]
    pub const fn primitive(size: u64, align: u64) -> SingleLayout<'a> {
        SingleLayout {
            size,
            align,
            field_locations: Slice::new(&[]),
            gc_pointer_locations: Slice::new(&[]),
        }
    }
}

/// The layout of a type.
#[repr(u8)]
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum TyLayout<'a> {
    Single(SingleLayout<'a>) = 0,
    Sum {
        layouts: Slice<'a, SingleLayout<'a>>,
        /// The size required to hold the largest variant layout, in bytes.
        size: u64,
        /// The highest alignment required by a variant layout, in bytes.
        align: u64,
    } = 1,
    String = 2,
}

impl<'a> TyLayout<'a> {
    #[inline]
    pub const fn size(&self) -> Option<u64> {
        match *self {
            TyLayout::Single(ref layout) => Some(layout.size),
            TyLayout::Sum { size, .. } => Some(size),
            TyLayout::String => None,
        }
    }

    #[inline]
    pub const fn align(&self) -> u64 {
        match *self {
            TyLayout::Single(ref layout) => layout.align,
            TyLayout::Sum { align, .. } => align,
            TyLayout::String => 1,
        }
    }

    #[inline]
    pub const fn as_single(&self) -> Option<&SingleLayout<'a>> {
        if let TyLayout::Single(layout) = self {
            Some(layout)
        } else {
            None
        }
    }

    #[inline]
    pub const fn as_sum(&self) -> Option<Slice<'a, SingleLayout<'a>>> {
        if let TyLayout::Sum { layouts, .. } = *self {
            Some(layouts)
        } else {
            None
        }
    }
}

impl<'a> From<SingleLayout<'a>> for TyLayout<'a> {
    #[inline]
    fn from(value: SingleLayout<'a>) -> Self {
        TyLayout::Single(value)
    }
}

/// ## Errors
///
/// Returns an error if `tracing` instantiation fails.
#[inline]
pub fn init_tracing(filter: LevelFilter) -> Result<(), Box<dyn Error + Send + Sync + 'static>> {
    tracing_subscriber::fmt()
        .with_max_level(filter)
        .without_time()
        .with_writer(io::stderr)
        .try_init()
}
