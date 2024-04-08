#![feature(allocator_api)]
#![feature(dropck_eyepatch)]
#![feature(ptr_mask)]
#![warn(clippy::missing_inline_in_public_items)]

use std::alloc;
use std::alloc::AllocError;
use std::alloc::Allocator;
use std::alloc::Global;
use std::alloc::Layout;
use std::cell::Cell;
use std::cell::UnsafeCell;
use std::fmt;
use std::ptr;
use std::ptr::NonNull;

struct Chunk {
    start: NonNull<()>,
    end: NonNull<()>,
    layout: Layout,
}

impl Chunk {
    /// ## Safety
    ///
    /// `capacity` must be non-zero.
    unsafe fn new(capacity: usize) -> Result<Chunk, AllocError> {
        let layout = Layout::from_size_align(capacity, START_CAPACITY).unwrap();
        let end: NonNull<()> = Global.allocate(layout)?.cast();
        // SAFETY: `end` was allocated with `capacity` bytes.
        let start = unsafe { end.as_ptr().byte_add(capacity) };
        // SAFETY: `start` is a valid pointer.
        let start = unsafe { NonNull::new_unchecked(start) };
        Ok(Chunk { start, end, layout })
    }

    /// ## Safety
    ///
    /// `self.has_capacity_for::<T>()` must return `true`.
    #[inline(always)]
    unsafe fn allocate(&mut self, layout: Layout) -> NonNull<()> {
        debug_assert!(self.has_capacity_for(layout));

        // SAFETY: Must be ensured by caller.
        let ptr = unsafe { self.start.as_ptr().byte_sub(layout.size()) };
        let aligned = ptr.mask(!(layout.align() - 1));
        // SAFETY: Must be ensured by caller.
        let non_null_aligned = unsafe { NonNull::new_unchecked(aligned) };
        self.start = non_null_aligned;
        non_null_aligned
    }

    #[inline(always)]
    fn has_capacity_for(&self, layout: Layout) -> bool {
        let start = self.start.as_ptr() as usize;
        let item_start = (start - layout.size()) & !(layout.align() - 1);
        item_start >= self.end.as_ptr() as usize
    }

    fn deallocate(&self) {
        // SAFETY: This memory was allocated with `Chunk::allocate`.
        unsafe {
            alloc::dealloc(self.end.as_ptr().cast(), self.layout);
        }
    }
}

pub struct Arena<'arena> {
    chunks: UnsafeCell<Vec<Chunk>>,
    managed: UnsafeCell<Vec<NonNull<(dyn Any + 'arena)>>>,
    next_capacity: Cell<usize>,
}

const START_CAPACITY: usize = 4 * 1024;
const MAX_CAPACITY: usize = 2 * 1024 * 1024;

impl<'arena> Arena<'arena> {
    /// ## Safety
    ///
    /// All data allocated in this arena must *strictly* outlive the arena.
    ///
    /// This is most easily enforced with higher-rank trait bounds, as in [`with_arena`].
    ///
    /// ## Panics
    ///
    /// Panics on allocation error.
    #[inline]
    pub unsafe fn new() -> Arena<'arena> {
        // SAFETY: `START_CAPACITY` is non-zero.
        let start_chunk = unsafe { Chunk::new(START_CAPACITY).unwrap() };
        Arena {
            chunks: UnsafeCell::new(vec![start_chunk]),
            managed: UnsafeCell::new(Vec::new()),
            next_capacity: Cell::new(START_CAPACITY * 2),
        }
    }

    #[inline(always)]
    fn allocate_chunk(&self, chunks: &mut Vec<Chunk>, min_size: usize) -> Result<(), AllocError> {
        let capacity = self.next_capacity.get().max(min_size);
        // SAFETY: `self.next_capacity` is never zero.
        let new_chunk = unsafe { Chunk::new(capacity)? };
        chunks.push(new_chunk);
        if capacity < MAX_CAPACITY {
            self.next_capacity.set(capacity * 2);
        }
        Ok(())
    }

    #[inline(always)]
    fn allocate_raw(&'arena self, layout: Layout) -> Result<NonNull<()>, AllocError> {
        assert!(layout.align() <= START_CAPACITY);

        // SAFETY: This is the only access to `*self.chunks`.
        let chunks = unsafe { &mut *self.chunks.get() };

        if !chunks.last().unwrap().has_capacity_for(layout) {
            self.allocate_chunk(chunks, layout.size())?;
        }

        // SAFETY: Just checked.
        unsafe { Ok(chunks.last_mut().unwrap().allocate(layout)) }
    }

    /// ## Panics
    ///
    /// Panics if `mem::align_of::<T>() > 4096`.
    #[inline]
    #[allow(clippy::mut_from_ref)]
    pub fn allocate<T: 'arena>(&'arena self, value: T) -> &'arena mut T {
        let layout = Layout::new::<T>();
        let ptr = self
            .allocate_raw(Layout::new::<T>())
            .unwrap_or_else(|_| alloc::handle_alloc_error(layout))
            .cast();

        // SAFETY: `Chunk::allocate` always returns a valid pointer.
        unsafe {
            ptr::write(ptr.as_ptr(), value);
        }

        // SAFETY: This is the only active reference to `*self.managed`.
        let managed = unsafe { &mut *self.managed.get() };
        managed.push(ptr);

        // SAFETY: There are no active references to `*ptr`.
        unsafe { &mut *ptr.as_ptr() }
    }
}

impl<'arena> fmt::Debug for Arena<'arena> {
    #[inline]
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("Arena").finish_non_exhaustive()
    }
}

// SAFETY: Ensured by caller of `Arena::new`.
unsafe impl<#[may_dangle] 'arena> Drop for Arena<'arena> {
    #[inline]
    fn drop(&mut self) {
        for &value in self.managed.get_mut().iter().rev() {
            // SAFETY: This is the last pointer to `*value`.
            unsafe {
                ptr::drop_in_place(value.as_ptr());
            }
        }
        for chunk in self.chunks.get_mut() {
            chunk.deallocate();
        }
    }
}

trait Any {}

impl<T: ?Sized> Any for T {}

#[inline]
pub fn with_arena<F, T>(f: F) -> T
where
    F: for<'arena> FnOnce(&'arena Arena<'arena>) -> T,
{
    // SAFETY: Ensured by higher-order lifetime.
    let arena = unsafe { Arena::new() };
    f(&arena)
}

// SAFETY: All returned pointers are valid.
unsafe impl<'arena> Allocator for &'arena Arena<'arena> {
    #[inline]
    fn allocate(&self, layout: Layout) -> Result<NonNull<[u8]>, AllocError> {
        let data: NonNull<u8> = self.allocate_raw(layout)?.cast();
        let ptr = NonNull::slice_from_raw_parts(data, layout.size());
        Ok(ptr)
    }

    #[inline(always)]
    unsafe fn deallocate(&self, _: NonNull<u8>, _: Layout) {}

    #[inline]
    unsafe fn shrink(
        &self,
        ptr: NonNull<u8>,
        old_layout: Layout,
        new_layout: Layout,
    ) -> Result<NonNull<[u8]>, AllocError> {
        if ptr.as_ptr() as usize & (new_layout.align() - 1) == 0 {
            Ok(NonNull::slice_from_raw_parts(ptr, old_layout.size()))
        } else {
            let new_ptr = self.allocate(new_layout)?;
            // SAFETY: `new_layout.size()` >= `old_layout.size()`, and `allocate` returns a valid
            // pointer.
            unsafe {
                ptr::copy_nonoverlapping(ptr.as_ptr(), new_ptr.cast().as_ptr(), new_layout.size());
            }
            Ok(new_ptr)
        }
    }
}
