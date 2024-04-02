#![feature(dropck_eyepatch, ptr_mask)]

use std::alloc;
use std::alloc::Layout;
use std::cell::Cell;
use std::cell::UnsafeCell;
use std::fmt;
use std::mem;
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
    unsafe fn new(capacity: usize) -> Chunk {
        let layout = Layout::from_size_align(capacity, START_CAPACITY).unwrap();
        // SAFETY: Ensured by caller.
        let end = unsafe { alloc::alloc(layout) };
        let non_null_end =
            NonNull::new(end.cast()).unwrap_or_else(|| alloc::handle_alloc_error(layout));
        // SAFETY: `end` was allocated with `capacity` bytes.
        let start = unsafe { end.byte_add(capacity) };
        // SAFETY: `start` is part of the allocation returned by `alloc`.
        let non_null_start = unsafe { NonNull::new_unchecked(start.cast()) };
        Chunk {
            start: non_null_start,
            end: non_null_end,
            layout,
        }
    }

    /// ## Safety
    ///
    /// `self.capacity_for::<T>()` must return `true`.
    unsafe fn allocate<T>(&mut self) -> NonNull<T> {
        debug_assert!(self.has_capacity_for::<T>());

        // SAFETY: Must be ensured by caller.
        let ptr = unsafe { self.start.as_ptr().byte_sub(mem::size_of::<T>()) };
        let aligned = ptr.mask(!(mem::align_of::<T>() - 1));
        // SAFETY: Must be ensured by caller.
        let non_null_aligned = unsafe { NonNull::new_unchecked(aligned) };
        self.start = non_null_aligned;
        non_null_aligned.cast()
    }

    fn has_capacity_for<T>(&self) -> bool {
        let start = self.start.as_ptr() as usize;
        let item_start = (start - mem::size_of::<T>()) & !(mem::align_of::<T>() - 1);
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
    pub unsafe fn new() -> Arena<'arena> {
        // SAFETY: `START_CAPACITY` is non-zero.
        let start_chunk = unsafe { Chunk::new(START_CAPACITY) };
        Arena {
            chunks: UnsafeCell::new(vec![start_chunk]),
            managed: UnsafeCell::new(Vec::new()),
            next_capacity: Cell::new(START_CAPACITY * 2),
        }
    }

    fn allocate_chunk<T>(&self, chunks: &mut Vec<Chunk>) {
        let capacity = self.next_capacity.get().max(mem::size_of::<T>());
        // SAFETY: `self.next_capacity` is never zero.
        let new_chunk = unsafe { Chunk::new(capacity) };
        chunks.push(new_chunk);
        if capacity < MAX_CAPACITY {
            self.next_capacity.set(capacity * 2);
        }
    }

    /// ## Panics
    ///
    /// Panics if `mem::align_of::<T>() > 4096`/
    #[allow(clippy::mut_from_ref)]
    pub fn allocate<T: 'arena>(&'arena self, value: T) -> &'arena mut T {
        assert!(mem::align_of::<T>() <= START_CAPACITY);

        // SAFETY: This is the only access to `*self.chunks`.
        let chunks = unsafe { &mut *self.chunks.get() };

        if !chunks.last().unwrap().has_capacity_for::<T>() {
            self.allocate_chunk::<T>(chunks);
        }

        // SAFETY: Just checked.
        let ptr = unsafe { chunks.last_mut().unwrap().allocate::<T>() };
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
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("Arena").finish_non_exhaustive()
    }
}

// SAFETY: Ensured by caller of `Arena::new`.
unsafe impl<#[may_dangle] 'arena> Drop for Arena<'arena> {
    fn drop(&mut self) {
        for &mut value in self.managed.get_mut() {
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

pub fn with_arena<F, T>(f: F) -> T
where
    F: for<'arena> FnOnce(&'arena Arena<'arena>) -> T,
{
    // SAFETY: Ensured by higher-order lifetime.
    let arena = unsafe { Arena::new() };
    f(&arena)
}
