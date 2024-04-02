#![feature(dropck_eyepatch)]

use std::cell::UnsafeCell;
use std::fmt;
use std::ptr::NonNull;

#[derive(Default)]
pub struct Arena<'arena> {
    managed: UnsafeCell<Vec<NonNull<dyn Any + 'arena>>>,
}

impl<'arena> Arena<'arena> {
    pub const fn new() -> Arena<'arena> {
        Arena {
            managed: UnsafeCell::new(Vec::new()),
        }
    }

    #[allow(clippy::mut_from_ref)]
    pub fn allocate<T: 'arena>(&'arena self, value: T) -> &'arena mut T {
        let value = Box::leak(Box::new(value));
        // NOTE: Using `value` past this point causes UB under stacked borrows.
        let ptr = value as *mut T;

        let any_ptr = ptr as *mut dyn Any;
        // SAFETY: `any_ptr` was derived from a reference, and so cannot be null.
        let any_ptr = unsafe { NonNull::new_unchecked(any_ptr) };

        // SAFETY: This is the only active reference to `*self.managed`.
        let managed = unsafe { &mut *self.managed.get() };
        managed.push(any_ptr);

        // SAFETY: There are no active references to `*ptr`.
        unsafe { &mut *ptr }
    }

    pub fn collect(&mut self) {
        for &mut value in self.managed.get_mut() {
            // SAFETY: This is the last pointer to `*value`.
            unsafe {
                drop(Box::from_raw(value.as_ptr()));
            }
        }
        self.managed.get_mut().clear();
    }
}

impl<'arena> fmt::Debug for Arena<'arena> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("Arena").finish_non_exhaustive()
    }
}

// SAFETY: `Arena` owns everything it references.
unsafe impl<#[may_dangle] 'arena> Drop for Arena<'arena> {
    fn drop(&mut self) {
        self.collect();
    }
}

trait Any {}

impl<T: ?Sized> Any for T {}
