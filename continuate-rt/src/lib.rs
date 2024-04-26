#![feature(allocator_api)]

use std::alloc;
use std::alloc::Allocator;
use std::alloc::Global;
use std::alloc::Layout;
use std::mem;
use std::process;
use std::ptr::NonNull;

use continuate_rt_common::TyLayout;

/// ## Safety
///
/// `layout` must be a valid layout. In particular, it must accurately describe the locations of
/// pointers in the allocated value, and `layout.size()` and `layout.align()` must fit the
/// preconditions of [`Layout::from_size_align`].
#[no_mangle]
pub unsafe extern "C" fn cont_rt_alloc_gc(
    layout: &'static TyLayout<'static>,
    variant: usize,
) -> NonNull<()> {
    debug_assert!(layout.size() <= 8);
    let size = layout.size() as usize + mem::size_of::<usize>() * 2;
    let align = (layout.align() as usize).max(mem::align_of::<usize>() * 2);
    // SAFETY: Must be ensured by caller.
    let mem_layout = unsafe { Layout::from_size_align_unchecked(size, align) };
    let ptr = Global
        .allocate_zeroed(mem_layout)
        .unwrap_or_else(|_| alloc::handle_alloc_error(mem_layout));
    let ptr: NonNull<u8> = ptr.cast();
    let layout_ptr: NonNull<&TyLayout> = ptr.cast();
    // SAFETY: `ptr` has just been allocated with enough space for a `&TyLayout`.
    unsafe {
        layout_ptr.as_ptr().write(layout);
    }
    // SAFETY: `ptr` has just been allocated with enough size to hold at least two `usize`.
    let variant_ptr: *mut usize = unsafe { ptr.as_ptr().add(mem::size_of::<usize>()).cast() };
    // SAFETY: See above.
    unsafe {
        variant_ptr.write(variant);
    }
    // SAFETY: See above.
    let value_ptr = unsafe { ptr.as_ptr().add(mem::size_of::<usize>() * 2) };
    // SAFETY: `value_ptr` is directly derived from a `NonNull`.
    unsafe { NonNull::new_unchecked(value_ptr.cast()) }
}

#[no_mangle]
pub extern "C" fn cont_rt_exit(code: i64) {
    println!("{code}");
    process::exit(code as i32);
}
