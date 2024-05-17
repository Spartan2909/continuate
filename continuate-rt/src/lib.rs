#![feature(allocator_api)]

use std::alloc::handle_alloc_error;
use std::alloc::Allocator;
use std::alloc::Global;
use std::alloc::Layout;
use std::mem;
use std::process;
use std::ptr::NonNull;

use continuate_rt_common::TyLayout;

use log::info;

static STRING_LAYOUT: TyLayout = TyLayout::String;

/// ## Safety
///
/// `layout` must be a valid layout. In particular, it must accurately describe the locations of
/// pointers in the allocated value, and `layout.size()` and `layout.align()` must fit the
/// preconditions of [`Layout::from_size_align`].
///
/// ## Panics
///
/// Panics if `layout` is a `TyLayout::String`.
#[no_mangle]
pub unsafe extern "C" fn cont_rt_alloc_gc(
    layout: &'static TyLayout<'static>,
    variant: usize,
) -> NonNull<()> {
    #[cfg(debug_assertions)]
    info!("allocating object with layout {layout:?}");

    let size = layout
        .size()
        .expect("cannot allocate string with 'cont_rt_alloc_gc'");
    debug_assert!(size >= 8);
    let size = size as usize + mem::size_of::<usize>() * 2;
    let align = (layout.align() as usize).max(mem::align_of::<usize>() * 2);
    // SAFETY: Must be ensured by caller.
    let mem_layout = unsafe { Layout::from_size_align_unchecked(size, align) };
    let ptr = Global
        .allocate_zeroed(mem_layout)
        .unwrap_or_else(|_| handle_alloc_error(mem_layout));
    let ptr: NonNull<u8> = ptr.cast();
    let variant_ptr: NonNull<usize> = ptr.cast();
    // SAFETY: `ptr` has just been allocated with enough space for a `usize`.
    unsafe {
        variant_ptr.as_ptr().write(variant);
    }
    // SAFETY: `ptr` has just been allocated with enough size to hold at least two `usize`.
    let layout_ptr: *mut &TyLayout = unsafe { ptr.as_ptr().add(mem::size_of::<usize>()).cast() };
    // SAFETY: See above.
    unsafe {
        layout_ptr.write(layout);
    }
    // SAFETY: See above.
    let value_ptr = unsafe { ptr.as_ptr().add(mem::size_of::<usize>() * 2) };
    // SAFETY: `value_ptr` is directly derived from a `NonNull`.
    unsafe { NonNull::new_unchecked(value_ptr.cast()) }
}

#[no_mangle]
#[allow(clippy::missing_panics_doc)]
pub extern "C" fn cont_rt_alloc_string(len: usize) -> NonNull<()> {
    #[cfg(debug_assertions)]
    info!("allocating string with length {len}");

    let mem_layout = Layout::from_size_align(len + mem::size_of::<usize>(), 1).unwrap();

    let ptr: NonNull<u8> = Global
        .allocate(mem_layout)
        .unwrap_or_else(|_| handle_alloc_error(mem_layout))
        .cast();
    let layout_ptr: NonNull<&TyLayout> = ptr.cast();
    // SAFETY: `ptr` has just been allocated with enough space for a `usize`.
    unsafe {
        layout_ptr.as_ptr().write(&STRING_LAYOUT);
    }

    // SAFETY: See above.
    let value_ptr = unsafe { ptr.as_ptr().add(mem::size_of::<usize>()) };

    // SAFETY: `value_ptr` is directly derived from a `NonNull`.
    unsafe { NonNull::new_unchecked(value_ptr.cast()) }
}

#[no_mangle]
pub extern "C" fn cont_rt_exit(code: i64) {
    println!("{code}");
    process::exit(code as i32);
}

#[cfg(debug_assertions)]
#[no_mangle]
#[allow(clippy::missing_panics_doc)]
pub extern "C" fn cont_rt_enable_log() {
    simple_logger::SimpleLogger::new()
        .with_level(log::LevelFilter::Info)
        .with_colors(true)
        .without_timestamps()
        .init()
        .unwrap();
}

#[cfg(not(debug_assertions))]
#[no_mangle]
#[inline(always)]
pub extern "C" fn cont_rt_enable_log() {}
