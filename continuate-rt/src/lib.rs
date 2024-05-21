#![feature(allocator_api)]

use std::alloc::handle_alloc_error;
use std::alloc::Allocator;
use std::alloc::Global;
use std::alloc::Layout;
use std::mem;
use std::process;
use std::ptr::NonNull;

use continuate_common::TyLayout;

use tracing::debug;

use tracing_subscriber::filter::LevelFilter;

static STRING_LAYOUT: TyLayout = TyLayout::String;

#[repr(C)]
struct GcValue<T: ?Sized> {
    layout: &'static TyLayout<'static>,
    value: T,
}

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
pub unsafe extern "C" fn cont_rt_alloc_gc(layout: &'static TyLayout<'static>) -> NonNull<()> {
    #[cfg(debug_assertions)]
    debug!("allocating object with layout {layout:?}");

    let size = layout
        .size()
        .expect("cannot allocate string with 'cont_rt_alloc_gc'");
    debug_assert!(size >= 8);
    let size = size as usize + mem::size_of::<usize>();
    let align = (layout.align() as usize).max(mem::align_of::<usize>());

    // SAFETY: Must be ensured by caller.
    let mem_layout = unsafe { Layout::from_size_align_unchecked(size, align) };
    let ptr = Global
        .allocate_zeroed(mem_layout)
        .unwrap_or_else(|_| handle_alloc_error(mem_layout));

    let ptr: NonNull<GcValue<()>> = ptr.cast();
    let layout_ptr: *mut &TyLayout = ptr.as_ptr().cast();

    // SAFETY: `ptr` has just been allocated with enough size to hold at least a `usize`.
    unsafe {
        layout_ptr.write(layout);
    }
    // SAFETY: See above.
    let value_ptr = unsafe { ptr.as_ptr().add(mem::offset_of!(GcValue<()>, value)) };
    // SAFETY: `value_ptr` is directly derived from a `NonNull`.
    unsafe { NonNull::new_unchecked(value_ptr.cast()) }
}

/// ## Safety
///
/// - `ptr` must point to memory allocated with [`cont_rt_alloc_gc`], and must not have
/// previously been passed to this function.
///
/// - All objects allocated with [`cont_rt_alloc_gc`] must be reachable from `ptr` or an object
/// previously marked with [`cont_rt_mark_root`].
#[no_mangle]
pub const unsafe extern "C" fn cont_rt_mark_root(ptr: NonNull<()>) {
    let _ = ptr;
}

/// ## Safety
///
/// `ptr` must point to memory allocated with [`cont_rt_alloc_gc`] and marked by
/// [`cont_rt_mark_root`], and must not have previously been passed to this function.
#[no_mangle]
pub const unsafe extern "C" fn cont_rt_unmark_root(ptr: NonNull<()>) {
    let _ = ptr;
}

#[no_mangle]
#[allow(clippy::missing_panics_doc)]
pub extern "C" fn cont_rt_alloc_string(len: usize) -> NonNull<()> {
    #[cfg(debug_assertions)]
    debug!("allocating string with length {len}");

    let mem_layout =
        Layout::from_size_align(len + mem::size_of::<usize>(), mem::align_of::<usize>()).unwrap();

    let ptr: NonNull<GcValue<()>> = Global
        .allocate(mem_layout)
        .unwrap_or_else(|_| handle_alloc_error(mem_layout))
        .cast();
    let layout_ptr: NonNull<&TyLayout> = ptr.cast();
    // SAFETY: `ptr` has just been allocated with enough space for a `usize`.
    unsafe {
        layout_ptr.as_ptr().write(&STRING_LAYOUT);
    }

    // SAFETY: See above.
    let value_ptr = unsafe { ptr.as_ptr().add(mem::offset_of!(GcValue<()>, value)) };

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
    continuate_common::init_tracing(LevelFilter::DEBUG).expect("failed to instantiate logger");
}

#[cfg(not(debug_assertions))]
#[no_mangle]
#[inline(always)]
pub extern "C" fn cont_rt_enable_log() {}
