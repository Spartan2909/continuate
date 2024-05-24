#![feature(allocator_api)]

use std::alloc::handle_alloc_error;
use std::alloc::Allocator;
use std::alloc::Global;
use std::alloc::Layout;
use std::ffi::c_char;
use std::ffi::CStr;
use std::mem;
use std::ptr::NonNull;
use std::sync::Mutex;

use continuate_common::SingleLayout;
use continuate_common::TyLayout;

use mimalloc::MiMalloc;

#[cfg(debug_assertions)]
use tracing::debug;

use tracing_subscriber::filter::LevelFilter;

#[global_allocator]
static GLOBAL: MiMalloc = MiMalloc;

static STRING_LAYOUT: TyLayout = TyLayout::String;

#[repr(C)]
struct GcValue<T: ?Sized> {
    layout: &'static TyLayout<'static>,
    next: Option<NonNull<GcValue<()>>>,
    mark: bool,
    value: T,
}

struct GarbageCollector<A> {
    values: Option<NonNull<GcValue<()>>>,
    roots: Vec<NonNull<GcValue<()>>>,
    temp_roots: Vec<NonNull<GcValue<()>>>,
    bytes_allocated: usize,
    next_gc: usize,
    allocator: A,
}

fn mark_object(value: &mut GcValue<()>) {
    value.mark = true;
    let gc_pointer_locations = match *value.layout {
        TyLayout::Single(SingleLayout {
            gc_pointer_locations,
            ..
        }) => gc_pointer_locations.as_slice(),
        TyLayout::Sum { layouts, .. } => {
            let value: *mut () = &mut value.value;
            let discriminant: *mut u64 = value.cast();
            // SAFETY: A `GcValue` with a `Layout::Sum` must begin with a `u64` discriminant.
            let discriminant = unsafe { discriminant.read() };
            layouts[discriminant as usize]
                .gc_pointer_locations
                .as_slice()
        }
        TyLayout::String => &[],
    };
    let value: *mut GcValue<()> = value;

    for &location in gc_pointer_locations {
        let location = mem::offset_of!(GcValue<()>, value) + location as usize;
        // SAFETY: Every element of `gc_pointer_locations` is a valid offset into `value.value`.
        let object = unsafe { value.byte_add(location) };
        // SAFETY: See above.
        unsafe {
            mark_object(&mut *object);
        }
    }
}

impl<A: Allocator> GarbageCollector<A> {
    const HEAP_GROW_FACTOR: usize = 2;

    /// ## Safety
    ///
    /// All roots in `self` must be valid.
    unsafe fn mark_roots(&mut self) {
        for &root in &self.roots {
            // SAFETY: Must be ensured by caller.
            let root = unsafe { &mut *root.as_ptr() };
            mark_object(root);
        }

        for &temp_root in &self.roots {
            // SAFETY: Must be ensured by caller.
            let temp_root = unsafe { &mut *temp_root.as_ptr() };
            mark_object(temp_root);
        }
    }

    /// ## Safety
    ///
    /// `object` must be a valid pointer to a `GcValue<()>`.
    unsafe fn free_object(&mut self, object: NonNull<GcValue<()>>) {
        // SAFETY: `object` is a valid pointer to a `GcValue<()>`.
        let layout_ptr: *const &TyLayout = unsafe {
            object
                .as_ptr()
                .add(mem::offset_of!(GcValue<()>, layout))
                .cast()
        };
        // SAFETY: See above.
        let layout = unsafe { layout_ptr.read() };

        match *layout {
            TyLayout::Single(SingleLayout { size, align, .. })
            | TyLayout::Sum { size, align, .. } => {
                let layout = Layout::from_size_align(size as usize, align as usize).unwrap();
                // SAFETY: `object` was allocated with `Global` with `layout`.
                unsafe {
                    self.allocator.deallocate(object.cast(), layout);
                }
            }
            TyLayout::String => {
                // SAFETY: `object` is a valid pointer to a `GcValue<c_char>`.
                let value: *const c_char = unsafe {
                    object
                        .as_ptr()
                        .add(mem::offset_of!(GcValue<()>, value))
                        .cast()
                };
                // SAFETY: `value` is a pointer to a nul-terminated sequence of bytes.
                let bytes = unsafe { CStr::from_ptr(value) };
                let size = mem::size_of::<GcValue<()>>() + bytes.to_bytes_with_nul().len();
                let layout = Layout::from_size_align(size, mem::align_of::<GcValue<()>>()).unwrap();
                // SAFETY: `object` was allocated with `Global` with `layout`.
                unsafe {
                    self.allocator.deallocate(object.cast(), layout);
                }
            }
        }
    }

    /// ## Safety
    ///
    /// - Any memory allocated in `self` which is accessed after this method is called must be
    ///     marked.
    ///
    /// - All values in `self` must be valid.
    unsafe fn sweep(&mut self) {
        let mut previous = None;
        let mut current = self.values;
        while let Some(value) = current {
            // SAFETY: Must be ensured by caller.
            let value = unsafe { &mut *value.as_ptr() };

            if value.mark {
                value.mark = false;
                current = value.next;
                previous = Some(NonNull::from(value));
            } else {
                current = value.next;
                let value = NonNull::from(value);
                if let Some(previous) = previous {
                    // SAFETY: All values in `self` are valid.
                    let previous = unsafe { &mut *previous.as_ptr() };
                    previous.next = current;
                } else {
                    self.values = current;
                }

                // SAFETY: `value` is valid.
                unsafe {
                    self.free_object(value);
                }
            }
        }
    }

    /// ## Safety
    ///
    /// - Any memory allocated in `self` which is accessed after this method is called must be
    ///     reachable from an element of `self.roots` or `self.temp_roots`.
    ///
    /// - All values in `self` must be valid.
    unsafe fn collect(&mut self) {
        // SAFETY: Must be ensured by caller.
        unsafe {
            self.mark_roots();
        }

        // SAFETY: All reachable memory has just been marked.
        unsafe {
            self.sweep();
        }

        self.next_gc *= Self::HEAP_GROW_FACTOR;
    }
}

// SAFETY: Every pointer in a `GarbageCollector` is owned by that collector.
unsafe impl<A: Send> Send for GarbageCollector<A> {}

static GARBAGE_COLLECTOR: Mutex<GarbageCollector<Global>> = Mutex::new(GarbageCollector {
    values: None,
    roots: Vec::new(),
    temp_roots: Vec::new(),
    bytes_allocated: 0,
    next_gc: 1024 * 1024,
    allocator: Global,
});

/// ## Safety
///
/// `ptr` must be a valid pointer to a (possibly uninitialised) `GcValue<()>`.
unsafe fn track_object(ptr: NonNull<GcValue<()>>, size: usize) {
    let mut gc = GARBAGE_COLLECTOR.lock().unwrap();
    gc.bytes_allocated += size;
    if gc.bytes_allocated > gc.next_gc {
        // SAFETY: The only unreachable object is `ptr`, which is not yet tracked.
        unsafe {
            gc.collect();
        }
    }

    // SAFETY: `ptr` is a valid pointer to a `GcValue<()>`.
    let next_ptr: *mut Option<NonNull<GcValue<()>>> = unsafe {
        ptr.as_ptr()
            .byte_add(mem::offset_of!(GcValue<()>, next))
            .cast()
    };
    // SAFETY: `next_ptr` is valid.
    unsafe {
        next_ptr.write(gc.values);
    }
    gc.values = Some(ptr);

    drop(gc);

    // SAFETY: `ptr` is a valid pointer to a `GcValue<()>`.
    let mark_ptr: *mut bool = unsafe {
        ptr.as_ptr()
            .byte_add(mem::offset_of!(GcValue<()>, mark))
            .cast()
    };
    // SAFETY: `next_ptr` is valid.
    unsafe {
        mark_ptr.write(true);
    }
}

/// ## Safety
///
/// `layout` must be a valid layout. In particular, it must accurately describe the locations of
/// pointers in the allocated value, and `layout.size()` and `layout.align()` must fit the
/// preconditions of [`Layout::from_size_align`].
///
/// ## Panics
///
/// Panics if `layout` is a `TyLayout::String` or if another garbage collection operation has
/// previously panicked.
#[no_mangle]
pub unsafe extern "C" fn cont_rt_alloc_gc(layout: &'static TyLayout<'static>) -> NonNull<()> {
    #[cfg(debug_assertions)]
    debug!("allocating object with layout {layout:?}");

    let size = layout
        .size()
        .expect("cannot allocate string with 'cont_rt_alloc_gc'");
    debug_assert!(size >= 8);
    let size = size as usize + mem::size_of::<GcValue<()>>();
    let align = (layout.align() as usize).max(mem::align_of::<GcValue<()>>());

    // SAFETY: Must be ensured by caller.
    let mem_layout = unsafe { Layout::from_size_align_unchecked(size, align) };
    let ptr = GARBAGE_COLLECTOR
        .lock()
        .unwrap()
        .allocator
        .allocate_zeroed(mem_layout)
        .unwrap_or_else(|_| handle_alloc_error(mem_layout));

    let ptr: NonNull<GcValue<()>> = ptr.cast();
    let layout_ptr: *mut &TyLayout = ptr.as_ptr().cast();

    // SAFETY: `ptr` has just been allocated with enough size to hold at least a `usize`.
    unsafe {
        layout_ptr.write(layout);
    }

    // SAFETY: `ptr` is a valid pointer to a `GcValue<()>`.
    unsafe {
        track_object(ptr, size);
    }

    // SAFETY: See above.
    let value_ptr = unsafe { ptr.as_ptr().byte_add(mem::offset_of!(GcValue<()>, value)) };
    // SAFETY: `value_ptr` is directly derived from a `NonNull`.
    unsafe { NonNull::new_unchecked(value_ptr.cast()) }
}

/// ## Safety
///
/// - `ptr` must point to memory allocated with [`cont_rt_alloc_gc`], and must not have
///     previously been passed to this function.
///
/// - All objects allocated with [`cont_rt_alloc_gc`] must be reachable from `ptr` or an object
///     previously marked with [`cont_rt_mark_root`].
///
/// ## Panics
///
/// Panics if a garbage collection operation has previously panicked.
#[no_mangle]
pub unsafe extern "C" fn cont_rt_mark_root(ptr: NonNull<()>) {
    // SAFETY: Must be ensured by caller.
    let value: *mut GcValue<()> =
        unsafe { ptr.as_ptr().sub(mem::offset_of!(GcValue<()>, value)).cast() };
    // SAFETY: Garbage collected pointers are always non-null.
    let value = unsafe { NonNull::new_unchecked(value) };
    let mut gc = GARBAGE_COLLECTOR.lock().unwrap();
    gc.roots.push(value);
    gc.temp_roots.clear();
}

/// ## Safety
///
/// `ptr` must point to memory allocated with [`cont_rt_alloc_gc`] and marked by
/// [`cont_rt_mark_root`], and must not have previously been passed to this function.
///
/// ## Panics
///
/// Panics if a garbage collection operation has previously panicked.
#[no_mangle]
#[allow(clippy::significant_drop_in_scrutinee)]
pub unsafe extern "C" fn cont_rt_unmark_root(ptr: NonNull<()>) {
    // SAFETY: Must be ensured by caller.
    let value: *mut GcValue<()> = unsafe {
        ptr.as_ptr()
            .byte_sub(mem::offset_of!(GcValue<()>, value))
            .cast()
    };
    let mut gc = GARBAGE_COLLECTOR.lock().unwrap();
    for (i, &root) in gc.roots.iter().rev().enumerate() {
        if root.as_ptr() == value {
            gc.roots.remove(i);
            drop(gc);
            break;
        }
    }
}

#[no_mangle]
#[allow(clippy::missing_panics_doc)]
pub extern "C" fn cont_rt_alloc_string(len: usize) -> NonNull<()> {
    #[cfg(debug_assertions)]
    debug!("allocating string with length {len}");

    let size = len + mem::size_of::<GcValue<()>>();
    let mem_layout = Layout::from_size_align(size, mem::align_of::<GcValue<()>>()).unwrap();

    let ptr: NonNull<GcValue<()>> = GARBAGE_COLLECTOR
        .lock()
        .unwrap()
        .allocator
        .allocate(mem_layout)
        .unwrap_or_else(|_| handle_alloc_error(mem_layout))
        .cast();
    let layout_ptr: NonNull<&TyLayout> = ptr.cast();
    // SAFETY: `ptr` has just been allocated with enough space for a `usize`.
    unsafe {
        layout_ptr.as_ptr().write(&STRING_LAYOUT);
    }

    // SAFETY: See above.
    let value_ptr = unsafe { ptr.as_ptr().byte_add(mem::offset_of!(GcValue<()>, value)) };

    // SAFETY: `ptr` is a valid pointer to a `GcValue<()>`.
    unsafe {
        track_object(ptr, size);
    }

    // SAFETY: `value_ptr` is directly derived from a `NonNull`.
    unsafe { NonNull::new_unchecked(value_ptr.cast()) }
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
