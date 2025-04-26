use crate::layout::SingleLayout;
use crate::layout::TyLayout;

use std::alloc;
use std::alloc::handle_alloc_error;
use std::alloc::Layout;
use std::borrow::Borrow;
use std::ffi::c_char;
use std::ffi::CStr;
use std::fmt;
use std::hash;
use std::hash::BuildHasherDefault;
use std::mem;
use std::ptr::NonNull;
use std::sync::Mutex;

use nohash_hasher::IntSet;

#[cfg(debug_assertions)]
use tracing::debug;

static STRING_LAYOUT: TyLayout = TyLayout::String;

#[repr(C)]
struct GcValue<T: ?Sized> {
    layout: &'static TyLayout<'static>,
    mark: bool,
    next: Option<NonNull<GcValue<()>>>,
    value: T,
}

impl<T: ?Sized> GcValue<T> {
    const unsafe fn layout(this: *const GcValue<T>) -> &'static TyLayout<'static> {
        // SAFETY: Must be ensured by caller.
        let layout_ptr: *const &TyLayout =
            unsafe { this.byte_add(mem::offset_of!(GcValue<()>, layout)).cast() };
        // SAFETY: Must be ensured by caller.
        unsafe { layout_ptr.read() }
    }

    const unsafe fn mark(this: *const GcValue<T>) -> bool {
        // SAFETY: Must be ensured by caller.
        let mark_ptr: *const bool =
            unsafe { this.byte_add(mem::offset_of!(GcValue<()>, mark)).cast() };
        // SAFETY: Must be ensured by caller.
        unsafe { mark_ptr.read() }
    }

    const unsafe fn set_mark(this: *mut GcValue<T>, mark: bool) {
        // SAFETY: Must be ensured by caller.
        let mark_ptr: *mut bool =
            unsafe { this.byte_add(mem::offset_of!(GcValue<()>, mark)).cast() };
        // SAFETY: Must be ensured by caller.
        unsafe {
            mark_ptr.write(mark);
        }
    }
}

impl<T: ?Sized> fmt::Debug for GcValue<T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("GcValue")
            .field("layout", self.layout)
            .field("next", &self.next)
            .field("mark", &self.mark)
            .finish_non_exhaustive()
    }
}

#[repr(transparent)]
struct HashableGcValue<T>(NonNull<GcValue<T>>);

impl<T> Clone for HashableGcValue<T> {
    fn clone(&self) -> Self {
        *self
    }
}

impl<T> Copy for HashableGcValue<T> {}

impl<T> PartialEq for HashableGcValue<T> {
    fn eq(&self, other: &Self) -> bool {
        self.0 == other.0
    }
}

impl<T> Eq for HashableGcValue<T> {}

impl<T> hash::Hash for HashableGcValue<T> {
    fn hash<H: hash::Hasher>(&self, state: &mut H) {
        state.write_usize(self.0.as_ptr() as usize);
    }
}

impl<T> From<NonNull<GcValue<T>>> for HashableGcValue<T> {
    fn from(value: NonNull<GcValue<T>>) -> Self {
        HashableGcValue(value)
    }
}

impl<T> Borrow<NonNull<GcValue<T>>> for HashableGcValue<T> {
    fn borrow(&self) -> &NonNull<GcValue<T>> {
        &self.0
    }
}

// SAFETY: `HashableGcValue` cannot be used from safe code.
unsafe impl<T> Send for HashableGcValue<T> {}

impl<T> nohash_hasher::IsEnabled for HashableGcValue<T> {}

struct GarbageCollector {
    values: Option<NonNull<GcValue<()>>>,
    roots: IntSet<HashableGcValue<()>>,
    temp_roots: IntSet<HashableGcValue<()>>,
    bytes_allocated: usize,
    next_gc: usize,
}

/// ## Safety
///
/// `value` must be valid.
unsafe fn mark_object(value: *mut GcValue<()>) {
    // SAFETY: Must be ensured by caller.
    if unsafe { GcValue::mark(value) } {
        return;
    }

    // SAFETY: Must be ensured by caller.
    unsafe {
        GcValue::set_mark(value, true);
    }
    // SAFETY: Must be ensured by caller.
    let layout = unsafe { GcValue::layout(value) };
    let gc_pointer_locations = match *layout {
        TyLayout::Single(SingleLayout {
            gc_pointer_locations,
            ..
        }) => gc_pointer_locations.as_slice(),
        TyLayout::Sum { layouts, .. } => {
            // SAFETY: `value` is a valid pointer to a `GcValue<()>`.
            let discriminant: *mut u64 =
                unsafe { value.byte_add(mem::offset_of!(GcValue<()>, value)).cast() };
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
        let value_ptr: *const *mut () = unsafe { value.byte_add(location).cast() };
        // SAFETY: `value_ptr` is valid.
        let value = unsafe { value_ptr.read() };
        // SAFETY: `value` is a valid pointer to the `value` field of a `GcValue<()>`.
        let object = unsafe { value.byte_sub(mem::offset_of!(GcValue<()>, value)).cast() };
        // SAFETY: See above.
        unsafe {
            mark_object(object);
        }
    }
}

impl GarbageCollector {
    const HEAP_GROW_FACTOR: usize = 2;

    /// ## Safety
    ///
    /// All roots in `self` must be valid.
    unsafe fn mark_roots(&mut self) {
        for &root in self.roots.iter().chain(&self.temp_roots) {
            // SAFETY: Must be ensured by caller.
            unsafe {
                mark_object(root.0.as_ptr());
            }
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
                let size = size as usize + mem::size_of::<GcValue<()>>();
                let layout = Layout::from_size_align(size, align as usize).unwrap();
                // SAFETY: `object` was allocated with `Global` with `layout`.
                unsafe {
                    alloc::dealloc(object.cast().as_ptr(), layout);
                }
                self.bytes_allocated -= size;
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
                    alloc::dealloc(object.cast().as_ptr(), layout);
                }
                self.bytes_allocated -= size;
            }
        }
    }

    /// ## Safety
    ///
    /// - Any memory allocated in `self` which is accessed after this method is called must be
    ///   marked.
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
    ///   reachable from an element of `self.roots` or `self.temp_roots`.
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

    /// ## Safety
    ///
    /// `ptr` must be a valid pointer to a (possibly uninitialised) `GcValue<()>` allocated in `gc`.
    unsafe fn track_object(&mut self, ptr: NonNull<GcValue<()>>, size: usize) {
        self.bytes_allocated += size;
        if cfg!(test) || self.bytes_allocated > self.next_gc {
            // SAFETY: The only unreachable object is `ptr`, which is not yet tracked.
            unsafe {
                self.collect();
            }
        }

        // SAFETY: `ptr` is a valid pointer to a `GcValue<()>`.
        let mark_ptr = unsafe { &raw mut (*ptr.as_ptr()).mark };
        // SAFETY: `mark_ptr` is valid.
        unsafe { mark_ptr.write(false) }

        // SAFETY: `ptr` is a valid pointer to a `GcValue<()>`.
        let next_ptr = unsafe { &raw mut (*ptr.as_ptr()).next };
        // SAFETY: `next_ptr` is valid.
        unsafe {
            next_ptr.write(self.values);
        }
        self.values = Some(ptr);

        self.temp_roots.insert(ptr.into());
    }

    /// ## Safety
    ///
    /// - All values in `self` must be valid.
    ///
    /// - No values in `self` may be accessed again.
    unsafe fn clear(&mut self) {
        let mut current = self.values;
        while let Some(mut value) = current {
            // SAFETY: Must be ensured by caller.
            let value = unsafe { value.as_mut() };
            current = value.next;
            // SAFETY: `value` is never accessed again.
            unsafe {
                self.free_object(NonNull::from(value));
            }
        }
    }
}

// SAFETY: Every pointer in a `GarbageCollector` is owned by that collector.
unsafe impl Send for GarbageCollector {}

static GARBAGE_COLLECTOR: Mutex<GarbageCollector> = Mutex::new(GarbageCollector {
    values: None,
    roots: IntSet::with_hasher(BuildHasherDefault::new()),
    temp_roots: IntSet::with_hasher(BuildHasherDefault::new()),
    bytes_allocated: 0,
    next_gc: 1024 * 1024,
});

/// ## Safety
///
/// `layout` must be a valid layout. In particular, it must accurately describe the locations of
///     pointers in the allocated value, and `layout.size()` and `layout.align()` must fit the
///     preconditions of [`Layout::from_size_align`].
///
/// ## Panics
///
/// Panics if `layout` is a `TyLayout::String` or if another garbage collection operation has
/// previously panicked.
#[export_name = "cont_rt_alloc_gc"]
#[allow(clippy::missing_inline_in_public_items)]
pub unsafe extern "C" fn alloc_gc(layout: &'static TyLayout<'static>) -> NonNull<()> {
    #[cfg(debug_assertions)]
    debug!("allocating object with layout {layout:?}");

    let size = layout
        .size()
        .expect("cannot allocate string with 'cont_rt_alloc_gc'");
    let size = size as usize + mem::size_of::<GcValue<()>>();
    let align = (layout.align() as usize).max(mem::align_of::<GcValue<()>>());

    // SAFETY: Must be ensured by caller.
    let mut gc = GARBAGE_COLLECTOR.lock().unwrap();

    // SAFETY: Must be ensured by caller.
    let mem_layout = unsafe { Layout::from_size_align_unchecked(size, align) };
    // SAFETY: `GcValue`s are not zero-sized.
    let ptr: NonNull<GcValue<()>> = unsafe {
        NonNull::new(alloc::alloc_zeroed(mem_layout).cast())
            .unwrap_or_else(|| handle_alloc_error(mem_layout))
    };

    let ptr: NonNull<GcValue<()>> = ptr.cast();
    let layout_ptr: *mut &TyLayout = ptr.as_ptr().cast();

    // SAFETY: `ptr` has just been allocated with enough size to hold at least a `usize`.
    unsafe {
        layout_ptr.write(layout);
    }

    // SAFETY: `ptr` is a valid pointer to a `GcValue<()>`.
    unsafe {
        gc.track_object(ptr, size);
    }

    drop(gc);

    // SAFETY: See above.
    let value_ptr = unsafe { &raw mut (*ptr.as_ptr()).value };
    // SAFETY: `value_ptr` is directly derived from a `NonNull`.
    unsafe { NonNull::new_unchecked(value_ptr.cast()) }
}

/// ## Safety
///
/// - `ptr` must point to memory allocated with [`cont_rt_alloc_gc`], and must not have
///   previously been passed to this function.
///
/// - `ptr` must be valid for writes.
///
/// ## Panics
///
/// Panics if a garbage collection operation has previously panicked.
#[export_name = "cont_rt_mark_root"]
#[allow(clippy::missing_inline_in_public_items)]
pub unsafe extern "C" fn mark_root(ptr: NonNull<()>) {
    // SAFETY: Must be ensured by caller.
    let value: *mut GcValue<()> = unsafe {
        ptr.as_ptr()
            .byte_sub(mem::offset_of!(GcValue<()>, value))
            .cast()
    };
    // SAFETY: Garbage collected pointers are always non-null.
    let value = unsafe { NonNull::new_unchecked(value) };
    // SAFETY: Must be ensured by caller.
    let mut gc = GARBAGE_COLLECTOR.lock().unwrap();
    gc.roots.insert(value.into());
}

/// ## Safety
///
/// - `ptr` must point to memory allocated with [`cont_rt_alloc_gc`] and marked by
///   [`cont_rt_mark_root`], and must not have previously been passed to this function.
///
/// - The garbage collector must be initialised.
///
/// ## Panics
///
/// Panics if a garbage collection operation has previously panicked.
#[export_name = "cont_rt_unmark_root"]
#[allow(clippy::missing_inline_in_public_items)]
pub unsafe extern "C" fn unmark_root(ptr: NonNull<()>) {
    // SAFETY: Must be ensured by caller.
    let value: *mut GcValue<()> = unsafe {
        ptr.as_ptr()
            .byte_sub(mem::offset_of!(GcValue<()>, value))
            .cast()
    };
    // SAFETY: `value` is derived from a non-null pointer.
    let value = unsafe { NonNull::new_unchecked(value) };
    // SAFETY: Must be ensured by caller.
    GARBAGE_COLLECTOR.lock().unwrap().roots.remove(&value);
}

#[export_name = "cont_rt_alloc_string"]
#[allow(clippy::missing_inline_in_public_items)]
#[allow(clippy::missing_panics_doc)]
pub extern "C" fn alloc_string(len: usize) -> NonNull<()> {
    #[cfg(debug_assertions)]
    debug!("allocating string with length {len}");

    let size = len + mem::size_of::<GcValue<()>>();
    let mem_layout = Layout::from_size_align(size, mem::align_of::<GcValue<()>>()).unwrap();

    let mut gc = GARBAGE_COLLECTOR.lock().unwrap();

    // SAFETY: `GcValue`s are not zero-sized.
    let ptr: NonNull<GcValue<()>> = unsafe {
        NonNull::new(alloc::alloc_zeroed(mem_layout).cast())
            .unwrap_or_else(|| handle_alloc_error(mem_layout))
    };
    let layout_ptr: NonNull<&TyLayout> = ptr.cast();
    // SAFETY: `ptr` has just been allocated with enough space for a `usize`.
    unsafe {
        layout_ptr.as_ptr().write(&STRING_LAYOUT);
    }

    // SAFETY: See above.
    let value_ptr = unsafe { ptr.as_ptr().byte_add(mem::offset_of!(GcValue<()>, value)) };

    // SAFETY: `ptr` is a valid pointer to a `GcValue<()>`.
    unsafe {
        gc.track_object(ptr, size);
    }

    drop(gc);

    // SAFETY: `value_ptr` is directly derived from a `NonNull`.
    unsafe { NonNull::new_unchecked(value_ptr.cast()) }
}

/// ## Safety
///
/// - All garbage-collected value must be valid.
///
/// - No garbage-collected values may be accessed again.
///
/// ## Panics
///
/// Panics if a garbage collection operation has previously panicked.
#[inline]
pub unsafe fn clear() {
    // SAFETY: Must be ensured by caller.
    unsafe {
        GARBAGE_COLLECTOR.lock().unwrap().clear();
    }
}

#[cfg(test)]
mod tests;
