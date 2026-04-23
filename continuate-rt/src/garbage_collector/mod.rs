use crate::{
    debug,
    layout::{SingleLayout, TyLayout},
};

use std::{
    alloc::{self, Layout, handle_alloc_error},
    ffi::{CStr, c_char},
    fmt, mem,
    ptr::{self, NonNull},
    slice,
    sync::{
        Mutex, PoisonError,
        atomic::{AtomicPtr, Ordering},
    },
};

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

struct GarbageCollector {
    values: Option<NonNull<GcValue<()>>>,
    bytes_allocated: usize,
    next_gc: usize,
}

/// # Safety
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

#[repr(C)]
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct StackFrame {
    pub return_address: usize,
    pub stack_pointer: *const (),
}

#[repr(align(8))]
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct StackMap {
    pub return_address: usize,
    pub entry: *const u64,
}

#[repr(C, align(8))]
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct StackMapEntry {
    pub offset: u32,
    pub size: u32,
}

impl StackMapEntry {
    const fn normalise(self) -> StackMapEntry {
        StackMapEntry {
            offset: self.offset.to_le(),
            size: self.size.to_le(),
        }
    }
}

static STACK_MAPS_LOCK: Mutex<()> = Mutex::new(());

static STACK_MAPS_PTR: AtomicPtr<StackMap> = AtomicPtr::new(ptr::null_mut());

#[inline]
pub fn set_stack_maps_ptr(ptr: *const ()) -> impl Drop {
    let lock = STACK_MAPS_LOCK
        .lock()
        .unwrap_or_else(PoisonError::into_inner);
    let gc_lock = GARBAGE_COLLECTOR
        .lock()
        .unwrap_or_else(PoisonError::into_inner);
    STACK_MAPS_PTR.store(ptr.cast_mut().cast(), Ordering::Relaxed);
    drop(gc_lock);
    lock
}

unsafe fn get_stack_map(return_address: usize) -> &'static [StackMapEntry] {
    let mut stack_maps = STACK_MAPS_PTR.load(Ordering::Acquire);
    let map = loop {
        // SAFETY: `stack_maps` must be valid.
        let map = unsafe { *stack_maps };
        if map.return_address == return_address {
            break map.entry;
        }
        // SAFETY: One of the stack maps is valid.
        stack_maps = unsafe { stack_maps.add(1) };
    };
    // SAFETY: `map` must be valid.
    let len = unsafe { *map }.to_le();
    let len = len as usize;
    // SAFETY: we're offsetting to just after `map`, which is fine
    let map = unsafe { map.add(1) };
    // SAFETY: `len` must be correct for `map`
    unsafe { slice::from_raw_parts(map.cast(), len) }
}

#[cfg(target_pointer_width = "32")]
type DoubleUsize = u64;

#[cfg(target_pointer_width = "64")]
type DoubleUsize = u128;

/// # Safety
///
/// `stack_frame` must be correct.
unsafe fn mark_roots(stack_frame: &StackFrame) {
    debug!("marking roots");

    // SAFETY: `stack_frame` must be correct
    let map = unsafe { get_stack_map(stack_frame.return_address) };
    for entry in map {
        debug!("marking {entry:?}");

        let entry = entry.normalise();
        let ptr: *mut () = if entry.size as usize == mem::size_of::<usize>() {
            // SAFETY: Stack map information must be valid
            let ptr = unsafe { stack_frame.stack_pointer.byte_add(entry.offset as usize) };
            // SAFETY: This is a valid pointer to a pointer
            unsafe { *ptr.cast() }
        } else {
            debug_assert_eq!(entry.size as usize, mem::size_of::<usize>() * 2);
            // SAFETY: Stack map information must be valid
            let ptr = unsafe { stack_frame.stack_pointer.byte_add(entry.offset as usize) };
            // SAFETY: This is a valid pointer to a wide pointer
            let wide: DoubleUsize = unsafe { *ptr.cast() };
            let wide = wide >> (mem::size_of::<usize>() * 8);
            let thin = wide as usize;
            ptr::with_exposed_provenance_mut(thin)
        };
        if ptr.is_null() {
            continue;
        }
        let difference = mem::offset_of!(GcValue<()>, value);
        // SAFETY: `ptr` is a pointer to a `GcValue`.
        let gc_value = unsafe { ptr.byte_sub(difference) };
        // SAFETY: This is a valid `GcObject`
        unsafe {
            mark_object(gc_value.cast());
        }
    }
}

impl GarbageCollector {
    const HEAP_GROW_FACTOR: usize = 2;

    /// # Safety
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

    /// # Safety
    ///
    /// - Any memory allocated in `self` which is accessed after this method is called must be marked.
    /// - All values in `self` must be valid.
    unsafe fn sweep(&mut self) {
        debug!("sweeping");

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

    /// # Safety
    ///
    /// - Any memory allocated in `self` which is accessed after this method is called must be  reachable from an element of `self.roots` or `self.temp_roots`.
    /// - All values in `self` must be valid.
    unsafe fn collect(&mut self, stack_frame: &StackFrame) {
        // SAFETY: Must be ensured by caller.
        unsafe {
            mark_roots(stack_frame);
        }

        // SAFETY: All reachable memory has just been marked.
        unsafe {
            self.sweep();
        }

        self.next_gc *= Self::HEAP_GROW_FACTOR;
    }

    /// # Safety
    ///
    /// `ptr` must be a valid pointer to a (possibly uninitialised) `GcValue<()>` allocated in `gc`.
    unsafe fn track_object(
        &mut self,
        ptr: NonNull<GcValue<()>>,
        size: usize,
        stack_frame: &StackFrame,
    ) {
        self.bytes_allocated += size;
        if cfg!(debug_assertions) || self.bytes_allocated > self.next_gc {
            debug!("collecting garbage");
            // SAFETY: The only unreachable object is `ptr`, which is not yet tracked.
            unsafe {
                self.collect(stack_frame);
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
    }

    /// # Safety
    ///
    /// - All values in `self` must be valid.
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
    bytes_allocated: 0,
    next_gc: 1024 * 1024,
});

/// # Safety
///
/// - `layout` must be a valid layout.
///   In particular, it must accurately describe the locations of pointers in the allocated value, and `layout.size()` and `layout.align()` must fit the preconditions of [`Layout::from_size_align`].
/// - The contents of `stack_frame` must be correct.
///
/// # Panics
///
/// Panics if `layout` describes a string.
#[unsafe(export_name = "cont_rt_alloc_gc")]
pub unsafe extern "C-unwind" fn alloc_gc(
    layout: &'static TyLayout<'static>,
    stack_frame: &StackFrame,
) -> NonNull<()> {
    debug!("allocating object with layout {layout:?}");

    let size = layout
        .size()
        .expect("cannot allocate string with 'cont_rt_alloc_gc'");
    let size = size as usize + mem::size_of::<GcValue<()>>();
    let align = (layout.align() as usize).max(mem::align_of::<GcValue<()>>());

    let mut gc = GARBAGE_COLLECTOR
        .lock()
        .unwrap_or_else(PoisonError::into_inner);

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
        gc.track_object(ptr, size, stack_frame);
    }

    drop(gc);

    // SAFETY: See above.
    let value_ptr = unsafe { &raw mut (*ptr.as_ptr()).value };
    // SAFETY: `value_ptr` is directly derived from a `NonNull`.
    unsafe { NonNull::new_unchecked(value_ptr.cast()) }
}

/// # Safety
///
/// The contents of `stack_frame` must be correct.
///
/// # Panics
///
/// Panics if `len` is greater than `isize::MAX` when rounded up to a multiple of 8.
#[unsafe(export_name = "cont_rt_alloc_string")]
pub unsafe extern "C-unwind" fn alloc_string(len: usize, stack_frame: &StackFrame) -> NonNull<()> {
    debug!("allocating string with length {len}");

    let size = len + mem::size_of::<GcValue<()>>();
    let mem_layout = Layout::from_size_align(size, mem::align_of::<GcValue<()>>()).unwrap();

    let mut gc = GARBAGE_COLLECTOR
        .lock()
        .unwrap_or_else(PoisonError::into_inner);

    // SAFETY: `GcValue`s are not zero-sized.
    let ptr: NonNull<GcValue<()>> = unsafe {
        NonNull::new(alloc::alloc_zeroed(mem_layout).cast())
            .unwrap_or_else(|| handle_alloc_error(mem_layout))
    };
    let layout_ptr: NonNull<&TyLayout> = ptr.cast();
    // SAFETY: `ptr` has just been allocated with enough space for a `usize`.
    unsafe {
        layout_ptr.as_ptr().write(&TyLayout::String);
    }

    // SAFETY: See above.
    let value_ptr = unsafe { ptr.as_ptr().byte_add(mem::offset_of!(GcValue<()>, value)) };

    // SAFETY: `ptr` is a valid pointer to a `GcValue<()>`.
    unsafe {
        gc.track_object(ptr, size, stack_frame);
    }

    drop(gc);

    // SAFETY: `value_ptr` is directly derived from a `NonNull`.
    unsafe { NonNull::new_unchecked(value_ptr.cast()) }
}

/// # Safety
///
/// - All garbage-collected value must be valid.
/// - No garbage-collected values may be accessed again.
#[inline]
pub unsafe fn clear() {
    // SAFETY: Must be ensured by caller.
    unsafe {
        GARBAGE_COLLECTOR
            .lock()
            .unwrap_or_else(PoisonError::into_inner)
            .clear();
    }
}

#[cfg(test)]
mod tests;
