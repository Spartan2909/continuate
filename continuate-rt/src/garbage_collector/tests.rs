use super::*;

use continuate_common::Slice;

static I64_LAYOUT: TyLayout = TyLayout::Single(SingleLayout {
    size: 8,
    align: 8,
    field_locations: Slice::new(&[]),
    gc_pointer_locations: Slice::new(&[]),
});

#[derive(Clone, Copy)]
struct I64Box(NonNull<i64>);

static I64_BOX_LAYOUT: TyLayout = TyLayout::Single(SingleLayout {
    size: 8,
    align: 8,
    field_locations: Slice::new(&[0]),
    gc_pointer_locations: Slice::new(&[0]),
});

/// ## Safety
///
/// - `layout` must be valid for `T`.
///
/// - The returned value must not be used after it is collected.
unsafe fn alloc_value<'a, T: 'a>(layout: &'static TyLayout<'static>, value: T) -> NonNull<T> {
    // SAFETY: `I64_LAYOUT` is valid.
    let ptr: NonNull<T> = unsafe { alloc_gc(layout).cast() };
    // SAFETY: `ptr` has just been allocated
    unsafe {
        ptr.write(value);
    }
    ptr
}

#[test]
fn simple() {
    // SAFETY: `I64_LAYOUT` is valid.
    let x = unsafe { alloc_value(&I64_LAYOUT, 5i64) };

    // SAFETY: `x` has just been allocated, and is the only unmarked pointer.
    unsafe {
        mark_root(x.cast());
    }

    // SAFETY: `I64_LAYOUT` is valid.
    let y = unsafe { alloc_value(&I64_LAYOUT, 7i64) };

    // SAFETY: `y` has just been allocated, and is the only unmarked pointer.
    unsafe {
        mark_root(y.cast());
    }

    // SAFETY: `x` must be valid.
    unsafe {
        assert_eq!(*x.as_ptr(), 5);
    }
    // SAFETY: `y` must be valid.
    unsafe {
        assert_eq!(*y.as_ptr(), 7);
    }
}

#[test]
fn link() {
    // SAFETY: `I64_LAYOUT` is valid.
    let x = unsafe { alloc_value(&I64_LAYOUT, 3i64) };

    // SAFETY: `x` is a valid garbage-collected pointer.
    unsafe {
        mark_root(x.cast());
    }

    // SAFETY: `I64_BOX_LAYOUT` is valid.
    let x_box = unsafe { alloc_value(&I64_BOX_LAYOUT, I64Box(x)) };

    // SAFETY: `x` is a valid marked, garbage-collected pointer.
    unsafe {
        unmark_root(x.cast());
    }

    // SAFETY: `x_box` has just been allocated.
    unsafe {
        mark_root(x_box.cast());
    }

    // SAFETY: `x` must be valid.
    unsafe {
        assert_eq!(*x.as_ptr(), 3);
    }
    // SAFETY: `x_box` must be valid.
    let x_box = unsafe { x_box.as_ptr().read() };
    // SAFETY: `x_box.0` must be valid.
    unsafe {
        assert_eq!(*x_box.0.as_ptr(), 3);
    }
}
