use super::*;

use crate::slice::Slice;

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

/// # Safety
///
/// - `layout` must be valid for `T`.
///
/// - The returned value must not be used after it is collected.
unsafe fn alloc_value<'a, T: 'a>(layout: &'static TyLayout<'static>, value: T) -> NonNull<T> {
    let stack_frame = StackFrame {
        return_address: 0,
        stack_pointer: &(),
    };
    // SAFETY: `I64_LAYOUT` is valid.
    let ptr: NonNull<T> = unsafe { alloc_gc(layout, &stack_frame).cast() };
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

    // SAFETY: `I64_LAYOUT` is valid.
    let y = unsafe { alloc_value(&I64_LAYOUT, 7i64) };

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

    // SAFETY: `I64_BOX_LAYOUT` is valid.
    let x_box = unsafe { alloc_value(&I64_BOX_LAYOUT, I64Box(x)) };

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
