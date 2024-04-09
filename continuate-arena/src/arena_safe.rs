use std::cell::Cell;
use std::cell::OnceCell;
use std::cell::RefCell;
use std::cell::UnsafeCell;
use std::collections::BTreeMap;
use std::collections::BTreeSet;
use std::collections::BinaryHeap;
use std::collections::HashMap;
use std::collections::HashSet;
use std::collections::LinkedList;
use std::collections::VecDeque;
use std::rc::Rc;
use std::rc::Weak as WeakRc;
use std::sync::Arc;
use std::sync::Mutex;
use std::sync::Weak as WeakArc;

/// Types that can safely be allocated in an arena.
///
/// The trait [`AutoArenaSafe`] can be implemented for `'static` types to provide an implementation
/// of `ArenaSafe`.
///
/// ## Safety
///
/// The destructor of this type must not refer to data allocated in the same arena.
///
/// This is trivially true for types with no `Drop` implementation and whose constituent parts
/// are `ArenaSafe`.
pub unsafe trait ArenaSafe {}

// SAFETY: `&T` doesn't need `Drop`.
unsafe impl<'a, T: ArenaSafe> ArenaSafe for &'a T {}

// SAFETY: `&mut T` doesn't need `Drop`.
unsafe impl<'a, T: ArenaSafe> ArenaSafe for &'a mut T {}

macro_rules! impl_arena_safe {
    (
        $($ty:ident $(
            <$($ty_param:ident),* $(,)?>
        )?),* $(,)?
    ) => {
        $(
            // SAFETY: All of `$ty`'s fields are `ArenaSafe`.
            unsafe impl<$($($ty_param : ArenaSafe),*)?> ArenaSafe for $ty<$($($ty_param),*)?> {}
        )*
    };
}

impl_arena_safe![
    i8,
    i16,
    i32,
    i64,
    i128,
    isize,
    u8,
    u16,
    u32,
    u64,
    u128,
    usize,
    f32,
    f64,
    String,
    Box<T>,
    Cell<T>,
    OnceCell<T>,
    RefCell<T>,
    UnsafeCell<T>,
    BTreeMap<K, V>,
    BTreeSet<T>,
    BinaryHeap<T>,
    LinkedList<T>,
    VecDeque<T>,
    Option<T>,
    Rc<T>,
    WeakRc<T>,
    Result<T, E>,
    Arc<T>,
    Mutex<T>,
    WeakArc<T>,
    Vec<T>,
];

// SAFETY: Arrays do not introspect on drop.
unsafe impl<T: ArenaSafe, const N: usize> ArenaSafe for [T; N] {}

// SAFETY: `HashMap` does not introspect on drop.
unsafe impl<K: ArenaSafe, V: ArenaSafe, S> ArenaSafe for HashMap<K, V, S> {}

// SAFETY: `HashMap` does not introspect on drop.
unsafe impl<T: ArenaSafe, S> ArenaSafe for HashSet<T, S> {}

macro_rules! tuple_impl {
    () => {
        tuple_impl!(@impl);
    };
    ($T:ident $( $U:ident )*) => {
        tuple_impl!($( $U )*);
        tuple_impl!(@impl $T $( $U )*);
    };
    (@impl $( $T:ident )*) => {
        // SAFETY: Tuples do not inspect their contents on drop.
        unsafe impl<$( $T: ArenaSafe, )*> ArenaSafe for ($( $T, )*) {}
    };
}

tuple_impl!(E D C B A Z Y X W V U T);
