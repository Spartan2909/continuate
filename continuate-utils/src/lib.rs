#![feature(allocator_api)]

use bumpalo::Bump;

pub type Box<'a, T> = std::boxed::Box<T, &'a Bump>;

pub type Vec<'a, T> = std::vec::Vec<T, &'a bumpalo::Bump>;

pub type HashMap<'a, K, V> =
    hashbrown::HashMap<K, V, hashbrown::DefaultHashBuilder, &'a bumpalo::Bump>;

pub type HashSet<'a, K> = hashbrown::HashSet<K, hashbrown::DefaultHashBuilder, &'a bumpalo::Bump>;

pub fn collect_into<T, I, C>(iter: I, mut initial: C) -> C
where
    I: IntoIterator<Item = T>,
    C: Extend<T>,
{
    initial.extend(iter);
    initial
}

/// ## Errors
///
/// Returns the first error in `iter`.
pub fn try_collect_into<T, E, I, C>(iter: I, mut initial: C) -> Result<C, E>
where
    I: IntoIterator<Item = Result<T, E>>,
    C: Extend<T>,
{
    for item in iter {
        initial.extend(Some(item?));
    }
    Ok(initial)
}
