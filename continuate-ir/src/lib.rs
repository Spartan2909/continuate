#![feature(allocator_api)]

pub type HashMap<'a, K, V> =
    hashbrown::HashMap<K, V, hashbrown::hash_map::DefaultHashBuilder, &'a bumpalo::Bump>;

pub type Vec<'a, T> = std::vec::Vec<T, &'a bumpalo::Bump>;

pub fn collect_into<T, I, C>(iter: I, mut initial: C) -> C
where
    I: IntoIterator<Item = T>,
    C: Extend<T>,
{
    initial.extend(iter);
    initial
}

fn try_collect_into<T, E, I, C>(iter: I, mut initial: C) -> Result<C, E>
where
    I: IntoIterator<Item = Result<T, E>>,
    C: Extend<T>,
{
    for item in iter {
        initial.extend(Some(item?));
    }
    Ok(initial)
}

pub mod bimap;
pub mod common;
pub mod high_level_ir;
pub mod ir_interpreter;
pub mod lib_std;
pub mod mid_level_ir;
