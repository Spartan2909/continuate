#![feature(allocator_api)]

use bumpalo::Bump;

pub type Box<'a, T> = std::boxed::Box<T, &'a Bump>;
