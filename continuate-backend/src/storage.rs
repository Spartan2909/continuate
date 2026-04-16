use std::{
    iter, ops,
    sync::{Mutex, MutexGuard, OnceLock},
};

pub(crate) struct Storage<T> {
    initialiser: fn() -> T,
    first: OnceLock<Box<Node<T>>>,
}

impl<T> Storage<T> {
    pub const fn new(initialiser: fn() -> T) -> Storage<T> {
        Storage {
            initialiser,
            first: OnceLock::new(),
        }
    }

    pub fn get(&self) -> impl ops::DerefMut<Target = T> + use<'_, T> {
        let mut node = &self.first;
        let mut new_len = 8;
        while let Some(next) = node.get() {
            new_len = new_len.max(next.values.len() * 2);
            if let Some(value) = next.get() {
                return value;
            }
            node = &next.next;
        }

        if let Some(value) = node
            .get_or_init(|| Box::new(Node::new(new_len, self.initialiser)))
            .get()
        {
            value
        } else {
            self.get()
        }
    }
}

struct Node<T> {
    values: Box<[Mutex<T>]>,
    next: OnceLock<Box<Node<T>>>,
}

impl<T> Node<T> {
    fn new(len: usize, mut initialiser: impl FnMut() -> T) -> Node<T> {
        Node {
            values: iter::repeat_with(|| Mutex::new(initialiser()))
                .take(len)
                .collect(),
            next: OnceLock::new(),
        }
    }

    fn get(&self) -> Option<MutexGuard<'_, T>> {
        for value in &self.values {
            if let Ok(l) = value.try_lock() {
                return Some(l);
            }
        }
        None
    }
}
