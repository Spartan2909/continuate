use std::cell::OnceCell;
use std::cell::RefCell;
use std::ops;

pub(crate) struct LinkedList<T> {
    initialiser: fn() -> T,
    first: OnceCell<Box<Node<T>>>,
}

impl<T> LinkedList<T> {
    pub const fn new(initialiser: fn() -> T) -> LinkedList<T> {
        LinkedList {
            initialiser,
            first: OnceCell::new(),
        }
    }

    pub fn get(&self) -> impl ops::DerefMut<Target = T> + use<'_, T> {
        let mut node = &self.first;
        while let Some(next) = node.get() {
            if let Ok(ctx) = next.ctx.try_borrow_mut() {
                return ctx;
            }
            node = &next.next;
        }

        let _ = node.set(Box::new(Node::new((self.initialiser)())));
        node.get().unwrap().ctx.borrow_mut()
    }
}

struct Node<T> {
    ctx: RefCell<T>,
    next: OnceCell<Box<Node<T>>>,
}

impl<T> Node<T> {
    const fn new(value: T) -> Node<T> {
        Node {
            ctx: RefCell::new(value),
            next: OnceCell::new(),
        }
    }
}
