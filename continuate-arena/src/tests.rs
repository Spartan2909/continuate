use super::*;

#[test]
fn collect() {
    let mut arena = Arena::new();

    let x = arena.allocate(3);
    let y = arena.allocate(2);

    assert_eq!(*x, 3);
    assert_eq!(*y, 2);

    arena.collect();

    let z = arena.allocate(5);

    assert_eq!(*z, 5);
}

#[repr(align(4096))]
struct BigU8(u8);

// SAFETY: `BigU8` is `'static`.
unsafe impl ArenaSafe for BigU8 {}

#[test]
fn new_chunks() {
    let mut arena = Arena::new();

    let x = arena.allocate(BigU8(5));
    let y = arena.allocate(BigU8(7));

    {
        // SAFETY: `arena.chunks` is not mutated in this scope.
        let chunks = unsafe { &*arena.chunks.get() };
        assert_eq!(chunks.len(), 2);
    }

    let z = arena.allocate(BigU8(8));
    let w = arena.allocate(BigU8(14));

    {
        // SAFETY: `arena.chunks` is not mutated in this scope.
        let chunks = unsafe { &*arena.chunks.get() };
        assert_eq!(chunks.len(), 3);
    }

    assert_eq!(x.0, 5);
    assert_eq!(y.0, 7);
    assert_eq!(z.0, 8);
    assert_eq!(w.0, 14);

    arena.collect();

    {
        // SAFETY: `arena.chunks` is not mutated in this scope.
        let chunks = unsafe { &*arena.chunks.get() };
        assert_eq!(chunks.len(), 1);
        assert_eq!(arena.next_capacity.get(), 4096 * 8);
    }
}

struct Droppable(u8);

impl Drop for Droppable {
    fn drop(&mut self) {
        eprintln!("dropping Droppable with contents: {}", self.0);
    }
}

// SAFETY: `Droppable` is `'static`.
unsafe impl ArenaSafe for Droppable {}

#[test]
fn drop() {
    let arena = Arena::new();

    arena.allocate(Droppable(0));
    arena.allocate(Droppable(1));
}
