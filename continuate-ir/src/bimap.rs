use crate::HashMap;

use std::borrow::Borrow;
use std::hash::Hash;
use std::rc::Rc;
use std::{fmt, ptr};

use bumpalo::Bump;

#[derive(PartialEq, Eq, Hash)]
struct Ref<'arena, T: ?Sized>(Rc<T, &'arena Bump>);

impl<T: ?Sized> Clone for Ref<'_, T> {
    fn clone(&self) -> Self {
        Ref(Rc::clone(&self.0))
    }
}

impl<T: fmt::Debug + ?Sized> fmt::Debug for Ref<'_, T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        fmt::Debug::fmt(&*self.0, f)
    }
}

#[repr(transparent)]
#[derive(PartialEq, Eq, Hash)]
struct Wrapper<T: ?Sized>(T);

impl<T: ?Sized> Wrapper<T> {
    const fn wrap(value: &T) -> &Self {
        // SAFETY: `Self` is `repr(transparent)`, so `Self` and `T` are the same.
        unsafe { &*(ptr::from_ref(value) as *const Self) }
    }
}

impl<'arena, K, Q> Borrow<Wrapper<Q>> for Ref<'arena, K>
where
    K: Borrow<Q>,
    Q: ?Sized,
{
    fn borrow(&self) -> &Wrapper<Q> {
        let k: &K = self.0.borrow();
        let q: &Q = k.borrow();
        Wrapper::wrap(q)
    }
}

pub enum Overwritten<L, R> {
    Neither,
    Left(L, R),
    Right(L, R),
    Pair(L, R),
    Both((L, R), (L, R)),
}

pub struct BiMap<'arena, L, R> {
    left: HashMap<'arena, Ref<'arena, L>, Ref<'arena, R>>,
    right: HashMap<'arena, Ref<'arena, R>, Ref<'arena, L>>,
    arena: &'arena Bump,
}

impl<'arena, L, R> BiMap<'arena, L, R> {
    pub fn new(arena: &'arena Bump) -> BiMap<'arena, L, R> {
        BiMap {
            left: HashMap::new_in(arena),
            right: HashMap::new_in(arena),
            arena,
        }
    }

    pub fn iter(&self) -> Iter<L, R> {
        Iter {
            inner: self.left.iter(),
        }
    }

    pub fn left_values(&self) -> LeftValues<L, R> {
        LeftValues { inner: self.iter() }
    }
}

impl<'arena, L: Eq + Hash, R: Eq + Hash> BiMap<'arena, L, R> {
    pub fn get_by_left<Q>(&self, left: &Q) -> Option<&R>
    where
        L: Borrow<Q>,
        Q: Eq + Hash + ?Sized,
    {
        self.left.get(Wrapper::wrap(left)).map(|right| &*right.0)
    }

    pub fn get_by_right<Q>(&self, right: &Q) -> Option<&L>
    where
        R: Borrow<Q>,
        Q: Eq + Hash + ?Sized,
    {
        self.right.get(Wrapper::wrap(right)).map(|left| &*left.0)
    }

    #[allow(clippy::missing_panics_doc)]
    pub fn remove_by_left<Q>(&mut self, left: &Q) -> Option<(L, R)>
    where
        L: Borrow<Q>,
        Q: Eq + Hash + ?Sized,
    {
        self.left.remove(Wrapper::wrap(left)).map(|right_rc| {
            let left_rc = self.right.remove(&right_rc).unwrap();
            (
                Rc::try_unwrap(left_rc.0).ok().unwrap(),
                Rc::try_unwrap(right_rc.0).ok().unwrap(),
            )
        })
    }

    #[allow(clippy::missing_panics_doc)]
    pub fn remove_by_right<Q>(&mut self, right: &Q) -> Option<(L, R)>
    where
        R: Borrow<Q>,
        Q: Eq + Hash + ?Sized,
    {
        self.right.remove(Wrapper::wrap(right)).map(|left_rc| {
            let right_rc = self.left.remove(&left_rc).unwrap();
            (
                Rc::try_unwrap(left_rc.0).ok().unwrap(),
                Rc::try_unwrap(right_rc.0).ok().unwrap(),
            )
        })
    }

    pub fn insert(&mut self, left: L, right: R) -> Overwritten<L, R> {
        let value = match (self.remove_by_left(&left), self.remove_by_right(&right)) {
            (None, None) => Overwritten::Neither,
            (None, Some((left, right))) => Overwritten::Right(left, right),
            (Some(l_pair), None) => {
                if l_pair.1 == right {
                    Overwritten::Pair(l_pair.0, l_pair.1)
                } else {
                    Overwritten::Left(l_pair.0, l_pair.1)
                }
            }
            (Some(l_pair), Some(r_pair)) => Overwritten::Both(l_pair, r_pair),
        };
        self.insert_unchecked(left, right);
        value
    }

    fn insert_unchecked(&mut self, left: L, right: R) {
        let left = Ref(Rc::new_in(left, self.arena));
        let right = Ref(Rc::new_in(right, self.arena));
        self.left.insert(left.clone(), right.clone());
        self.right.insert(right, left);
    }
}

impl<L: fmt::Debug, R: fmt::Debug> fmt::Debug for BiMap<'_, L, R> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        fmt::Debug::fmt(&self.left, f)
    }
}

pub struct IntoIter<'arena, L, R> {
    inner: hashbrown::hash_map::IntoIter<Ref<'arena, L>, Ref<'arena, R>, &'arena Bump>,
}

impl<L, R> Iterator for IntoIter<'_, L, R> {
    type Item = (L, R);

    fn next(&mut self) -> Option<Self::Item> {
        self.inner.next().map(|(l, r)| {
            (
                Rc::try_unwrap(l.0).ok().unwrap(),
                Rc::try_unwrap(r.0).ok().unwrap(),
            )
        })
    }
}

impl<'arena, L, R> IntoIterator for BiMap<'arena, L, R> {
    type Item = (L, R);
    type IntoIter = IntoIter<'arena, L, R>;

    fn into_iter(self) -> Self::IntoIter {
        IntoIter {
            inner: self.left.into_iter(),
        }
    }
}

pub struct Iter<'arena, L, R> {
    inner: hashbrown::hash_map::Iter<'arena, Ref<'arena, L>, Ref<'arena, R>>,
}

impl<'arena, L, R> Iterator for Iter<'arena, L, R> {
    type Item = (&'arena L, &'arena R);

    fn next(&mut self) -> Option<Self::Item> {
        self.inner.next().map(|(l, r)| (&*l.0, &*r.0))
    }
}

impl<'arena, L, R> IntoIterator for &'arena BiMap<'arena, L, R> {
    type Item = (&'arena L, &'arena R);
    type IntoIter = Iter<'arena, L, R>;

    fn into_iter(self) -> Self::IntoIter {
        self.iter()
    }
}

pub struct LeftValues<'arena, L, R> {
    inner: Iter<'arena, L, R>,
}

impl<'arena, L, R> Iterator for LeftValues<'arena, L, R> {
    type Item = &'arena L;

    fn next(&mut self) -> Option<Self::Item> {
        self.inner.next().map(|(l, _)| l)
    }
}
