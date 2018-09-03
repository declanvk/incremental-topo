use std::{
    borrow::Borrow,
    cmp::min,
    collections::{
        hash_map::{self, RandomState},
        HashMap,
    },
    hash::{BuildHasher, Hash, Hasher},
    iter,
};

type LeftHash = u64;
type RightHash = u64;

#[derive(Clone, Debug, Eq, PartialEq)]
pub enum Overwritten<L, R> {
    // Neither the left nor the right value previously existed in the `BiMap`.
    Neither,

    // The left value existed in the `BiMap`, and the previous left-right pair is returned.
    Left(L, R),

    // The right value existed in the `BiMap`, and the previous left-right pair is returned.
    Right(L, R),

    // Both the left and the right value existed in the `BiMap`, but as part of separate pairs.
    // The first tuple is the left-right pair of the previous left value, and the second is the
    // left-right pair of the previous right value.
    Both((L, R), (L, R)),

    // The left-right pair already existed in the `BiMap`, and the previous left-right pair is
    // returned.
    Pair(L, R),
}

#[derive(Debug, Clone, Default)]
pub struct BiMap<L, R, S: BuildHasher = RandomState> {
    hash_builder: S,
    left_to_right: HashMap<LeftHash, R, S>,
    right_to_left: HashMap<RightHash, L, S>,
}

impl<L, R> BiMap<L, R>
where
    L: Hash + Eq,
    R: Hash + Eq,
{
    pub fn new() -> BiMap<L, R, RandomState> {
        BiMap {
            hash_builder: RandomState::default(),
            left_to_right: HashMap::new(),
            right_to_left: HashMap::new(),
        }
    }

    pub fn with_capacity(capacity: usize) -> BiMap<L, R, RandomState> {
        BiMap {
            hash_builder: RandomState::default(),
            left_to_right: HashMap::with_capacity(capacity),
            right_to_left: HashMap::with_capacity(capacity),
        }
    }
}

impl<L, R, S> BiMap<L, R, S>
where
    L: Hash + Eq,
    R: Hash + Eq,
    S: BuildHasher,
{
    pub fn with_hasher(hash_builder: S) -> BiMap<L, R, S>
    where
        S: Clone,
    {
        BiMap {
            hash_builder: hash_builder.clone(),
            left_to_right: HashMap::with_hasher(hash_builder.clone()),
            right_to_left: HashMap::with_hasher(hash_builder),
        }
    }

    pub fn with_capacity_and_hasher(capacity: usize, hash_builder: S) -> Self
    where
        S: Clone,
    {
        BiMap {
            hash_builder: hash_builder.clone(),
            left_to_right: HashMap::with_capacity_and_hasher(capacity, hash_builder.clone()),
            right_to_left: HashMap::with_capacity_and_hasher(capacity, hash_builder),
        }
    }

    pub fn hasher(&self) -> &S {
        &self.hash_builder
    }

    pub fn capacity(&self) -> usize {
        min(self.left_to_right.capacity(), self.right_to_left.capacity())
    }

    pub fn reserve(&mut self, additional: usize) {
        self.left_to_right.reserve(additional);
        self.right_to_left.reserve(additional);
    }

    pub fn shrink_to_fit(&mut self) {
        self.left_to_right.shrink_to_fit();
        self.right_to_left.shrink_to_fit();
    }

    pub fn len(&self) -> usize {
        min(self.left_to_right.len(), self.right_to_left.len())
    }

    pub fn is_empty(&self) -> bool {
        self.left_to_right.is_empty() && self.right_to_left.is_empty()
    }

    pub fn clear(&mut self) {
        self.left_to_right.clear();
        self.right_to_left.clear();
    }

    pub fn iter(&self) -> Iter<L, R> {
        Iter {
            inner: self.right_to_left.values().zip(self.left_to_right.values()),
        }
    }

    pub fn iter_mut(&mut self) -> IterMut<L, R> {
        IterMut {
            inner: self
                .right_to_left
                .values_mut()
                .zip(self.left_to_right.values_mut()),
        }
    }

    pub fn drain(&mut self) -> Drain<L, R> {
        Drain {
            inner: self.right_to_left.drain().zip(self.left_to_right.drain()),
        }
    }

    pub fn left_values(&mut self) -> Values<L> {
        Values {
            inner: self.right_to_left.values(),
        }
    }

    pub fn left_values_mut(&mut self) -> ValuesMut<L> {
        ValuesMut {
            inner: self.right_to_left.values_mut(),
        }
    }

    pub fn right_values(&mut self) -> Values<R> {
        Values {
            inner: self.left_to_right.values(),
        }
    }

    pub fn right_values_mut(&mut self) -> ValuesMut<R> {
        ValuesMut {
            inner: self.left_to_right.values_mut(),
        }
    }

    pub fn get_by_left<P>(&self, left: &P) -> Option<&R>
    where
        L: Borrow<P>,
        P: Hash + Eq + ?Sized,
    {
        let left_hash = hash_value(left, self.hash_builder.build_hasher());

        self.left_to_right.get(&left_hash)
    }

    pub fn get_by_left_mut<P>(&mut self, left: &P) -> Option<&mut R>
    where
        L: Borrow<P>,
        P: Hash + Eq + ?Sized,
    {
        let left_hash = hash_value(left, self.hash_builder.build_hasher());

        self.left_to_right.get_mut(&left_hash)
    }

    pub fn get_by_right<Q>(&self, right: &Q) -> Option<&L>
    where
        R: Borrow<Q>,
        Q: Hash + Eq + ?Sized,
    {
        let right_hash = hash_value(right, self.hash_builder.build_hasher());

        self.right_to_left.get(&right_hash)
    }

    pub fn get_by_right_mut<Q>(&mut self, right: &Q) -> Option<&mut L>
    where
        R: Borrow<Q>,
        Q: Hash + Eq + ?Sized,
    {
        let right_hash = hash_value(right, self.hash_builder.build_hasher());

        self.right_to_left.get_mut(&right_hash)
    }

    pub fn contains_left<P>(&self, left: &P) -> bool
    where
        L: Borrow<P>,
        P: Hash + Eq + ?Sized,
    {
        let left_hash = hash_value(left, self.hash_builder.build_hasher());

        self.left_to_right.contains_key(&left_hash)
    }

    pub fn contains_right<Q>(&self, right: &Q) -> bool
    where
        R: Borrow<Q>,
        Q: Hash + Eq + ?Sized,
    {
        let right_hash = hash_value(right, self.hash_builder.build_hasher());

        self.right_to_left.contains_key(&right_hash)
    }

    pub fn remove_by_left<P>(&mut self, left: &P) -> Option<(L, R)>
    where
        L: Borrow<P>,
        P: Hash + Eq + ?Sized,
    {
        let left_hash = hash_value(left, self.hash_builder.build_hasher());
        if let Some(right_value) = self.left_to_right.remove(&left_hash) {
            let right_hash = hash_value(&right_value, self.hash_builder.build_hasher());
            if let Some(left_value) = self.right_to_left.remove(&right_hash) {
                Some((left_value, right_value))
            } else {
                None
            }
        } else {
            None
        }
    }

    pub fn remove_by_right<Q>(&mut self, right: &Q) -> Option<(L, R)>
    where
        R: Borrow<Q>,
        Q: Hash + Eq + ?Sized,
    {
        let right_hash = hash_value(&right, self.hash_builder.build_hasher());
        if let Some(left_value) = self.right_to_left.remove(&right_hash) {
            let left_hash = hash_value(&left_value, self.hash_builder.build_hasher());
            if let Some(right_value) = self.left_to_right.remove(&left_hash) {
                Some((left_value, right_value))
            } else {
                None
            }
        } else {
            None
        }
    }

    // insert, insert_no_overwrite, and retain are directly cribbed from the crate
    // bimap, author Billy Rieger

    pub fn insert(&mut self, left: L, right: R) -> Overwritten<L, R> {
        let result = match (self.contains_left(&left), self.contains_right(&right)) {
            (false, false) => Overwritten::Neither,
            (true, false) => {
                let prev_pair = self.remove_by_left(&left).unwrap();
                Overwritten::Left(prev_pair.0, prev_pair.1)
            },
            (false, true) => {
                let prev_pair = self.remove_by_right(&right).unwrap();
                Overwritten::Left(prev_pair.0, prev_pair.1)
            },
            (true, true) => if self.get_by_left(&left) == Some(&right) {
                let prev_pair = self.remove_by_left(&left).unwrap();
                Overwritten::Pair(prev_pair.0, prev_pair.1)
            } else {
                let left_overwritten = self.remove_by_left(&left).unwrap();
                let right_overwritten = self.remove_by_right(&right).unwrap();
                Overwritten::Both(left_overwritten, right_overwritten)
            },
        };

        let left_hash = hash_value(&left, self.hash_builder.build_hasher());
        let right_hash = hash_value(&right, self.hash_builder.build_hasher());

        self.left_to_right.insert(left_hash, right);
        self.right_to_left.insert(right_hash, left);

        result
    }

    pub fn insert_no_overwrite(&mut self, left: L, right: R) -> bool {
        if self.contains_left(&left) || self.contains_right(&right) {
            false
        } else {
            self.insert(left, right);
            true
        }
    }

    pub fn retain<F>(&mut self, mut f: F)
    where
        F: FnMut(&mut L, &mut R) -> bool,
        S::Hasher: Clone,
    {
        let hasher = self.hash_builder.build_hasher();
        let to_remove: Vec<_> = self
            .iter_mut()
            .filter_map(|(left, right)| {
                let left_hash = hash_value(left, hasher.clone());
                let right_hash = hash_value(right, hasher.clone());

                if !f(left, right) {
                    Some((left_hash, right_hash))
                } else {
                    None
                }
            }).collect();

        for (left_hash, right_hash) in to_remove {
            self.left_to_right.remove(&left_hash);
            self.right_to_left.remove(&right_hash);
        }
    }
}

fn hash_value<V, H>(value: &V, mut state: H) -> u64
where
    V: Hash + ?Sized,
    H: Hasher,
{
    value.hash(&mut state);

    state.finish()
}

pub struct Iter<'a, L, R>
where
    L: 'a,
    R: 'a,
{
    inner: iter::Zip<hash_map::Values<'a, RightHash, L>, hash_map::Values<'a, LeftHash, R>>,
}

impl<'a, L, R> Iterator for Iter<'a, L, R> {
    type Item = (&'a L, &'a R);

    fn next(&mut self) -> Option<(&'a L, &'a R)> {
        self.inner.next()
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        self.inner.size_hint()
    }
}

pub struct IterMut<'a, L, R>
where
    L: 'a,
    R: 'a,
{
    inner: iter::Zip<hash_map::ValuesMut<'a, RightHash, L>, hash_map::ValuesMut<'a, LeftHash, R>>,
}

impl<'a, L, R> Iterator for IterMut<'a, L, R> {
    type Item = (&'a mut L, &'a mut R);

    fn next(&mut self) -> Option<(&'a mut L, &'a mut R)> {
        self.inner.next()
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        self.inner.size_hint()
    }
}

pub struct Values<'a, T>
where
    T: 'a,
{
    inner: hash_map::Values<'a, u64, T>,
}

impl<'a, T> Iterator for Values<'a, T> {
    type Item = &'a T;

    fn next(&mut self) -> Option<&'a T> {
        self.inner.next()
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        self.inner.size_hint()
    }
}

pub struct ValuesMut<'a, T>
where
    T: 'a,
{
    inner: hash_map::ValuesMut<'a, u64, T>,
}

impl<'a, T> Iterator for ValuesMut<'a, T> {
    type Item = &'a mut T;

    fn next(&mut self) -> Option<&'a mut T> {
        self.inner.next()
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        self.inner.size_hint()
    }
}

pub struct IntoIter<L, R> {
    inner: iter::Zip<hash_map::IntoIter<RightHash, L>, hash_map::IntoIter<LeftHash, R>>,
}

impl<L, R> Iterator for IntoIter<L, R> {
    type Item = (L, R);

    fn next(&mut self) -> Option<Self::Item> {
        self.inner
            .next()
            .map(|pair_pair| ((pair_pair.0).1, (pair_pair.1).1))
    }
}

pub struct Drain<'a, L, R>
where
    L: 'a,
    R: 'a,
{
    inner: iter::Zip<hash_map::Drain<'a, RightHash, L>, hash_map::Drain<'a, LeftHash, R>>,
}

impl<'a, L, R> Iterator for Drain<'a, L, R>
where
    L: 'a,
    R: 'a,
{
    type Item = (L, R);

    fn next(&mut self) -> Option<Self::Item> {
        self.inner
            .next()
            .map(|pair_pair| ((pair_pair.0).1, (pair_pair.1).1))
    }
}

use std::iter::{Extend, FromIterator, IntoIterator};

impl<L, R, S: BuildHasher> IntoIterator for BiMap<L, R, S>
where
    L: Hash + Eq,
    R: Hash + Eq,
{
    type IntoIter = IntoIter<L, R>;
    type Item = (L, R);

    fn into_iter(self) -> Self::IntoIter {
        IntoIter {
            inner: self
                .right_to_left
                .into_iter()
                .zip(self.left_to_right.into_iter()),
        }
    }
}

impl<'a, L, R, S: BuildHasher> IntoIterator for &'a BiMap<L, R, S>
where
    L: 'a + Hash + Eq,
    R: 'a + Hash + Eq,
{
    type IntoIter = Iter<'a, L, R>;
    type Item = (&'a L, &'a R);

    fn into_iter(self) -> Self::IntoIter {
        self.iter()
    }
}

impl<'a, L, R, S: BuildHasher> IntoIterator for &'a mut BiMap<L, R, S>
where
    L: 'a + Hash + Eq,
    R: 'a + Hash + Eq,
{
    type IntoIter = IterMut<'a, L, R>;
    type Item = (&'a mut L, &'a mut R);

    fn into_iter(self) -> Self::IntoIter {
        self.iter_mut()
    }
}

impl<L, R, S> FromIterator<(L, R)> for BiMap<L, R, S>
where
    L: Hash + Eq,
    R: Hash + Eq,
    S: BuildHasher + Default + Clone,
{
    fn from_iter<T: IntoIterator<Item = (L, R)>>(iter: T) -> BiMap<L, R, S> {
        let mut map = BiMap::with_hasher(S::default());

        for (left, right) in iter {
            map.insert(left, right);
        }

        map
    }
}

impl<L, R, S> Extend<(L, R)> for BiMap<L, R, S>
where
    L: Hash + Eq,
    R: Hash + Eq,
    S: BuildHasher + Default + Clone,
{
    fn extend<T: IntoIterator<Item = (L, R)>>(&mut self, iter: T) {
        for (left, right) in iter {
            self.insert(left, right);
        }
    }
}
