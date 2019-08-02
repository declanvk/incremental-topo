//! A fast two-way bijective map.
//!
//! ## Disclaimer
//!
//! This API and documentation is taken directly from Billy Rieger's
//! [`bimap-rs`]. Specific changes have been made to the implementation such
//! that left and right values can be searched for using `Borrow`ed versions of
//! themselves.
//!
//! Before the change the `get_by_left` function signature looked like this:
//! ```text
//! pub fn get_by_left(&self, left: &L) -> Option<&R>;
//! ```
//!
//! After the change the `get_by_left` function signature looks like this:
//! ```text
//! pub fn get_by_left<P>(&self, left: &P) -> Option<&R>
//! where
//!     L: Borrow<P>,
//!     P: Hash + Eq + ?Sized,
//! ```
//!
//! In order to accomodate this change, the internal representation of the bimap
//! changed slightly. Previously bimap used an internal representation of two
//! hashmaps that mapped `Rc<L> -> Rc<R>` and `Rc<R> -> Rc<L>`. The new version
//! also has two hashmaps that map `hash(L) -> R` and `hash(R) -> L`.
//!
//! Overall, this version accomplishes the bare minimum needed for a bimap,
//! while [`bimap-rs`] offers more options.
//!
//! ## Description
//!
//! A `BiMap<L, R>` is a [bijective map] between values of type `L`, called
//! left values, and values of type `R`, called right values. This means every
//! left value is associated with exactly one right value and vice versa.
//! Compare this to a [`HashMap`], where every key is associated with exactly
//! one value but a value can be associated with more than one key.
//!
//! Internally, a `BiMap` is composed of two `HashMap`s, one for the
//! left-to-right direction and one for right-to-left. As such, the big-O
//! performance of the `get`, `remove`, `insert`, and `contains` methods are
//! the same as those of a `HashMap`.
//!
//! As with `HashMap`, it is considered a logic error to modify a value's hash
//! while it is in the `BiMap` using a `Cell`, `RefCell`, etc. This is
//! especially important because both the left and right values are hashed, and
//! accessible via mutable getters.
//!
//! # Examples
//!
//! ```
//! use incremental_topo::bimap::BiMap;
//!
//! let mut elements = BiMap::new();
//!
//! // insert chemicals and their corresponding symbols
//! elements.insert("hydrogen", "H");
//! elements.insert("carbon", "C");
//! elements.insert("bromine", "Br");
//! elements.insert("neodymium", "Nd");
//!
//! // retrieve chemical symbol by name (left to right)
//! assert_eq!(elements.get_by_left(&"bromine"), Some(&"Br"));
//! assert_eq!(elements.get_by_left(&"oxygen"), None);
//!
//! // retrieve name by chemical symbol (right to left)
//! assert_eq!(elements.get_by_right(&"C"), Some(&"carbon"));
//! assert_eq!(elements.get_by_right(&"Al"), None);
//!
//! // check membership
//! assert!(elements.contains_left(&"hydrogen"));
//! assert!(!elements.contains_right(&"He"));
//!
//! // remove elements
//! assert_eq!(
//!     elements.remove_by_left(&"neodymium"),
//!     Some(("neodymium", "Nd"))
//! );
//! assert_eq!(elements.remove_by_right(&"Nd"), None);
//!
//! // iterate over elements
//! for (left, right) in elements.iter() {
//!     println!("the chemical symbol for {} is {}", left, right);
//! }
//! ```
//!
//! ## Insertion and overwriting
//!
//! Consider the following example:
//!
//! ```
//! use incremental_topo::bimap::BiMap;
//!
//! let mut bimap = BiMap::new();
//! bimap.insert('a', 1);
//! bimap.insert('b', 1); // what to do here?
//! ```
//!
//! In order to maintain the bijection, the `BiMap` cannot have both `('a', 1)`
//! and `('b', 1)` in the map. Otherwise, the right-value `1` would have two
//! left values associated with it. Either we should allow the call to `insert`
//! to go through and overwrite `('a', 1)`, or not let `('b', 1)` be inserted
//! at all. `BiMap` allows for both possibilities. To insert with overwriting,
//! use [`insert`], and to insert without overwriting, use
//! [`insert_no_overwrite`]. The return type of `insert` is the `enum`
//! [`Overwritten`], which indicates what values, if any, were overwritten; the
//! return type of `insert_no_overwrite` is a boolean indicating if the
//! insertion was successful.
//!
//! This is especially important when dealing with types that can be equal
//! while having different data. Unlike a `HashMap`, which [doesn't update an
//! equal key upon insertion], a `BiMap` updates both the left values and the
//! right values.
//!
//! ```
//! use incremental_topo::bimap::{BiMap, Overwritten};
//! use std::hash::{Hash, Hasher};
//!
//! #[derive(Clone, Copy, Debug)]
//! struct Foo {
//!     important: char,
//!     unimportant: u32,
//! }
//!
//! // equality only depends on the important data
//! impl PartialEq for Foo {
//!     fn eq(&self, other: &Foo) -> bool {
//!         self.important == other.important
//!     }
//! }
//!
//! impl Eq for Foo {}
//!
//! // hash only depends on the important data
//! impl Hash for Foo {
//!     fn hash<H: Hasher>(&self, state: &mut H) {
//!         self.important.hash(state);
//!     }
//! }
//!
//! // create two Foos that are equal but have different data
//! let foo1 = Foo {
//!     important: 'a',
//!     unimportant: 1,
//! };
//! let foo2 = Foo {
//!     important: 'a',
//!     unimportant: 2,
//! };
//! assert_eq!(foo1, foo2);
//!
//! let mut bimap = BiMap::new();
//! bimap.insert(foo1, 99);
//! let overwritten = bimap.insert(foo2, 100);
//! // foo1 is overwritten and returned; foo2 is in the bimap
//! assert_eq!(overwritten, Overwritten::Left(foo1, 99));
//! assert_eq!(bimap.get_by_right(&100), Some(&foo2));
//! ```
//!
//! [bijective map]: https://en.wikipedia.org/wiki/Bijection
//! [doesn't update an equal key upon insertion]:
//! https://doc.rust-lang.org/std/collections/index.html#insert-and-complex-keys
//! [`HashMap`]: https://doc.rust-lang.org/std/collections/struct.HashMap.html
//! [`insert`]: struct.BiMap.html#method.insert
//! [`insert_no_overwrite`]: struct.BiMap.html#method.insert_no_overwrite
//! [`Overwritten`]: enum.Overwritten.html
//! [`bimap-rs`]: https://github.com/billyrieger/bimap-rs/

use std::{
    borrow::Borrow,
    cmp::min,
    collections::{hash_map::RandomState, HashMap},
    hash::{BuildHasher, Hash, Hasher},
    iter::{Extend, FromIterator, IntoIterator},
};

type LeftHash = u64;
type RightHash = u64;

/// The previous pairs, if any, that were overwritten by a call the [`insert`]
/// method of [`BiMap`].
///
/// [`insert`]: struct.BiMap.html#method.insert
/// [`BiMap`]: struct.BiMap.html
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum Overwritten<L, R> {
    /// Neither the left or right value existed in the `BiMap`.
    Neither,

    /// The left value extisted in the `BiMap`, and the previous pair is
    /// returned.
    Left(L, R),

    /// The right value existed in the `BiMap`, and the previous pair is
    /// returned.
    Right(L, R),

    /// Both the left and right values existed in the `BiMap`, but as parts of
    /// different pairs. Both pairs are returned, the first one corresponding
    /// to the left value, and the second one corresponding to the right value
    Both((L, R), (L, R)),

    // Both the left and the right values existed in the `BiMap`, as parts of the same pair. The
    // previous pair is returned.
    Pair(L, R),
}

/// A two-way map between left values and right values.
///
/// See the [module-level documentation] for more details and examples.
///
/// [module-level documentation]: index.html
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
    /// Creates an empty `BiMap` using `RandomState` as the hash provider.
    ///
    /// # Examples
    ///
    /// ```
    /// use incremental_topo::bimap::BiMap;
    ///
    /// let mut bimap: BiMap<&'static str, u32> = BiMap::new();
    ///
    /// assert_eq!(bimap.capacity(), 0);
    /// ```
    pub fn new() -> BiMap<L, R, RandomState> {
        BiMap {
            hash_builder: RandomState::default(),
            left_to_right: HashMap::new(),
            right_to_left: HashMap::new(),
        }
    }

    /// Create an empty `BiMap` with the given capacity and `RandomState` as
    /// the hash provider.
    ///
    /// # Examples
    ///
    /// ```
    /// use incremental_topo::bimap::BiMap;
    ///
    /// let mut bimap: BiMap<char, u32> = BiMap::with_capacity(100);
    ///
    /// assert!(bimap.capacity() >= 100);
    /// ```
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
    /// Creates an empty `BiMap` which will use the given hash builder to hash
    /// keys.
    ///
    /// The created map has the default initial capacity.
    ///
    /// Warning: `hash_builder` is normally randomly generated, and
    /// is designed to allow BiMaps to be resistant to attacks that
    /// cause many collisions and very poor performance. Setting it
    /// manually using this function can expose a DoS attack vector.
    ///
    /// # Examples
    ///
    /// ```
    /// use incremental_topo::bimap::BiMap;
    /// use std::hash::{BuildHasherDefault, Hasher};
    ///
    /// #[derive(Default)]
    /// struct MyHasher;
    ///
    /// impl Hasher for MyHasher {
    ///     fn write(&mut self, bytes: &[u8]) {
    ///         // Your hashing algorithm goes here!
    ///         unimplemented!()
    ///     }
    ///
    ///     fn finish(&self) -> u64 {
    ///         // Your hashing algorithm goes here!
    ///         unimplemented!()
    ///     }
    /// }
    ///
    /// type MyBuildHasher = BuildHasherDefault<MyHasher>;
    ///
    /// let mut bimap: BiMap<&'static str, u32, MyBuildHasher> =
    ///     BiMap::with_hasher(MyBuildHasher::default());
    /// ```
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

    /// Creates an empty `BiMap` with the specified capacity, using
    /// `hash_builder` to hash the keys.
    ///
    /// The hash map will be able to hold at least `capacity` elements without
    /// reallocating. If `capacity` is 0, the map will not allocate.
    ///
    /// Warning: `hash_builder` is normally randomly generated, and
    /// is designed to allow BiMap to be resistant to attacks that
    /// cause many collisions and very poor performance. Setting it
    /// manually using this function can expose a DoS attack vector.
    ///
    /// # Examples
    ///
    /// ```
    /// use incremental_topo::bimap::BiMap;
    /// use std::collections::hash_map::RandomState;
    ///
    /// let s = RandomState::new();
    /// let mut bimap: BiMap<char, u32> = BiMap::with_capacity_and_hasher(10, s);
    /// bimap.insert('a', 32);
    /// ```
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

    /// Returns a reference to the map's [`BuildHasher`].
    ///
    /// [`BuildHasher`]: https://doc.rust-lang.org/std/hash/trait.BuildHasher.html
    ///
    /// # Examples
    ///
    /// ```
    /// use incremental_topo::bimap::BiMap;
    /// use std::collections::hash_map::RandomState;
    ///
    /// let hasher = RandomState::new();
    /// let map: BiMap<i32, i32> = BiMap::with_hasher(hasher);
    /// let hasher: &RandomState = map.hasher();
    /// ```
    pub fn hasher(&self) -> &S {
        &self.hash_builder
    }

    /// Returns the number of elements the map can hold without reallocating.
    ///
    /// This number is a lower bound; the `BiMap<L, R>` might be able to hold
    /// more, but is guaranteed to be able to hold at least this many.
    ///
    /// # Examples
    ///
    /// ```
    /// use incremental_topo::bimap::BiMap;
    ///
    /// let map: BiMap<i32, i32> = BiMap::with_capacity(20);
    /// assert!(map.capacity() > 20);
    /// ```
    pub fn capacity(&self) -> usize {
        min(self.left_to_right.capacity(), self.right_to_left.capacity())
    }

    /// Reserves capacity for at least `additional` more elements to be inserted
    /// in the `BiMap`. The collection may reserve more space to avoid
    /// frequent reallocations.
    ///
    /// # Panics
    ///
    /// Panics if the new allocation size overflows [`usize`].
    ///
    /// [`usize`]: https://doc.rust-lang.org/std/primitive.usize.html
    ///
    /// # Examples
    ///
    /// ```
    /// use incremental_topo::bimap::BiMap;
    ///
    /// let mut map: BiMap<i32, i32> = BiMap::new();
    /// map.reserve(10);
    /// ```
    pub fn reserve(&mut self, additional: usize) {
        self.left_to_right.reserve(additional);
        self.right_to_left.reserve(additional);
    }

    /// Shrinks the capacity of the map as much as possible. It will drop
    /// down as much as possible while maintaining the internal rules
    /// and possibly leaving some space in accordance with the resize policy.
    ///
    /// # Examples
    ///
    /// ```
    /// use incremental_topo::bimap::BiMap;
    ///
    /// let mut map: BiMap<i32, i32> = BiMap::with_capacity(100);
    /// map.insert(1, 2);
    /// map.insert(3, 4);
    /// assert!(map.capacity() >= 100);
    /// map.shrink_to_fit();
    /// assert!(map.capacity() >= 2);
    /// ```
    pub fn shrink_to_fit(&mut self) {
        self.left_to_right.shrink_to_fit();
        self.right_to_left.shrink_to_fit();
    }

    /// Returns the number of elements in the map.
    ///
    /// # Examples
    ///
    /// ```
    /// use incremental_topo::bimap::BiMap;
    ///
    /// let mut map: BiMap<i32, i32> = BiMap::new();
    ///
    /// map.insert(1, 2);
    /// map.insert(3, 4);
    /// map.insert(5, 6);
    ///
    /// assert_eq!(map.len(), 3);
    /// ```
    pub fn len(&self) -> usize {
        min(self.left_to_right.len(), self.right_to_left.len())
    }

    /// Returns true if there are no pairs in the map.
    ///
    /// # Examples
    ///
    /// ```
    /// use incremental_topo::bimap::BiMap;
    ///
    /// let mut map: BiMap<i32, i32> = BiMap::new();
    ///
    /// assert!(map.is_empty());
    ///
    /// map.insert(1, 2);
    /// map.insert(3, 4);
    /// map.insert(5, 6);
    ///
    /// assert!(!map.is_empty());
    /// ```
    pub fn is_empty(&self) -> bool {
        self.left_to_right.is_empty() && self.right_to_left.is_empty()
    }

    /// Removes all pairs from the map, keeping the allocated memory for future
    /// use.
    ///
    /// # Examples
    ///
    /// ```
    /// use incremental_topo::bimap::BiMap;
    ///
    /// let mut map: BiMap<i32, i32> = BiMap::new();
    ///
    /// map.insert(1, 2);
    /// map.insert(3, 4);
    /// map.insert(5, 6);
    ///
    /// assert!(!map.is_empty());
    /// map.clear();
    /// assert!(map.is_empty());
    /// ```
    pub fn clear(&mut self) {
        self.left_to_right.clear();
        self.right_to_left.clear();
    }

    /// An iterator visiting all pairs in arbitrary order.
    /// The iterator element type is `(&'a L, &'a R)`.
    ///
    /// # Examples
    ///
    /// ```
    /// use incremental_topo::bimap::BiMap;
    ///
    /// let mut map = BiMap::new();
    ///
    /// map.insert(1, 2);
    /// map.insert(3, 4);
    /// map.insert(5, 6);
    ///
    /// for (left, right) in map.iter() {
    ///     println!("left: {} right: {}", left, right);
    /// }
    /// ```
    pub fn iter(&self) -> impl Iterator<Item = (&L, &R)> {
        self.right_to_left
            .values()
            .map(move |l| (l, self.get_by_left(l).unwrap()))
    }

    /// Consume the map, producing an iterator over the left and right values
    /// pairs.
    ///
    /// # Examples
    ///
    /// ```
    /// use incremental_topo::bimap::BiMap;
    ///
    /// let mut map = BiMap::new();
    ///
    /// map.insert(1, 2);
    /// map.insert(3, 4);
    /// map.insert(5, 6);
    ///
    /// for (left, right) in map.into_iter() {
    ///     println!("{} + {} = {}", left, right, left + right);
    /// }
    /// ```
    // TODO: remove and implement IntoIterator for T, &T
    #[allow(clippy::should_implement_trait)]
    pub fn into_iter(self) -> impl Iterator<Item = (L, R)> {
        let mut l2r = self.left_to_right;
        let r2l = self.right_to_left;
        let builder = self.hash_builder;

        r2l.into_iter().map(move |(_, l)| {
            let left_hash = hash_value(&l, builder.build_hasher());

            (l, l2r.remove(&left_hash).unwrap())
        })
    }

    /// Clears the map, returning all pairs as an iterator. Keeps the
    /// allocated memory for reuse.
    ///
    /// # Examples
    ///
    /// ```
    /// use incremental_topo::bimap::BiMap;
    ///
    /// let mut map = BiMap::new();
    ///
    /// map.insert(1, 2);
    /// map.insert(3, 4);
    /// map.insert(5, 6);
    ///
    /// for (left, right) in map.drain() {
    ///     println!("left: {} right: {}", left, right);
    /// }
    ///
    /// assert!(map.is_empty());
    /// ```
    pub fn drain(&mut self) -> impl Iterator<Item = (L, R)> + '_ {
        let r2l = &mut self.right_to_left;
        let l2r = &mut self.left_to_right;
        let builder = &self.hash_builder;

        r2l.drain().map(move |(_, l)| {
            let left_hash = hash_value(&l, builder.build_hasher());

            (l, l2r.remove(&left_hash).unwrap())
        })
    }

    /// An iterator visiting all left values in arbitrary order.
    /// The iterator element type is `&'a L`.
    ///
    /// # Examples
    ///
    /// ```
    /// use incremental_topo::bimap::BiMap;
    ///
    /// let mut map = BiMap::new();
    ///
    /// map.insert(1, 2);
    /// map.insert(3, 4);
    /// map.insert(5, 6);
    ///
    /// for left in map.left_values() {
    ///     println!("left: {}", left);
    /// }
    /// ```
    pub fn left_values(&self) -> impl Iterator<Item = &L> {
        self.right_to_left.values()
    }

    // FIXME(#1) mutable access not to be allowed
    #[allow(dead_code)]
    fn left_values_mut(&mut self) -> impl Iterator<Item = &mut L> {
        self.right_to_left.values_mut()
    }

    /// An iterator visiting all right values in arbitrary order.
    /// The iterator element type is `&'a R`.
    ///
    /// # Examples
    ///
    /// ```
    /// use incremental_topo::bimap::BiMap;
    ///
    /// let mut map = BiMap::new();
    ///
    /// map.insert(1, 2);
    /// map.insert(3, 4);
    /// map.insert(5, 6);
    ///
    /// for left in map.right_values() {
    ///     println!("left: {}", left);
    /// }
    /// ```
    pub fn right_values(&self) -> impl Iterator<Item = &R> {
        self.left_to_right.values()
    }

    // FIXME(#1) mutable access not to be allowed
    #[allow(dead_code)]
    fn right_values_mut(&mut self) -> impl Iterator<Item = &mut R> {
        self.left_to_right.values_mut()
    }

    /// Returns a reference to the value corresponding to this left value.
    ///
    /// The left value may be any borrowed form of the map's left type, but
    /// [`Hash`] and [`Eq`] on the borrowed form *must* match those for
    /// the left type.
    ///
    /// [`Eq`]: https://doc.rust-lang.org/std/cmp/trait.Eq.html
    /// [`Hash`]: https://doc.rust-lang.org/std/hash/trait.Hash.html
    ///
    /// # Examples
    ///
    /// ```
    /// use incremental_topo::bimap::BiMap;
    ///
    /// let mut map = BiMap::new();
    ///
    /// map.insert(1, "a");
    /// assert_eq!(map.get_by_left(&1), Some(&"a"));
    /// assert_eq!(map.get_by_left(&2), None);
    /// ```
    pub fn get_by_left<P>(&self, left: &P) -> Option<&R>
    where
        L: Borrow<P>,
        P: Hash + Eq + ?Sized,
    {
        let left_hash = hash_value(left, self.hash_builder.build_hasher());

        self.left_to_right.get(&left_hash)
    }

    // FIXME(#1) mutable access not to be allowed
    #[allow(dead_code)]
    fn get_by_left_mut<P>(&mut self, left: &P) -> Option<&mut R>
    where
        L: Borrow<P>,
        P: Hash + Eq + ?Sized,
    {
        let left_hash = hash_value(left, self.hash_builder.build_hasher());

        self.left_to_right.get_mut(&left_hash)
    }

    /// Returns a reference to the value corresponding to this right value.
    ///
    /// The right value may be any borrowed form of the map's right type, but
    /// [`Hash`] and [`Eq`] on the borrowed form *must* match those for
    /// the right type.
    ///
    /// [`Eq`]: https://doc.rust-lang.org/std/cmp/trait.Eq.html
    /// [`Hash`]: https://doc.rust-lang.org/std/hash/trait.Hash.html
    ///
    /// # Examples
    ///
    /// ```
    /// use incremental_topo::bimap::BiMap;
    ///
    /// let mut map = BiMap::new();
    ///
    /// map.insert(1, "a");
    /// assert_eq!(map.get_by_right(&"a"), Some(&1));
    /// assert_eq!(map.get_by_right(&"b"), None);
    /// ```
    pub fn get_by_right<Q>(&self, right: &Q) -> Option<&L>
    where
        R: Borrow<Q>,
        Q: Hash + Eq + ?Sized,
    {
        let right_hash = hash_value(right, self.hash_builder.build_hasher());

        self.right_to_left.get(&right_hash)
    }

    // FIXME(#1) mutable access not to be allowed
    #[allow(dead_code)]
    fn get_by_right_mut<Q>(&mut self, right: &Q) -> Option<&mut L>
    where
        R: Borrow<Q>,
        Q: Hash + Eq + ?Sized,
    {
        let right_hash = hash_value(right, self.hash_builder.build_hasher());

        self.right_to_left.get_mut(&right_hash)
    }

    /// Returns true if the map contains a pair for the specified left value.
    ///
    /// The left value may be any borrowed form of the map's left type, but
    /// [`Hash`] and [`Eq`] on the borrowed form *must* match those for
    /// the left type.
    ///
    /// [`Eq`]: https://doc.rust-lang.org/std/cmp/trait.Eq.html
    /// [`Hash`]: https://doc.rust-lang.org/std/hash/trait.Hash.html
    ///
    /// # Examples
    ///
    /// ```
    /// use incremental_topo::bimap::BiMap;
    ///
    /// let mut map = BiMap::new();
    ///
    /// map.insert(1, "a");
    /// assert_eq!(map.contains_left(&1), true);
    /// assert_eq!(map.contains_left(&2), false);
    /// ```
    pub fn contains_left<P>(&self, left: &P) -> bool
    where
        L: Borrow<P>,
        P: Hash + Eq + ?Sized,
    {
        let left_hash = hash_value(left, self.hash_builder.build_hasher());

        self.left_to_right.contains_key(&left_hash)
    }

    /// Returns true if the map contains a pair for the specified right value.
    ///
    /// The right value may be any borrowed form of the map's right type, but
    /// [`Hash`] and [`Eq`] on the borrowed form *must* match those for
    /// the right type.
    ///
    /// [`Eq`]: https://doc.rust-lang.org/std/cmp/trait.Eq.html
    /// [`Hash`]: https://doc.rust-lang.org/std/hash/trait.Hash.html
    ///
    /// # Examples
    ///
    /// ```
    /// use incremental_topo::bimap::BiMap;
    ///
    /// let mut map = BiMap::new();
    ///
    /// map.insert(1, "a");
    /// assert_eq!(map.contains_right(&"a"), true);
    /// assert_eq!(map.contains_right(&"b"), false);
    /// ```
    pub fn contains_right<Q>(&self, right: &Q) -> bool
    where
        R: Borrow<Q>,
        Q: Hash + Eq + ?Sized,
    {
        let right_hash = hash_value(right, self.hash_builder.build_hasher());

        self.right_to_left.contains_key(&right_hash)
    }

    /// Removes a pair from the map, returning the value at the left value if
    /// the left value was previously in the map.
    ///
    /// The left value may be any borrowed form of the map's left type, but
    /// [`Hash`] and [`Eq`] on the borrowed form *must* match those for
    /// the left type.
    ///
    /// [`Eq`]: https://doc.rust-lang.org/std/cmp/trait.Eq.html
    /// [`Hash`]: https://doc.rust-lang.org/std/hash/trait.Hash.html
    ///
    /// # Examples
    ///
    /// ```
    /// use incremental_topo::bimap::BiMap;
    ///
    /// let mut map = BiMap::new();
    ///
    /// map.insert(1, "a");
    /// assert_eq!(map.remove_by_left(&1), Some((1, "a")));
    /// assert_eq!(map.remove_by_left(&1), None);
    /// ```
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

    /// Removes a pair from the map, returning the value at the right value if
    /// the right value was previously in the map.
    ///
    /// The right value may be any borrowed form of the map's right type, but
    /// [`Hash`] and [`Eq`] on the borrowed form *must* match those for
    /// the right type.
    ///
    /// [`Eq`]: https://doc.rust-lang.org/std/cmp/trait.Eq.html
    /// [`Hash`]: https://doc.rust-lang.org/std/hash/trait.Hash.html
    ///
    /// # Examples
    ///
    /// ```
    /// use incremental_topo::bimap::BiMap;
    ///
    /// let mut map = BiMap::new();
    ///
    /// map.insert(1, "a");
    /// assert_eq!(map.remove_by_right(&"a"), Some((1, "a")));
    /// assert_eq!(map.remove_by_right(&"a"), None);
    /// ```
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

    // insert and insert_no_overwrite are directly cribbed from the crate
    // bimap, author Billy Rieger

    /// Inserts a left-right pair into the map.
    ///
    /// If the map did not have this key present, [`Overwritten::Neither`] is
    /// returned.
    ///
    /// If the map did have this key present, the value is updated, and the old
    /// value is returned. Depending on whether the right or the left value, or
    /// both were previously found in the map, different variants of
    /// Overwritten are returned. See the [module-level documentation] for more
    /// details.
    ///
    /// [`Overwritten::Neither`]: ./enum.Overwritten.html#variant.Neither
    /// [module-level documentation]: index.html#insertion-and-overwriting
    ///
    /// # Examples
    ///
    /// ```
    /// use incremental_topo::bimap::{BiMap, Overwritten};
    ///
    /// let mut map = BiMap::new();
    ///
    /// assert_eq!(map.insert(1, "a"), Overwritten::Neither);
    /// assert_eq!(map.insert(2, "b"), Overwritten::Neither);
    /// assert_eq!(map.insert(2, "c"), Overwritten::Left(2, "b"));
    /// assert_eq!(map.insert(3, "c"), Overwritten::Right(2, "c"));
    /// assert_eq!(map.insert(1, "c"), Overwritten::Both((1, "a"), (3, "c")));
    /// assert_eq!(map.insert(1, "c"), Overwritten::Pair(1, "c"));
    /// ```
    pub fn insert(&mut self, left: L, right: R) -> Overwritten<L, R> {
        let result = match (self.contains_left(&left), self.contains_right(&right)) {
            (false, false) => Overwritten::Neither,
            (true, false) => {
                let prev_pair = self.remove_by_left(&left).unwrap();
                Overwritten::Left(prev_pair.0, prev_pair.1)
            },
            (false, true) => {
                let prev_pair = self.remove_by_right(&right).unwrap();
                Overwritten::Right(prev_pair.0, prev_pair.1)
            },
            (true, true) => {
                if self.get_by_left(&left) == Some(&right) {
                    let prev_pair = self.remove_by_left(&left).unwrap();
                    Overwritten::Pair(prev_pair.0, prev_pair.1)
                } else {
                    let left_overwritten = self.remove_by_left(&left).unwrap();
                    let right_overwritten = self.remove_by_right(&right).unwrap();
                    Overwritten::Both(left_overwritten, right_overwritten)
                }
            },
        };

        let left_hash = hash_value(&left, self.hash_builder.build_hasher());
        let right_hash = hash_value(&right, self.hash_builder.build_hasher());

        self.left_to_right.insert(left_hash, right);
        self.right_to_left.insert(right_hash, left);

        result
    }

    /// Inserts the given left-right pair into the `BiMap` without overwriting
    /// any existing values.
    ///
    /// Returns a boolean representing if the pair was successfully inserted
    /// into the `BiMap`. If either value exists in the map, `false` is
    /// returned and the map is unchanged. Otherwise, the pair is inserted
    /// and `true` is returned.
    ///
    /// # Examples
    ///
    /// ```
    /// use incremental_topo::bimap::BiMap;
    ///
    /// let mut bimap = BiMap::new();
    /// assert!(bimap.insert_no_overwrite('a', 1));
    /// assert!(bimap.insert_no_overwrite('b', 2));
    /// assert!(!bimap.insert_no_overwrite('a', 3));
    /// assert!(!bimap.insert_no_overwrite('c', 2));
    /// ```
    pub fn insert_no_overwrite(&mut self, left: L, right: R) -> bool {
        if self.contains_left(&left) || self.contains_right(&right) {
            false
        } else {
            self.insert(left, right);
            true
        }
    }

    /// Retains only the elements specified by the predicate.
    ///
    /// In other words, remove all pairs `(l, r)` such that `f(&l, &r)` returns
    /// `false`.
    ///
    /// # Examples
    ///
    /// ```
    /// use incremental_topo::bimap::BiMap;
    ///
    /// let mut bimap = BiMap::new();
    /// bimap.insert('a', 1);
    /// bimap.insert('b', 2);
    /// bimap.insert('c', 3);
    /// bimap.retain(|&l, &r| r >= 2);
    /// assert_eq!(bimap.len(), 2);
    /// assert_eq!(bimap.get_by_left(&'b'), Some(&2));
    /// assert_eq!(bimap.get_by_left(&'c'), Some(&3));
    /// assert_eq!(bimap.get_by_left(&'a'), None);
    /// ```
    pub fn retain<F>(&mut self, mut f: F)
    where
        F: FnMut(&L, &R) -> bool,
        S::Hasher: Clone,
    {
        let hasher = self.hash_builder.build_hasher();
        let to_remove: Vec<_> = self
            .iter()
            .filter_map(|(left, right)| {
                let left_hash = hash_value(left, hasher.clone());
                let right_hash = hash_value(right, hasher.clone());

                if !f(left, right) {
                    Some((left_hash, right_hash))
                } else {
                    None
                }
            })
            .collect();

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
