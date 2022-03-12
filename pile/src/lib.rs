//! # Pile
//!
//! A pile is a **fast but limited collection** for storing values of a single type.
//!
//!
//! ## What is a pile?
//!
//! A pile is an ordered collection, similar to `Vec`, onto which values can be
//! pushed. In contrast to `Vec`, a pile allows pushing values through a shared
//! reference. Pushing values is an *O(1)* operation and will never relocate previously
//! pushed values, i.e., previously pushed values remain at a stable address in
//! memory. This enables safe pushing through a shared reference.
//!
//! When pushing a value, a pile returns a reference to the value in addition to a
//! *key*. The key does not borrow from the pile and can be used to retrieve the
//! value in *O(1)*. In addition, given an exclusive reference to the pile, the key
//! can be used to obtain an exclusive reference to the value in *O(1)*. Every key
//! corresponds to an insertion *index*. Values can also be accessed by their insertion
//! index in *O(log n)*. Iterating over a pile or converting it to a vector will also
//! preserve the insertion order.
//!
//! Here is a list of similar data structures and their differences:
//!
//! - A [`TypedArena`](https://docs.rs/typed-arena/) does not provide a key and
//!   returns an exclusive reference to a value inserted through a shared reference. A
//!   key is useful because it exists independently of the pile (it does not borrow
//!   from the pile). It can thus be passed around more freely than a reference and
//!   can also be meaningfully serialized (for details see below).
//! - A [`Slab`](https://docs.rs/slab) and a [`SlotMap`](https://docs.rs/slotmap) cannot
//!   be mutated trough a shared reference. If mutation through a shared reference is
//!   not required, you may want to use those as they are generally much more flexible.
//!
//!
//! ## Serialization
//!
//! Using the `serde` feature, piles and keys can be serialized.
//!
//! Piles storing values of type `T` are serialized as sequences of type `T`, just as a
//! `Vec` is, and keys are serialized as the corresponding insertion index. This enables
//! external tools to simply treat keys as indices into the the serialized sequence.
//!
//! When using a previously serialized and then deserialized key for accessing a value
//! without also serializing and then deserializing the corresponding pile is an
//! *O(log n)* operation (just as accessing by index).
//!
//!
//! ## Example
//!
//! ```
//! # use pile::*;
//! let vegetables = Pile::<&'static str>::new();
//!
//! let (cucumber_key, cucumber) = vegetables.push("Cucumber");
//! let (paprika_key, paprika) = vegetables.push("Paprika");
//!
//! assert_eq!(vegetables[cucumber_key], "Cucumber");
//!
//! assert_eq!(Vec::from(vegetables), vec!["Cucumber", "Paprika"]);
//! ```

use std::{cell::RefCell, marker::PhantomData};

#[doc(hidden)]
#[cfg(feature = "serde")]
pub use serde;

/// Key used to access values stored in some [`Pile`].
///
/// A [`Key`] must support infallible conversion from and to [`DefaultKey`].
pub trait Key: Clone + Copy + From<DefaultKey> + Into<DefaultKey> {
    /// The *index* associated with the key.
    fn index(self) -> usize;
}

/// Default key type to access values stored in some [`Pile`].
#[derive(Clone, Copy, Debug)]
pub struct DefaultKey {
    chunk_idx: u32,
    value_idx: u32,
}

impl DefaultKey {
    fn new(chunk_idx: usize, value_idx: usize) -> Self {
        Self {
            chunk_idx: u32::try_from(chunk_idx)
                .expect("Overflow in chunk number. Too many chunks."),
            value_idx: u32::try_from(value_idx)
                .expect("Overflow in index number. Too many values."),
        }
    }

    fn chunk_idx(self) -> usize {
        self.chunk_idx as usize
    }

    fn value_idx(self) -> usize {
        self.value_idx as usize
    }
}

#[cfg(feature = "serde")]
impl serde::Serialize for DefaultKey {
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: serde::Serializer,
    {
        self.index.serialize(serializer)
    }
}

#[cfg(feature = "serde")]
impl<'de> serde::Deserialize<'de> for DefaultKey {
    fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
    where
        D: serde::Deserializer<'de>,
    {
        let index = u32::deserialize(deserializer)?;
        Ok(Self { chunk: 0, index })
    }
}

impl Key for DefaultKey {
    fn index(self) -> usize {
        self.value_idx()
    }
}

impl std::fmt::Display for DefaultKey {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        self.value_idx.fmt(f)
    }
}

impl std::hash::Hash for DefaultKey {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        self.value_idx.hash(state);
    }
}

impl PartialEq for DefaultKey {
    fn eq(&self, other: &Self) -> bool {
        self.value_idx == other.value_idx
    }
}

impl Eq for DefaultKey {}

impl PartialOrd for DefaultKey {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        self.value_idx.partial_cmp(&other.value_idx)
    }
}

impl Ord for DefaultKey {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        self.value_idx.cmp(&other.value_idx)
    }
}

/// Defines a new type of [`Key`].
///
/// 📌 **Using different key types for different piles can prevent using the wrong key to
/// access a value in the wrong pile.**
///
///
/// # Examples
///
/// ```
/// # use pile::*;
/// new_key_type! {
///     /// This is a special key type identifying fruits stored in a pile.
///     pub struct FruitKey;
/// }
///
/// let pile = Pile::<&'static str, FruitKey>::new();
///
/// let (apple_key, _) = pile.push("Apple");
/// let (banana_key, _) = pile.push("Banana");
///
/// assert_eq!(pile[apple_key], "Apple");
/// ```
#[macro_export]
macro_rules! new_key_type {
    ($(#[$meta:meta])* $vis:vis struct $name:ident;) => {
        $(#[$meta])*
        #[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash, Debug)]
        #[repr(transparent)]
        $vis struct $name($crate::DefaultKey);

        const _: () = {
            #[automatically_derived]
            impl ::std::convert::From<$crate::DefaultKey> for $name {
                fn from(key: $crate::DefaultKey) -> Self {
                    Self(key)
                }
            }

            #[automatically_derived]
            impl ::std::convert::From<$name> for $crate::DefaultKey {
                fn from(key: $name) -> Self {
                    key.0
                }
            }

            #[automatically_derived]
            impl $crate::Key for $name {
                fn index(self) -> usize {
                    self.0.index()
                }
            }

            $crate::private_key_type_impl_serde!($name);
        };
    };
}

#[macro_export]
#[doc(hidden)]
#[cfg(not(feature = "serde"))]
macro_rules! private_key_type_impl_serde {
    ($name:ident) => {};
}

#[macro_export]
#[doc(hidden)]
#[cfg(feature = "serde")]
macro_rules! private_key_type_impl_serde {
    ($name:ident) => {
        impl $crate::serde::Serialize for $name {
            fn serialize<S>(&self, serializer: S) -> ::std::result::Result<S::Ok, S::Error>
            where
                S: $crate::serde::Serializer,
            {
                use $crate::serde::Serialize;
                self.0.serialize(serializer)
            }
        }

        impl<'de> $crate::serde::Deserialize<'de> for $name {
            fn deserialize<D>(deserializer: D) -> ::std::result::Result<Self, D::Error>
            where
                D: $crate::serde::Deserializer<'de>,
            {
                use $crate::serde::Deserialize;
                $crate::DefaultKey::deserialize(deserializer).map($name)
            }
        }
    };
}

/// The default capacity of a [`Pile`].
///
/// If you expect less values, a [`Pile`] is probably the wrong data structure. 😉
pub const DEFAULT_CAPACITY: usize = 32;

// The chunks of a pile grow until they reach the `HUGE_PAGE_SIZE`.
//
// This is based on how the `TypedArena` in the Rust compiler works.
const NORMAL_PAGE_SIZE: usize = 4096;
const HUGE_PAGE_SIZE: usize = 2 * 1024 * 1024;

#[derive(Clone, Debug)]
struct Chunk<T> {
    start: usize,
    storage: Vec<T>,
}

impl<T> Chunk<T> {
    fn new(start: usize, capacity: usize) -> Self {
        Self {
            start,
            storage: Vec::with_capacity(capacity),
        }
    }
}

#[derive(Clone, Debug)]
struct PileInner<T> {
    chunks: Vec<Chunk<T>>,
}

/// A [`Pile`] for storing values of a single type.
#[derive(Clone, Debug)]
pub struct Pile<T, K: Key = DefaultKey> {
    inner: RefCell<PileInner<T>>,
    _phantom_key: PhantomData<K>,
}

impl<T, K: Key> Pile<T, K> {
    /// Constructs an empty pile with a capacity of [`DEFAULT_CAPACITY`].
    pub fn new() -> Self {
        Self::with_capacity(DEFAULT_CAPACITY)
    }

    /// Constructs an empty pile able to store at least *capacity* values before
    /// needing to allocate.
    pub fn with_capacity(capacity: usize) -> Self {
        let page_capacity = NORMAL_PAGE_SIZE / std::mem::size_of::<T>();
        let capacity = std::cmp::max(page_capacity, capacity);
        Self {
            inner: RefCell::new(PileInner {
                chunks: vec![Chunk::new(0, capacity)],
            }),
            _phantom_key: PhantomData,
        }
    }

    /// Pushes a *value* onto the pile potentially allocating more memory.
    pub fn push(&self, value: T) -> (K, &T) {
        self.try_push(value).unwrap_or_else(|value| {
            self.grow(1);
            match self.try_push(value) {
                Ok(result) => result,
                Err(_) => unreachable!("There should be space because we just grew the pile."),
            }
        })
    }

    /// Tries to push a *value* onto the pile *without* allocating more memory.
    ///
    ///
    /// ## Error
    ///
    /// Fails in case no space is available in the pile.
    pub fn try_push(&self, value: T) -> Result<(K, &T), T> {
        let mut inner = self.inner.borrow_mut();
        let chunk_idx = inner.chunks.len() - 1;
        let active = inner
            .chunks
            .last_mut()
            .expect("There should be at least one chunk in the pile.");
        let offset = active.storage.len();
        if offset < active.storage.capacity() {
            active.storage.push(value);
            debug_assert!(offset < active.storage.len());
            // SAFETY: This is safe because we just ensured that there is a value stored
            // at the given offset. It is also safe to create a reference into the storage
            // because `Vec` dereferences to stable addresses and no exclusive reference
            // to the same value can be obtained through a shared reference to the pile.
            let reference = unsafe { &*active.storage.as_ptr().add(offset) };
            let value_idx = active.start + offset;
            Ok((K::from(DefaultKey::new(chunk_idx, value_idx)), reference))
        } else {
            Err(value)
        }
    }

    /// The number of values stored in the pile.
    pub fn len(&self) -> usize {
        let inner = self.inner.borrow();
        let active = inner
            .chunks
            .last()
            .expect("There should be at least one chunk in the pile.");
        (active.start as usize) + active.storage.len()
    }

    /// Returns a shared reference to the value stored for the given *key*.
    ///
    /// The complexity is *O(1)* if the *key* has been returned by this pile. It
    /// is *O(log n)* if the *key* cannot be found or it has been serialized and
    /// deserialized without also serializing and deserializing the pile.
    pub fn get(&self, key: K) -> Option<&T> {
        let key: DefaultKey = key.into();
        self.raw_get(key.chunk_idx(), key.value_idx())
            .or_else(|| self.get_slow(key))
    }

    /// Slow path of `get` in case we need to lookup the key by index.
    #[cold]
    fn get_slow(&self, key: DefaultKey) -> Option<&T> {
        let key: DefaultKey = self.key_from_index(key.index())?.into();
        self.raw_get(key.chunk_idx(), key.value_idx())
    }

    /// Returns an exclusive reference to the value stored for the given *key*.
    ///
    /// For details see [`get`][Pile::get].
    pub fn get_mut(&mut self, key: K) -> Option<&mut T> {
        let key: DefaultKey = key.into();
        // 💩 This would be much cleaner if `raw_get_mut` and `get_mut_slow` would take
        // an exclusive reference to `self`. However, this does not work because the
        // borrow checker does not understand that in the `None` branch, nothing is
        // mutably borrowed from `self` and, hence, does not let use use our exclusive
        // reference for the call to `get_mut_slow` again.
        //
        // SAFETY: This is safe because there cannot be any other references into the
        // pile as we have an exclusive reference to the pile. Hence, there can be no
        // references to the value for `key`, in particular.
        unsafe {
            self.raw_get_mut(key.chunk_idx(), key.value_idx())
                .or_else(|| self.get_mut_slow(key))
        }
    }

    /// Slow path of `get_mut` in case we need to lookup the key by index.
    ///
    /// 💩 See `get_mut` for why this method does not take an exclusive `self` reference.
    ///
    /// # Safety
    ///
    /// The caller must ensure that there are no other references to the value stored
    /// for the provided *key*. The method `get_mut` ensures this by taking an exclusive
    /// reference to the pile.
    #[cold]
    unsafe fn get_mut_slow(&self, key: DefaultKey) -> Option<&mut T> {
        let key: DefaultKey = self.key_from_index(key.index())?.into();
        self.raw_get_mut(key.chunk_idx(), key.value_idx())
    }

    /// Returns a key corresponding to the provided *index* if a value is stored at the
    /// given *index*.
    ///
    /// The complexity is *O(log n)*.
    pub fn key_from_index(&self, index: usize) -> Option<K> {
        let inner = self.inner.borrow();
        let chunk_idx = inner
            .chunks
            .binary_search_by_key(&index, |chunk| chunk.start)
            .unwrap_or_else(|idx| idx - 1);
        let chunk = &inner.chunks[chunk_idx];
        if index - chunk.start < chunk.storage.len() {
            Some(K::from(DefaultKey::new(chunk_idx, index)))
        } else {
            None
        }
    }

    /// Turns the pile into a vector.
    ///
    /// The *index* of [`Key`] can be used as an index into the returned vector.
    pub fn into_vec(self) -> Vec<T> {
        let mut result = Vec::with_capacity(self.len());
        let inner = self.inner.into_inner();
        for mut chunk in inner.chunks {
            result.append(&mut chunk.storage);
        }
        result
    }

    /// Returns an [`Iterator`] over the stored key-value pairs.
    pub fn iter(&self) -> Iter<T, K> {
        Iter {
            pile: self,
            chunk_idx: 0,
            value_idx: 0,
        }
    }

    /// Returns an [`Iterator`] moving key-value pairs out of the pile.
    pub fn into_iter(self) -> IntoIter<T, K> {
        IntoIter {
            chunks: self.inner.into_inner().chunks.into_iter(),
            active: None,
            chunk_idx: 0,
            value_idx: 0,
            _phantom_key: PhantomData,
        }
    }

    /// Grows the pile such that there is space for at least *additional* values.
    #[cold]
    fn grow(&self, additional: usize) {
        let mut inner = self.inner.borrow_mut();
        let active = inner
            .chunks
            .last()
            .expect("There should be at least one chunk in the Pile.");
        debug_assert!(
            active.storage.len() == active.storage.capacity(),
            "The active chunk is not full yet?"
        );
        let start = active.start + active.storage.len();
        let capacity = std::cmp::max(
            additional,
            std::cmp::min(
                active.storage.capacity() * 2,
                HUGE_PAGE_SIZE / std::mem::size_of::<T>(),
            ),
        );
        inner.chunks.push(Chunk::new(start, capacity));
    }

    /// Returns a reference to the value stored in the given *chunk* at the given *index*.
    fn raw_get(&self, chunk: usize, index: usize) -> Option<&T> {
        self.inner.borrow().chunks.get(chunk).and_then(|chunk| {
            let offset = index - (chunk.start as usize);
            if offset < chunk.storage.len() {
                // SAFETY: See `insert`.
                Some(unsafe { &*chunk.storage.as_ptr().add(offset) })
            } else {
                None
            }
        })
    }

    /// Returns an exclusive reference to the value stored in the given *chunk* at the
    /// given *index*.
    ///
    /// 💩 See `get_mut` for why this method does not take an exclusive `self` reference.
    ///
    /// # Safety
    ///
    /// The caller must ensure that there are no other references to the value stored
    /// in the given *chunk* with the given *index*. The method `get_mut` ensures this
    /// by taking an exclusive reference to the pile.
    unsafe fn raw_get_mut(&self, chunk: usize, index: usize) -> Option<&mut T> {
        self.inner
            .borrow_mut()
            .chunks
            .get_mut(chunk)
            .and_then(|chunk| {
                let offset = index - (chunk.start as usize);
                if offset < chunk.storage.len() {
                    // SAFETY: The caller must guarantee that no other references to
                    // this value and `Vec` dereferences to a stable address.
                    Some(&mut *(chunk.storage.as_mut_ptr().add(offset)))
                } else {
                    None
                }
            })
    }
}

impl<T, K: Key> From<Pile<T, K>> for Vec<T> {
    fn from(pile: Pile<T, K>) -> Self {
        pile.into_vec()
    }
}

impl<T, K: Key> From<Vec<T>> for Pile<T, K> {
    fn from(chunk: Vec<T>) -> Self {
        Self {
            inner: RefCell::new(PileInner {
                chunks: vec![Chunk {
                    start: 0,
                    storage: chunk,
                }],
            }),
            _phantom_key: PhantomData,
        }
    }
}

impl<T, K: Key> Default for Pile<T, K> {
    fn default() -> Self {
        Self::new()
    }
}

impl<'p, T, K: Key> IntoIterator for &'p Pile<T, K> {
    type Item = (K, &'p T);

    type IntoIter = Iter<'p, T, K>;

    fn into_iter(self) -> Self::IntoIter {
        self.iter()
    }
}

impl<T, K: Key> IntoIterator for Pile<T, K> {
    type Item = (K, T);

    type IntoIter = IntoIter<T, K>;

    fn into_iter(self) -> Self::IntoIter {
        self.into_iter()
    }
}

impl<T, K: Key> FromIterator<T> for Pile<T, K> {
    fn from_iter<I: IntoIterator<Item = T>>(iter: I) -> Self {
        let iter = iter.into_iter();
        let (lower_bound, upper_bound) = iter.size_hint();
        let capacity = upper_bound.unwrap_or(lower_bound);
        let pile = Pile::with_capacity(capacity);
        for value in iter {
            pile.push(value);
        }
        pile
    }
}

impl<T, K: Key> std::ops::Index<K> for Pile<T, K> {
    type Output = T;

    fn index(&self, key: K) -> &Self::Output {
        self.get(key)
            .expect("No value has been stored for the given key.")
    }
}

impl<T, K: Key> std::ops::IndexMut<K> for Pile<T, K> {
    fn index_mut(&mut self, key: K) -> &mut Self::Output {
        self.get_mut(key)
            .expect("No value has been stored for the given key.")
    }
}

#[cfg(feature = "serde")]
impl<T: serde::Serialize, K: Key> serde::Serialize for Pile<T, K> {
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: serde::Serializer,
    {
        use serde::ser::SerializeSeq;
        let mut seq = serializer.serialize_seq(Some(self.len()))?;
        for value in self.iter() {
            seq.serialize_element(value)?;
        }
        seq.end()
    }
}

#[cfg(feature = "serde")]
impl<'de, T: serde::Deserialize<'de>, K: Key> serde::Deserialize<'de> for Pile<T, K> {
    fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
    where
        D: serde::Deserializer<'de>,
    {
        Ok(Vec::deserialize(deserializer)?.into())
    }
}

/// An [`Iterator`] that moves key-value pairs out of a [`Pile`].
pub struct IntoIter<T, K: Key> {
    chunks: std::vec::IntoIter<Chunk<T>>,
    active: Option<std::vec::IntoIter<T>>,
    chunk_idx: usize,
    value_idx: usize,
    _phantom_key: PhantomData<K>,
}

impl<T, K: Key> Iterator for IntoIter<T, K> {
    type Item = (K, T);

    fn next(&mut self) -> Option<Self::Item> {
        loop {
            match &mut self.active {
                Some(chunk) => match chunk.next() {
                    Some(value) => {
                        let result = Some((
                            K::from(DefaultKey::new(self.chunk_idx, self.value_idx)),
                            value,
                        ));
                        self.value_idx += 1;
                        break result;
                    }
                    None => {
                        self.active = None;
                        self.chunk_idx += 1;
                    }
                },
                None => match self.chunks.next() {
                    Some(chunk) => {
                        self.active = Some(chunk.storage.into_iter());
                    }
                    None => break None,
                },
            }
        }
    }
}

/// An [`Iterator`] over key-value pairs in a [`Pile`].
pub struct Iter<'p, T, K: Key> {
    pile: &'p Pile<T, K>,
    chunk_idx: usize,
    value_idx: usize,
}

impl<'p, T, K: Key> Iterator for Iter<'p, T, K> {
    type Item = (K, &'p T);

    fn next(&mut self) -> Option<Self::Item> {
        loop {
            let inner = self.pile.inner.borrow();
            if self.chunk_idx >= inner.chunks.len() {
                break None;
            }
            match self.pile.raw_get(self.chunk_idx, self.value_idx) {
                Some(value) => {
                    let result = Some((
                        K::from(DefaultKey::new(self.chunk_idx, self.value_idx)),
                        value,
                    ));
                    self.value_idx += 1;
                    break result;
                }
                None => {
                    self.chunk_idx += 1;
                }
            }
        }
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        // No upper bound because values can be inserted while iterating.
        (self.pile.len(), None)
    }

    fn count(self) -> usize {
        self.pile.len() - self.value_idx
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    pub fn test_many() {
        let pile = Pile::<usize>::new();
        let values = (0..10_000)
            .map(|value| pile.push(value))
            .collect::<Vec<_>>();
        for (expected, (key, _)) in values.iter().enumerate() {
            assert_eq!(pile[*key], expected)
        }
        for (expected, (key, value_ref)) in pile.iter().enumerate() {
            assert_eq!(key.index(), expected);
            assert_eq!(*value_ref, expected);
        }
    }
}
