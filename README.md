# Pile    ![pipeline]

[pipeline]: https://img.shields.io/github/workflow/status/koehlma/pile-rs/Pipeline/main?label=tests

A pile is a **fast but limited collection** for storing values of a single type.


## What is a pile?

A pile is an ordered collection, similar to `Vec`, onto which values can be
pushed. In contrast to `Vec`, a pile allows pushing values through a shared
reference. Pushing values is an *O(1)* operation and will never relocate previously
pushed values, i.e., previously pushed values remain at a stable address in
memory. This enables safe pushing through a shared reference.

When pushing a value, a pile returns a reference to the value in addition to a
*key*. The key does not borrow from the pile and can be used to retrieve the
value in *O(1)*. In addition, given an exclusive reference to the pile, the key
can be used to obtain an exclusive reference to the value in *O(1)*. Every key
corresponds to an insertion *index*. Values can also be accessed by their insertion
index in *O(log n)*. Iterating over a pile or converting it to a vector will also
preserve the insertion order.

Here is a list of similar data structures and their differences:

- A [`TypedArena`](https://docs.rs/typed-arena/) does not provide a key and
  returns an exclusive reference to a value inserted through a shared reference. A
  key is useful because it exists independently of the pile (it does not borrow
  from the pile). It can thus be passed around more freely than a reference and
  can also be meaningfully serialized (for details see below).
- A [`Slab`](https://docs.rs/slab) and a [`SlotMap`](https://docs.rs/slotmap) cannot
  be mutated trough a shared reference. If mutation through a shared reference is
  not required, you may want to use those as they are generally much more flexible.


## Serialization

Using the `serde` feature, piles and keys can be serialized.

Piles storing values of type `T` are serialized as sequences of type `T`, just as a
`Vec` is, and keys are serialized as the corresponding insertion index. This enables
external tools to simply treat keys as indices into the the serialized sequence.

Using a previously serialized and then deserialized key for accessing a value
without also serializing and then deserializing the corresponding pile is an
*O(log n)* operation (just as accessing by index).


## Example

```rust
let vegetables = Pile::<&'static str>::new();

let (cucumber_key, cucumber) = vegetables.push("Cucumber");
let (paprika_key, paprika) = vegetables.push("Paprika");

assert_eq!(vegetables[cucumber_key], "Cucumber");

assert_eq!(Vec::from(vegetables), vec!["Cucumber", "Paprika"]);
```