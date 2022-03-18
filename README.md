# Stacko    ![pipeline]

[pipeline]: https://img.shields.io/github/workflow/status/koehlma/stacko-rs/Pipeline/main?label=tests


`Stacko` is a **fast but limited ordered collection** for storing values of a single
type.


## What is a `Stacko`?

`Stacko` is a fast and ordered collection, similar to `Vec`, onto which values
can be pushed. In contrast to a `Vec`, a `Stacko` allows pushing values
through a shared reference. Pushing values is an *O(1)* operation and will never
relocate previously pushed values, i.e., previous values remain at a stable address
in memory. This enables safe pushing through a shared reference.

When pushing a value, `Stacko` returns a reference to the value in addition to a
*key*. The key does not borrow from the `Stacko` and can be used to retrieve the
value in *O(1)*. In addition, given an exclusive reference to the `Stacko`, the key
can be used to obtain an exclusive reference to the value in *O(1)*. Every key
corresponds to an insertion *index*. Values can also be accessed by their insertion
index in *O(log n)*. Iterating over a `Stacko` or converting it to a `Vec` will
also preserve the insertion order.

Values cannot be removed from a `Stacko`.

Here is a list of similar data structures and their differences:

- A [`TypedArena`](https://docs.rs/typed-arena/) does not provide a key and
  returns an exclusive reference to a value inserted through a shared reference. A
  key is useful because it exists independently of the `Stacko` (it does not
  borrow). It can thus be passed around more freely than a reference and
  can also be meaningfully serialized (for details see below).
- A [`Slab`](https://docs.rs/slab) and a [`SlotMap`](https://docs.rs/slotmap) cannot
  be mutated trough a shared reference. If mutation through a shared reference is
  not required, you may want to consider those as they are generally much more
  flexible.


## Serialization

Using the `serde` feature flag, a `Stacko` and its keys can be serialized with
[Serde][serde].

A `Stacko` storing values of type `T` is serialized as a sequence of type `T`,
just as a `Vec` of type `T` is, and keys are serialized as the corresponding
insertion index into this sequence. This enables external tools to simply treat keys
as indices into the serialized sequence. Using a previously serialized and then
deserialized key for accessing a value without also serializing and then deserializing
the corresponding `Stacko` is an *O(log n)* operation (just as accessing by index).

This exact serialization behavior is considered part of the stability guarantees.


## Example

```rust
let vegetables = Stacko::<&'static str>::new();

let (cucumber_key, cucumber) = vegetables.push("Cucumber");
let (paprika_key, paprika) = vegetables.push("Paprika");

assert_eq!(vegetables[cucumber_key], "Cucumber");

assert_eq!(Vec::from(vegetables), vec!["Cucumber", "Paprika"]);
```