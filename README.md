# Pile

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