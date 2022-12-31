Direct ports of the standard library's [`BTreeMap`][std::collections::BTreeMap] and
[`BTreeSet`][std::collections::BTreeSet] collections, but which sort according to a specified
[`Comparator`] rather than relying upon the [`Ord`] trait.

This is primarily useful when the [`Comparator`] is not defined until runtime, and therefore
cannot be provided as an [`Ord`] implementation for any type.

# Lookup keys
In the standard library's collections, certain lookups can be performed using a key of type
`&Q` where the collection's storage key type `K` implements [`Borrow<Q>`]; for example, one
can use `&str` keys to perform lookups into collections that store `String` keys.  This is
possible because the [`Borrow`] trait stipulates that borrowed values must preserve [`Ord`]
order.

However, copse's collections do not use the [`Ord`] trait; instead, lookups can only ever
be performed using the [`Comparator<T>`] supplied upon collection creation.  This comparator
can only compare values of type `&T` for which it was defined, and hence such type must be
reachable from any key type `&Q` used to perform lookups in the collection.  copse ensures
this via its [`Sortable`] trait, which will typically be implemented by the stored key type
`K`; its [`State`][Sortable::State] associated type then specifies the `T` in which
comparisons will be performed, and values of type `&Q` can be used as lookup keys provided
that `Q: Borrow<T>`.

For example, a collection using a `Comparator<str>` comparator can store keys of type
`String` because `String` implements `Sortable<State = str>`; moreover, lookups can be
performed using keys of type `&str` because `str` implements `Borrow<str>` (due to the
reflexive blanket implementation).

Implementations of [`Sortable`] are provided for primitive and some common standard library
types, but storing keys of other foreign types may require newtyping.

# Function item types
In addition to the type parameters familiar from the standard library collections, copse's
collections are additionally parameterised by the type of the [`Comparator`].  If the
comparator type is not explicitly named, it defaults to the type of the [`Ord::cmp`]
function for `K::State`.  As noted in the documentation of the [`CmpFn`] type alias, this
is only a zero-sized function item type if the unstable `type_alias_impl_trait` feature is
enabled; otherwise it is a function pointer type, with ensuing size and indirect call
implications.  Collections built using the zero-sized function item type can still be
used in stable code, however; just not using the default type parameter.  For example:

```rust
let mut ord_map = BTreeMap::new(Ord::cmp);
```

However, naming this type carries the usual problems associated with anonymous types like
closures; in certain situations you may be able to use `impl Comparator` for the type
parameter, but in other situations (in stable code) the function pointer may be
unavoidable.

# Crate feature flags
This crate defines a number of feature flags, none of which are enabled by default:

* the `std` feature provides [`Sortable`] implementations for some libstd types
  that are not available in libcore + liballoc, namely [`OsString`] and [`PathBuf`];

* the `unstable` feature enables all other crate features, each of which enables the
  like-named unstable compiler feature that is used by the standard library's collection
  implementations (and which therefore require a nightly compiler)—most such behaviour
  is polyfilled when the features are disabled, so they should rarely be required, but
  they are nevertheless included to ease tracking of the stdlib implementations.
  
  The most visible differences to library users will be:
    * `allocator_api` enables the `new_in` methods for use of custom allocators;
    * `specialization` adds the collection type name to some panic messages;
    * `type_alias_impl_trait`, as mentioned above, ensures that the *default*
       [`Comparator`] type parameter for the collections is the zero-sized function
       item type of the `K::State::cmp` function.

[std::collections::BTreeMap]: https://doc.rust-lang.org/std/collections/struct.BTreeMap.html
[std::collections::BTreeSet]: https://doc.rust-lang.org/std/collections/struct.BTreeSet.html
[`Ord`]: https://doc.rust-lang.org/std/cmp/trait.Ord.html
[`Borrow`]: https://doc.rust-lang.org/std/borrow/trait.Borrow.html
[`Borrow<Q>`]: https://doc.rust-lang.org/std/borrow/trait.Borrow.html
[`Ord::cmp`]: https://doc.rust-lang.org/std/cmp/trait.Ord.html#tymethod.cmp
[`OsString`]: https://doc.rust-lang.org/std/ffi/os_str/struct.OsString.html
[`PathBuf`]: https://doc.rust-lang.org/std/path/struct.PathBuf.html

[`CmpFn`]: https://docs.rs/copse/latest/copse/type.CmpFn.html
[`Comparator`]: https://docs.rs/copse/latest/copse/trait.Comparator.html
[`Comparator<T>`]: https://docs.rs/copse/latest/copse/trait.Comparator.html
[`Sortable`]: https://docs.rs/copse/latest/copse/trait.Sortable.html
[Sortable::State]: https://docs.rs/copse/latest/copse/trait.Sortable.html#associatedtype.State