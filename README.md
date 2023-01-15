Direct ports of the standard library's [`BTreeMap`][std::collections::BTreeMap],
[`BTreeSet`][std::collections::BTreeSet] and [`BinaryHeap`][std::collections::BinaryHeap]
collections, but which sort according to a specified [`Comparator`] rather than relying upon
the [`Ord`] trait.

This is primarily useful when the [`Comparator`] is not defined until runtime, and therefore
cannot be provided as an [`Ord`] implementation for any type.

# Lookup keys
In the standard library's collections, certain lookups can be performed using a key of type
`&Q` where the collection's storage key type `K` implements [`Borrow<Q>`]; for example, one
can use `&str` keys to perform lookups into collections that store `String` keys.  This is
possible because the [`Borrow`] trait stipulates that borrowed values must preserve [`Ord`]
order.

However, copse's collections do not use the [`Ord`] trait; instead, lookups can only ever
be performed using the [`Comparator`] supplied upon collection creation.  This comparator
can only compare values of its [`Key`][Comparator::Key] associated type, and hence keys used
for lookups must implement [`LookupKey<C>`] in order that the conversion can be performed.

# Example
```rust
// define a comparator
struct NthByteComparator {
    n: usize, // runtime state
}

impl Comparator for NthByteComparator {
    type Key = str;
    fn cmp(&self, this: &str, that: &str) -> Ordering {
        match (this.as_bytes().get(self.n), that.as_bytes().get(self.n)) {
            (Some(lhs), Some(rhs)) => lhs.cmp(rhs),
            (Some(_), None) => Ordering::Greater,
            (None, Some(_)) => Ordering::Less,
            (None, None) => Ordering::Equal,
        }
    }
}

// define lookup key types for collections sorted by our comparator
impl LookupKey<NthByteComparator> for String {
    fn key(&self) -> &str { self.as_str() }
}
impl LookupKey<NthByteComparator> for str {
    fn key(&self) -> &str { self }
}

// create a collection using our comparator
let mut set = BTreeSet::new(NthByteComparator { n: 10 });
assert!(set.insert("abcdefghij".to_string()));
assert!(!set.insert("xxxxxxxxxj".to_string()));
assert!(set.contains("jjjjjjjjjj"));
```

# Collection type parameters
In addition to the type parameters familiar from the standard library collections, copse's
collections are additionally parameterised by the type of the [`Comparator`].  If the
comparator type is not explicitly named, it defaults to the [`OrdComparator`] for the
storage key's [`DefaultComparisonKey`][OrdStoredKey::DefaultComparisonKey], which yields
behaviour analagous to the standard library collections (i.e. sorted by the `Ord` trait).
If you find yourself using these items, then you should probably ditch copse for the
standard library instead.

# Crate feature flags
This crate defines a number of feature flags, none of which are enabled by default:

* the `std` feature provides [`OrdStoredKey`] implementations for some libstd types
  that are not available in libcore + liballoc, namely [`OsString`] and [`PathBuf`];

* the `unstable` feature enables all unstable features of the stdlib's BTree and
  BinaryHeap collection implementations that are purely contained therein, and which
  therefore do not require a nightly toolchain.

* the `btreemap_alloc` feature enables the like-named unstable compiler feature, thus
  exposing the collections' `new_in` methods; however this feature depends upon the
  `allocator_api` unstable compiler feature that is only available with a nightly
  toolchain.

* the `nightly` feature enables all other crate features, each of which enables the
  like-named unstable compiler feature that is used by the standard library's collection
  implementations (and which therefore require a nightly compiler)—most such behaviour
  is polyfilled when the features are disabled, so they should rarely be required, but
  they are nevertheless included to ease tracking of the stdlib implementations.

[std::collections::BTreeMap]: https://doc.rust-lang.org/std/collections/struct.BTreeMap.html
[std::collections::BTreeSet]: https://doc.rust-lang.org/std/collections/struct.BTreeSet.html
[std::collections::BinaryHeap]: https://doc.rust-lang.org/std/collections/struct.BinaryHeap.html
[`Ord`]: https://doc.rust-lang.org/std/cmp/trait.Ord.html
[`Borrow`]: https://doc.rust-lang.org/std/borrow/trait.Borrow.html
[`Borrow<Q>`]: https://doc.rust-lang.org/std/borrow/trait.Borrow.html
[`Ord::cmp`]: https://doc.rust-lang.org/std/cmp/trait.Ord.html#tymethod.cmp
[`OsString`]: https://doc.rust-lang.org/std/ffi/os_str/struct.OsString.html
[`PathBuf`]: https://doc.rust-lang.org/std/path/struct.PathBuf.html

[`Comparator`]: https://docs.rs/copse/latest/copse/trait.Comparator.html
[Comparator::Key]: https://docs.rs/copse/latest/copse/trait.Comparator.html#associatedtype.Key
[`LookupKey<C>`]: https://docs.rs/copse/latest/copse/trait.LookupKey.html
[`OrdComparator`]: https://docs.rs/copse/latest/copse/struct.OrdComparator.html
[`OrdStoredKey`]: https://docs.rs/copse/latest/copse/trait.OrdStoredKey.html
[OrdStoredKey::DefaultComparisonKey]: https://docs.rs/copse/latest/copse/trait.OrdStoredKey.html#associatedtype.DefaultComparisonKey
