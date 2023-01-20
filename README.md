Direct ports of the standard library's [`BTreeMap`][std::collections::BTreeMap],
[`BTreeSet`][std::collections::BTreeSet] and [`BinaryHeap`][std::collections::BinaryHeap]
collections, but which sort according to a specified [`TotalOrder`] rather than relying upon
the [`Ord`] trait.

This is primarily useful when the [`TotalOrder`] depends upon runtime state, and therefore
cannot be provided as an [`Ord`] implementation for any type.

# Lookup keys
In the standard library's collections, certain lookups can be performed using a key of type
`&Q` where the collection's storage key type `K` implements [`Borrow<Q>`]; for example, one
can use `&str` keys to perform lookups into collections that store `String` keys.  This is
possible because `String: Borrow<str>` and the [`Borrow`] trait stipulates that borrowed
values must preserve [`Ord`] order.

However, copse's collections do not use the [`Ord`] trait; instead, lookups can only ever
be performed using the [`TotalOrder`] supplied upon collection creation.  This total order
can only compare values of its [`OrderedType`][TotalOrder::OrderedType] associated type,
and hence keys used for lookups must implement [`SortableBy<O>`] in order that the
conversion can be performed.

# Example
```rust
// define a total order
struct OrderByNthByte {
    n: usize, // runtime state
}

impl TotalOrder for OrderByNthByte {
    type OrderedType = [u8];
    fn cmp(&self, this: &[u8], that: &[u8]) -> Ordering {
        match (this.get(self.n), that.get(self.n)) {
            (Some(lhs), Some(rhs)) => lhs.cmp(rhs),
            (Some(_), None) => Ordering::Greater,
            (None, Some(_)) => Ordering::Less,
            (None, None) => Ordering::Equal,
        }
    }
}

// define lookup key types for collections sorted by our total order
impl SortableBy<OrderByNthByte> for [u8] {
    fn key(&self) -> &[u8] { self }
}
impl SortableBy<OrderByNthByte> for str {
    fn key(&self) -> &[u8] { self.as_bytes() }
}
impl SortableBy<OrderByNthByte> for String {
    fn key(&self) -> &[u8] { SortableBy::<OrderByNthByte>::key(self.as_str()) }
}

// create a collection using our total order
let mut set = BTreeSet::new(OrderByNthByte { n: 9 });
assert!(set.insert("abcdefghijklm".to_string()));
assert!(!set.insert("xxxxxxxxxjxx".to_string()));
assert!(set.contains("jjjjjjjjjj"));
```

# Collection type parameters
In addition to the type parameters familiar from the standard library collections, copse's
collections are additionally parameterised by the type of the [`TotalOrder`].  If the
total order is not explicitly named, it defaults to the [`OrdTotalOrder`] for the storage
key's [`DefaultComparisonKey`][OrdStoredKey::DefaultComparisonKey], which yields behaviour
analagous to the standard library collections (i.e. sorted by the [`Ord`] trait).  If you
find yourself using these items, then you should probably ditch copse for the standard
library instead.

# Crate feature flags
This crate defines a number of [feature flags], none of which are enabled by default:

* the [`std`] feature provides [`OrdStoredKey`] implementations for some standard library
  types that are not present in libcore + liballoc, namely [`OsString`], [`OsStr`],
  [`PathBuf`] and [`Path`];

* each feature in the [`unstable`] set corresponds to the like-named unstable feature in
  the standard library's B-Tree and BinaryHeap collection implementations, all of which
  enable APIs that are wholly contained within the library and therefore do not require
  a nightly toolchain;

* the [`btreemap_alloc`] feature corresponds to the like-named unstable feature in the
  standard library's B-Tree collection implementations (namely that which enables their
  `new_in` associated functions)—however (as of rustc v1.66.1) this feature requires
  the [`allocator_api`] unstable compiler feature that is only available with a nightly
  toolchain; and

* all other features (combined into the [`nightly`] set) do not affect the APIs presented
  by this crate, but instead switch the implementation to use those features internally
  as are used by the standard library's implementations—these features should be of
  little use or interest to library users, but are nevertheless included to ease
  synchronisation with the standard library.

[std::collections::BTreeMap]: https://doc.rust-lang.org/std/collections/struct.BTreeMap.html
[std::collections::BTreeSet]: https://doc.rust-lang.org/std/collections/struct.BTreeSet.html
[std::collections::BinaryHeap]: https://doc.rust-lang.org/std/collections/struct.BinaryHeap.html
[`Ord`]: https://doc.rust-lang.org/std/cmp/trait.Ord.html
[`Borrow`]: https://doc.rust-lang.org/std/borrow/trait.Borrow.html
[`Borrow<Q>`]: https://doc.rust-lang.org/std/borrow/trait.Borrow.html
[`Ord::cmp`]: https://doc.rust-lang.org/std/cmp/trait.Ord.html#tymethod.cmp
[`OsString`]: https://doc.rust-lang.org/std/ffi/os_str/struct.OsString.html
[`OsStr`]: https://doc.rust-lang.org/std/ffi/os_str/struct.OsStr.html
[`PathBuf`]: https://doc.rust-lang.org/std/path/struct.PathBuf.html
[`Path`]: https://doc.rust-lang.org/std/path/struct.Path.html

[`TotalOrder`]: https://docs.rs/copse/latest/copse/trait.TotalOrder.html
[TotalOrder::OrderedType]: https://docs.rs/copse/latest/copse/trait.TotalOrder.html#associatedtype.OrderedType
[`SortableBy<O>`]: https://docs.rs/copse/latest/copse/trait.SortableBy.html
[`OrdTotalOrder`]: https://docs.rs/copse/latest/copse/default/struct.OrdTotalOrder.html
[`OrdStoredKey`]: https://docs.rs/copse/latest/copse/default/trait.OrdStoredKey.html
[OrdStoredKey::DefaultComparisonKey]: https://docs.rs/copse/latest/copse/default/trait.OrdStoredKey.html#associatedtype.DefaultComparisonKey

[feature flags]: https://docs.rs/crate/copse/latest/features
[`std`]: https://docs.rs/crate/copse/latest/features#std
[`unstable`]: https://docs.rs/crate/copse/latest/features#unstable
[`btreemap_alloc`]: https://docs.rs/crate/copse/latest/features#btreemap_alloc
[`allocator_api`]: https://docs.rs/crate/copse/latest/features#allocator_api
[`nightly`]: https://docs.rs/crate/copse/latest/features#nightly
