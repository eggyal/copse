Direct ports of the standard library's [`BTreeMap`][std::collections::BTreeMap],
[`BTreeSet`][std::collections::BTreeSet] and [`BinaryHeap`][std::collections::BinaryHeap]
collections, but which sort with respect to some runtime context rather than relying upon the
[`Ord`] trait.

Whereas the types that you use with the standard library collections are required to implement
[`Ord`] and/or [`Borrow`], the types that you use with contextual_alloc's collections are
required to implement their respective contextual analogues from the [`contextual_core`] crate:
namely, [`ContextualOrd`] and/or [`ContextualBorrow`].  Furthermore, as with the comparison traits
in the standard library, [`ContextualOrd`] has supertraits [`ContextualPartialOrd`],
[`ContextualPartialEq`] and [`ContextualEq`]—all of which must therefore be implemented on types
that implement [`ContextualOrd`].

Unfortunately, this is not as straightforward as with the standard library versions:

1. you cannot `#[derive]` the contextual comparison traits (as one will often have done with the
   standard library traits) because the derivation macro requires implementation details for your
   context;

2. there are no blanket reflexive implementations of the [`ContextualBorrow`] trait because it
   would conflict with the blanket implementation that is provided for [`NoContext`]; and

3. indeed no implementations whatsoever of the [`ContextualBorrow`] trait are provided for generic
   contexts, as particular contexts may have their own specific requirements.

Fortunately, the [`contextual`] macro significantly mitigates the burden these restrictions might
otherwise impose.  Generally speaking, you will invoke the macro with a `cmp` definition for the
basis of your key comparisons and zero or more `borrow` definitions for any other types with which
you may wish to perform lookups into a `contextual_alloc` collection.

# Example
```rust
use contextual_alloc::{collections::BTreeSet, contextual_core::contextual};

// define a runtime context
struct OrderByNthByte {
    n: usize, // runtime state
}

contextual! {
    fn cmp(&self, other: &[u8], context: &OrderByNthByte) -> Ordering {
        self.get(context.n).cmp(&other.get(context.n))
    }
    fn borrow(self: &str, _: &OrderByNthByte) -> &[u8], delegating cmp { self.as_bytes() }
    fn borrow(self: &String, _: &OrderByNthByte) -> &str, delegating cmp { self }
}

// create a collection using our runtime context
let mut set = BTreeSet::new(OrderByNthByte { n: 9 });
assert!(set.insert("abcdefghijklm".to_string()));
assert!(!set.insert("xxxxxxxxxjxx".to_string()));
assert!(set.contains("jjjjjjjjjj"));
```

# Collection type parameters
In addition to the type parameters familiar from the standard library collections,
`contextual_alloc`'s collections are additionally parameterised by the type of the runtime
context.  If the runtime context is not explicitly named, it defaults to the zero-sized
[`NoContext`], which yields behaviour analagous to the standard library collections (i.e. sorted by
the [`Ord`] trait); explicitly using [`NoContext`] indicates that you could (and probably *should*)
ditch contextual_alloc for the standard library instead.

# Crate feature flags
This crate defines a number of [feature flags], none of which are enabled by default:

* each feature in the [`unstable`] set corresponds to the like-named unstable feature in the
  standard library's B-Tree and BinaryHeap collection implementations, all of which enable APIs
  that are wholly contained within the library and therefore do not require a nightly toolchain;

* the [`btreemap_alloc`] feature corresponds to the like-named unstable feature in the standard
  library's B-Tree collection implementations (namely that which enables their `new_in` associated
  functions)—however (as of rustc v1.66.1) this feature requires the [`allocator_api`] unstable
  compiler feature that is only available with a nightly toolchain; and

* all other features (combined into the [`nightly`] set) do not affect the APIs presented by this
  crate, but instead switch the implementation to use those features internally as are used by the
  standard library's implementations—these features should be of little use or interest to library
  users, but are nevertheless included to ease synchronisation with the standard library.

[std::collections::BTreeMap]: https://doc.rust-lang.org/std/collections/struct.BTreeMap.html
[std::collections::BTreeSet]: https://doc.rust-lang.org/std/collections/struct.BTreeSet.html
[std::collections::BinaryHeap]: https://doc.rust-lang.org/std/collections/struct.BinaryHeap.html
[`Ord`]: https://doc.rust-lang.org/std/cmp/trait.Ord.html
[`Borrow`]: https://doc.rust-lang.org/std/borrow/trait.Borrow.html

[`contextual_core`]: https://docs.rs/contextual_core/latest/
[`ContextualBorrow`]: https://docs.rs/contextual_core/latest/borrow/trait.ContextualBorrow.html
[`ContextualEq`]: https://docs.rs/contextual_core/latest/cmp/trait.ContextualEq.html
[`ContextualOrd`]: https://docs.rs/contextual_core/latest/cmp/trait.ContextualOrd.html
[`ContextualPartialEq`]: https://docs.rs/contextual_core/latest/cmp/trait.ContextualPartialEq.html
[`ContextualPartialOrd`]: https://docs.rs/contextual_core/latest/cmp/trait.ContextualPartialOrd.html
[`NoContext`]: https://docs.rs/contextual_core/latest/cmp/struct.NoContext.html
[`contextual`]: https://docs.rs/contextual_core/latest/macro.contextual.html

[feature flags]: https://docs.rs/crate/contextual_alloc/latest/features
[`unstable`]: https://docs.rs/crate/contextual_alloc/latest/features#unstable
[`btreemap_alloc`]: https://docs.rs/crate/contextual_alloc/latest/features#btreemap_alloc
[`allocator_api`]: https://docs.rs/crate/contextual_alloc/latest/features#allocator_api
[`nightly`]: https://docs.rs/crate/contextual_alloc/latest/features#nightly
