Direct ports of the standard library's comparison ([`Ord`], [`PartialOrd`], [`PartialEq`] and [`Eq`])
and borrowing ([`Borrow`] and [`BorrowMut`]) traits, but whose methods additionally accept a context
value of custom type.

Ports of [`Iterator`] methods that utilise those traits are further provided by way of a
blanket-implemented extension trait.

A macro is also provided to ease the implementation of these traits.

While the examples shown in this crate's documentation all use [`NoContext`], and thereby exhibit
the same behaviour as the analogous parts of the standard library, you will typically substitute
the type of your own context in its place and (may) utilise such context in the resulting methods.
If you find yourself explicitly using [`NoContext`], then you could (and probably *should*) just
use the standard library types instead.

# Crate feature flags

This crate defines a single feature flag, [`is_sorted`], which enables the contextual analogues of
standard library [`Iterator`] methods that are gated behind a feature flag of the same name.

[`Eq`]: https://doc.rust-lang.org/std/cmp/trait.Eq.html
[`Ord`]: https://doc.rust-lang.org/std/cmp/trait.Ord.html
[`PartialEq`]: https://doc.rust-lang.org/std/cmp/trait.PartialEq.html
[`PartialOrd`]: https://doc.rust-lang.org/std/cmp/trait.PartialOrd.html
[`Borrow`]: https://doc.rust-lang.org/std/borrow/trait.Borrow.html
[`BorrowMut`]: https://doc.rust-lang.org/std/borrow/trait.BorrowMut.html
[`Iterator`]: https://doc.rust-lang.org/std/iter/trait.Iterator.html

[`NoContext`]: https://docs.rs/crate/contextual_core/latest/struct.NoContext.html
[`is_sorted`]: https://docs.rs/crate/contextual_core/latest/features#is_sorted
