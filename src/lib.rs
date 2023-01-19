//! Direct ports of the standard library's [`BTreeMap`][std::collections::BTreeMap],
//! [`BTreeSet`][std::collections::BTreeSet] and [`BinaryHeap`][std::collections::BinaryHeap]
//! collections, but which sort according to a specified [`TotalOrder`] rather than relying upon
//! the [`Ord`] trait.
//!
//! This is primarily useful when the [`TotalOrder`] depends upon runtime state, and therefore
//! cannot be provided as an [`Ord`] implementation for any type.
//!
//! # Lookup keys
//! In the standard library's collections, certain lookups can be performed using a key of type
//! `&Q` where the collection's storage key type `K` implements [`Borrow<Q>`]; for example, one
//! can use `&str` keys to perform lookups into collections that store `String` keys.  This is
//! possible because the [`Borrow`] trait stipulates that borrowed values must preserve [`Ord`]
//! order.
//!
//! However, copse's collections do not use the [`Ord`] trait; instead, lookups can only ever
//! be performed using the [`TotalOrder`] supplied upon collection creation.  This total order
//! can only compare values of its [`OrderedType`][TotalOrder::OrderedType] associated type,
//! and hence keys used for lookups must implement [`LookupKey<O>`] in order that the
//! conversion can be performed.
//!
//! # Example
//! ```rust
//! # use core::cmp::Ordering;
//! # use copse::{TotalOrder, LookupKey, BTreeSet};
//! #
//! // define a total order
//! struct OrderByNthByte {
//!     n: usize, // runtime state
//! }
//!
//! impl TotalOrder for OrderByNthByte {
//!     type OrderedType = [u8];
//!     fn cmp(&self, this: &[u8], that: &[u8]) -> Ordering {
//!         match (this.get(self.n), that.get(self.n)) {
//!             (Some(lhs), Some(rhs)) => lhs.cmp(rhs),
//!             (Some(_), None) => Ordering::Greater,
//!             (None, Some(_)) => Ordering::Less,
//!             (None, None) => Ordering::Equal,
//!         }
//!     }
//! }
//!
//! // define lookup key types for collections sorted by our total order
//! impl LookupKey<OrderByNthByte> for [u8] {
//!     fn key(&self) -> &[u8] { self }
//! }
//! impl LookupKey<OrderByNthByte> for str {
//!     fn key(&self) -> &[u8] { self.as_bytes() }
//! }
//! impl LookupKey<OrderByNthByte> for String {
//!     fn key(&self) -> &[u8] { LookupKey::<OrderByNthByte>::key(self.as_str()) }
//! }
//!
//! // create a collection using our total order
//! let mut set = BTreeSet::new(OrderByNthByte { n: 9 });
//! assert!(set.insert("abcdefghijklm".to_string()));
//! assert!(!set.insert("xxxxxxxxxjxx".to_string()));
//! assert!(set.contains("jjjjjjjjjj"));
//! ```
//!
//! # Collection type parameters
//! In addition to the type parameters familiar from the standard library collections, copse's
//! collections are additionally parameterised by the type of the [`TotalOrder`].  If the
//! total order is not explicitly named, it defaults to the [`OrdTotalOrder`] for the storage
//! key's [`DefaultComparisonKey`][OrdStoredKey::DefaultComparisonKey], which yields behaviour
//! analagous to the standard library collections (i.e. sorted by the `Ord` trait).  If you
//! find yourself using these items, then you should probably ditch copse for the standard
//! library instead.
//!
//! # Crate feature flags
//! This crate defines a number of feature flags, none of which are enabled by default:
//!
//! * the `std` feature provides [`OrdStoredKey`] implementations for some libstd types
//!   that are not available in libcore + liballoc, namely [`OsString`] and [`PathBuf`];
//!
//! * the `unstable` feature enables all unstable features of the stdlib's BTree and
//!   BinaryHeap collection implementations that are purely contained therein, and which
//!   therefore do not require a nightly toolchain.
//!
//! * the `btreemap_alloc` feature enables the like-named unstable compiler feature, thus
//!   exposing the collections' `new_in` methods; however this feature depends upon the
//!   `allocator_api` unstable compiler feature that is only available with a nightly
//!   toolchain.
//!
//! * the `nightly` feature enables all other crate features, each of which enables the
//!   like-named unstable compiler feature that is used by the standard library's collection
//!   implementations (and which therefore require a nightly compiler)—most such behaviour
//!   is polyfilled when the features are disabled, so they should rarely be required, but
//!   they are nevertheless included to ease tracking of the stdlib implementations.
//!
//! [`Borrow`]: std::borrow::Borrow
//! [`Borrow<Q>`]: std::borrow::Borrow
//! [`Ord`]: std::cmp::Ord
//! [`Ord::cmp`]: std::cmp::Ord::cmp
//! [`OrdComparator`]: default::OrdComparator
//! [`OrdStoredKey`]: default::OrdStoredKey
//! [OrdStoredKey::DefaultComparisonKey]: default::OrdStoredKey::DefaultComparisonKey
//! [`OrdTotalOrder`]: default::OrdTotalOrder
//! [`OsString`]: std::ffi::OsString
//! [`PathBuf`]: std::path::PathBuf

#![cfg_attr(not(any(feature = "std", test)), no_std)]
#![cfg_attr(feature = "allocator_api", feature(allocator_api))]
#![cfg_attr(feature = "core_intrinsics", feature(core_intrinsics))]
#![cfg_attr(feature = "dropck_eyepatch", feature(dropck_eyepatch))]
#![cfg_attr(feature = "error_in_core", feature(error_in_core))]
#![cfg_attr(feature = "exact_size_is_empty", feature(exact_size_is_empty))]
#![cfg_attr(feature = "exclusive_range_pattern", feature(exclusive_range_pattern))]
#![cfg_attr(feature = "extend_one", feature(extend_one))]
#![cfg_attr(feature = "hasher_prefixfree_extras", feature(hasher_prefixfree_extras))]
#![cfg_attr(feature = "inline_const", feature(inline_const))]
#![cfg_attr(feature = "inplace_iteration", feature(inplace_iteration))]
#![cfg_attr(feature = "is_sorted", feature(is_sorted))]
#![cfg_attr(feature = "maybe_uninit_slice", feature(maybe_uninit_slice))]
#![cfg_attr(feature = "new_uninit", feature(new_uninit))]
#![cfg_attr(feature = "rustc_attrs", feature(rustc_attrs))]
#![cfg_attr(feature = "slice_ptr_get", feature(slice_ptr_get))]
#![cfg_attr(feature = "specialization", feature(specialization))]
#![cfg_attr(feature = "trusted_len", feature(trusted_len))]
// documentation controls
#![cfg_attr(docsrs, feature(doc_auto_cfg, doc_cfg))]
#![deny(missing_docs)]
// linting controls
#![cfg_attr(feature = "specialization", allow(incomplete_features))]

#[macro_use]
extern crate alloc;

use core::cmp::Ordering;

#[macro_use]
mod polyfill;
pub mod default;

// port of stdlib implementation
mod liballoc;
pub use liballoc::collections::{binary_heap, btree_map, btree_set};

#[cfg(not(no_global_oom_handling))]
#[doc(no_inline)]
pub use binary_heap::BinaryHeap;

#[cfg(not(no_global_oom_handling))]
#[doc(no_inline)]
pub use btree_map::BTreeMap;

#[cfg(not(no_global_oom_handling))]
#[doc(no_inline)]
pub use btree_set::BTreeSet;

/// An immutable strict [total order] over the associated type [`OrderedType`].
/// This means that for all `a`, `b` and `c`:
///
/// 1. exactly one of `a < b`, `a == b` or `a > b` remains true *throughout the
///    life of `self`*;
/// 2. `<` is the dual of `>`: that is, `a < b` if and only if `b > a`; and
/// 3. `<` is transitive: `a < b` and `b < c` implies `a < c`.
///    The same must hold for both `==` and `>`.
///
/// [total order]: https://en.wikipedia.org/wiki/Total_order
/// [`OrderedType`]: TotalOrder::OrderedType
pub trait TotalOrder {
    /// The type over which this total order is defined.
    type OrderedType: ?Sized;

    /// Compare two values and return the position of `this` relative
    /// to `that` according to this total order.
    ///
    /// The comparison must satisfy both transitivity and duality.
    fn cmp(&self, this: &Self::OrderedType, that: &Self::OrderedType) -> Ordering;

    /// Tests whether `this == that` under this total order.  It is a logic
    /// error for this method to be inconsistent with [`TotalOrder::cmp`],
    /// and therefore the default implementation should rarely be overriden.
    #[doc(hidden)]
    #[inline]
    fn eq(&self, this: &Self::OrderedType, that: &Self::OrderedType) -> bool {
        self.cmp(this, that).is_eq()
    }
    /// Tests whether `this != that` under this total order.  It is a logic
    /// error for this method to be inconsistent with [`TotalOrder::cmp`],
    /// and therefore the default implementation should rarely be overriden.
    #[doc(hidden)]
    #[inline]
    fn ne(&self, this: &Self::OrderedType, that: &Self::OrderedType) -> bool {
        self.cmp(this, that).is_ne()
    }

    /// Tests whether `this >= that` under this total order.  It is a logic
    /// error for this method to be inconsistent with [`TotalOrder::cmp`],
    /// and therefore the default implementation should rarely be overriden.
    #[doc(hidden)]
    #[inline]
    fn ge(&self, this: &Self::OrderedType, that: &Self::OrderedType) -> bool {
        self.cmp(this, that).is_ge()
    }
    /// Tests whether `this > that` under this total order.  It is a logic
    /// error for this method to be inconsistent with [`TotalOrder::cmp`],
    /// and therefore the default implementation should rarely be overriden.
    #[doc(hidden)]
    #[inline]
    fn gt(&self, this: &Self::OrderedType, that: &Self::OrderedType) -> bool {
        self.cmp(this, that).is_gt()
    }
    /// Tests whether `this <= that` under this total order.  It is a logic
    /// error for this method to be inconsistent with [`TotalOrder::cmp`],
    /// and therefore the default implementation should rarely be overriden.
    #[doc(hidden)]
    #[inline]
    fn le(&self, this: &Self::OrderedType, that: &Self::OrderedType) -> bool {
        self.cmp(this, that).is_le()
    }
    /// Tests whether `this < that` under this total order.  It is a logic
    /// error for this method to be inconsistent with [`TotalOrder::cmp`],
    /// and therefore the default implementation should rarely be overriden.
    #[doc(hidden)]
    #[inline]
    fn lt(&self, this: &Self::OrderedType, that: &Self::OrderedType) -> bool {
        self.cmp(this, that).is_lt()
    }
}

/// A type that can be used as a lookup key in collections that are sorted by total orders
/// of type parameter `O`.
///
/// For example, if `MyOrdering` is a [`TotalOrder<OrderedType = str>`], then you may wish
/// to implement [`LookupKey<MyOrdering>`] for both [`String`] and [`str`] in order that
/// keys of those types can be used to search collections ordered by any total order of
/// type `MyOrdering`.  **Note that you must provide such implementation even for the
/// reflexive/no-op case, which will almost always be desirable.**
pub trait LookupKey<O: TotalOrder> {
    /// Return the key by which `self` is ordered under total orders of type `O`.
    fn key(&self) -> &O::OrderedType;
}
