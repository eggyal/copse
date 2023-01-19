#![doc = include_str!("../README.md")]
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
