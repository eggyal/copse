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
#![cfg_attr(docsrs, feature(doc_auto_cfg, doc_cfg, doc_cfg_hide))]
#![cfg_attr(docsrs, doc(cfg_hide(no_global_oom_handling)))]
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

/// A strict [total order] over the associated type [`OrderedType`].
///
/// This means that for all `a`, `b` and `c`:
///
/// 1. exactly one of `a < b`, `a == b` or `a > b` is true;
/// 2. `<` is the dual of `>`: that is, `a < b` if and only if `b > a`; and
/// 3. `<` is transitive: `a < b` and `b < c` implies `a < c`.
///    The same must hold for both `==` and `>`.
///
/// [total order]: https://en.wikipedia.org/wiki/Total_order
/// [`OrderedType`]: TotalOrder::OrderedType
pub trait TotalOrder {
    /// The type over which this total order is defined.
    type OrderedType: ?Sized;

    /// This method returns the [`Ordering`] between `this` and `that` under
    /// this total order.
    ///
    /// By convention, `self.cmp(&this, &that)` returns the ordering matching
    /// the expression `this <operator> that` if true.
    fn cmp(&self, this: &Self::OrderedType, that: &Self::OrderedType) -> Ordering;

    /// This method returns the [`Ordering`] between `this` and `that` under
    /// this total order.
    ///
    /// By convention, `self.cmp(&this, &that)` returns the ordering matching
    /// the expression `this <operator> that` if true.
    #[doc(hidden)]
    #[inline]
    fn cmp_any<A, B>(&self, this: &A, that: &B) -> Ordering
    where
        A: ?Sized + SortableBy<Self>,
        B: ?Sized + SortableBy<Self>,
    {
        self.cmp(this.sort_key(), that.sort_key())
    }

    /// Tests whether `this == that` under this total order.  It is a logic
    /// error for this method to be inconsistent with [`TotalOrder::cmp`],
    /// and therefore the default implementation should rarely be overriden.
    #[doc(hidden)]
    #[inline]
    fn eq<A, B>(&self, this: &A, that: &B) -> bool
    where
        A: ?Sized + SortableBy<Self>,
        B: ?Sized + SortableBy<Self>,
    {
        self.cmp_any(this, that).is_eq()
    }
    /// Tests whether `this != that` under this total order.  It is a logic
    /// error for this method to be inconsistent with [`TotalOrder::cmp`],
    /// and therefore the default implementation should rarely be overriden.
    #[doc(hidden)]
    #[inline]
    fn ne<A, B>(&self, this: &A, that: &B) -> bool
    where
        A: ?Sized + SortableBy<Self>,
        B: ?Sized + SortableBy<Self>,
    {
        self.cmp_any(this, that).is_ne()
    }

    /// Tests whether `this >= that` under this total order.  It is a logic
    /// error for this method to be inconsistent with [`TotalOrder::cmp`],
    /// and therefore the default implementation should rarely be overriden.
    #[doc(hidden)]
    #[inline]
    fn ge<A, B>(&self, this: &A, that: &B) -> bool
    where
        A: ?Sized + SortableBy<Self>,
        B: ?Sized + SortableBy<Self>,
    {
        self.cmp_any(this, that).is_ge()
    }
    /// Tests whether `this > that` under this total order.  It is a logic
    /// error for this method to be inconsistent with [`TotalOrder::cmp`],
    /// and therefore the default implementation should rarely be overriden.
    #[doc(hidden)]
    #[inline]
    fn gt<A, B>(&self, this: &A, that: &B) -> bool
    where
        A: ?Sized + SortableBy<Self>,
        B: ?Sized + SortableBy<Self>,
    {
        self.cmp_any(this, that).is_gt()
    }
    /// Tests whether `this <= that` under this total order.  It is a logic
    /// error for this method to be inconsistent with [`TotalOrder::cmp`],
    /// and therefore the default implementation should rarely be overriden.
    #[doc(hidden)]
    #[inline]
    fn le<A, B>(&self, this: &A, that: &B) -> bool
    where
        A: ?Sized + SortableBy<Self>,
        B: ?Sized + SortableBy<Self>,
    {
        self.cmp_any(this, that).is_le()
    }
    /// Tests whether `this < that` under this total order.  It is a logic
    /// error for this method to be inconsistent with [`TotalOrder::cmp`],
    /// and therefore the default implementation should rarely be overriden.
    #[doc(hidden)]
    #[inline]
    fn lt<A, B>(&self, this: &A, that: &B) -> bool
    where
        A: ?Sized + SortableBy<Self>,
        B: ?Sized + SortableBy<Self>,
    {
        self.cmp_any(this, that).is_lt()
    }
}

/// A type that is sorted under total orders of type parameter `O` by its [`sort_key`].
///
/// **Note that if you wish to use `O::OrderedType` itself, you must explicitly implement
/// `SortableBy<O>` for it even though that implementation will typically be a no-op.**
/// This case cannot be currently be provided for you by way of a blanket implementation
/// because that would conflict with the [blanket borrowing implementation] that is
/// provided for the default [`OrdTotalOrder`]; implementations for `O::OrderedType` that
/// are not no-ops are strongly discouraged, as they are prone to causing considerable
/// confusion: consider defining a distinct [`TotalOrder`] for any such use-case instead.
///
/// # Example
/// ```rust
/// struct MyOrdering;
///
/// impl TotalOrder for MyOrdering {
///     type OrderedType = str;
///     fn cmp(&self, this: &str, that: &str) -> Ordering { this.cmp(that) }
/// }
///
/// impl SortableBy<MyOrdering> for String {
///     fn sort_key(&self) -> &str { self.as_str() }
/// }
/// impl SortableBy<MyOrdering> for str {
///     fn sort_by(&self) -> &str { self }
/// }
///
/// let order = MyOrdering;
/// assert!(order.lt(&String::from("a"), "b"));
/// ```
///
/// [`sort_key`]: SortableBy::sort_key
/// [blanket borrowing implementation]: https://docs.rs/copse/latest/copse/trait.SortableBy.html#impl-SortableBy%3COrdTotalOrder%3CT%3E%3E-for-K
/// [`OrdTotalOrder`]: default::OrdTotalOrder
pub trait SortableBy<O: ?Sized + TotalOrder> {
    /// Extract the sort key by which `self` is ordered under total orders of type `O`.
    fn sort_key(&self) -> &O::OrderedType;
}
