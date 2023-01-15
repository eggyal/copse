//! Direct ports of the standard library's [`BTreeMap`][std::collections::BTreeMap],
//! [`BTreeSet`][std::collections::BTreeSet] and [`BinaryHeap`][std::collections::BinaryHeap]
//! collections, but which sort according to a specified [`Comparator`] rather than relying upon
//! the [`Ord`] trait.
//!
//! This is primarily useful when the [`Comparator`] depends upon runtime state, and therefore
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
//! be performed using the [`Comparator`] supplied upon collection creation.  This comparator
//! can only compare values of its [`Key`][Comparator::Key] associated type, and hence keys used
//! for lookups must implement [`LookupKey<C>`] in order that the conversion can be performed.
//!
//! # Example
//! ```rust
//! # use core::cmp::Ordering;
//! # use copse::{Comparator, LookupKey, BTreeSet};
//! #
//! // define a comparator
//! struct NthByteComparator {
//!     n: usize, // runtime state
//! }
//!
//! impl Comparator for NthByteComparator {
//!     type Key = [u8];
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
//! // define lookup key types for collections sorted by our comparator
//! impl LookupKey<NthByteComparator> for [u8] {
//!     fn key(&self) -> &[u8] { self }
//! }
//! impl LookupKey<NthByteComparator> for str {
//!     fn key(&self) -> &[u8] { self.as_bytes() }
//! }
//! impl LookupKey<NthByteComparator> for String {
//!     fn key(&self) -> &[u8] { LookupKey::<NthByteComparator>::key(self.as_str()) }
//! }
//!
//! // create a collection using our comparator
//! let mut set = BTreeSet::new(NthByteComparator { n: 9 });
//! assert!(set.insert("abcdefghijklm".to_string()));
//! assert!(!set.insert("xxxxxxxxxjxx".to_string()));
//! assert!(set.contains("jjjjjjjjjj"));
//! ```
//!
//! # Collection type parameters
//! In addition to the type parameters familiar from the standard library collections, copse's
//! collections are additionally parameterised by the type of the [`Comparator`].  If the
//! comparator type is not explicitly named, it defaults to the [`OrdComparator`] for the
//! storage key's [`DefaultComparisonKey`][OrdStoredKey::DefaultComparisonKey], which yields
//! behaviour analagous to the standard library collections (i.e. sorted by the `Ord` trait).
//! If you find yourself using these items, then you should probably ditch copse for the
//! standard library instead.
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

use alloc::{boxed::Box, vec::Vec};
use core::{borrow::Borrow, cmp::Ordering, marker::PhantomData};

#[macro_use]
mod polyfill;

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

/// A comparator defines a total order over its associated type `Key`.
pub trait Comparator {
    /// The type over which this comparator defines a total order.
    type Key: ?Sized;

    /// Compare two values and return the position of `this` relative
    /// to `that` according to the total order defined by this comparator.
    ///
    /// The comparison must satisfy both transitivity and duality.
    fn cmp(&self, this: &Self::Key, that: &Self::Key) -> Ordering;

    /// Tests whether `this == that` under the total order defined by this
    /// comparator.
    fn eq(&self, this: &Self::Key, that: &Self::Key) -> bool {
        self.cmp(this, that).is_eq()
    }
    /// Tests whether `this != that` under the total order defined by this
    /// comparator.
    fn ne(&self, this: &Self::Key, that: &Self::Key) -> bool {
        self.cmp(this, that).is_ne()
    }

    /// Tests whether `this >= that` under the total order defined by this
    /// comparator.
    fn ge(&self, this: &Self::Key, that: &Self::Key) -> bool {
        self.cmp(this, that).is_ge()
    }
    /// Tests whether `this > that` under the total order defined by this
    /// comparator.
    fn gt(&self, this: &Self::Key, that: &Self::Key) -> bool {
        self.cmp(this, that).is_gt()
    }
    /// Tests whether `this <= that` under the total order defined by this
    /// comparator.
    fn le(&self, this: &Self::Key, that: &Self::Key) -> bool {
        self.cmp(this, that).is_le()
    }
    /// Tests whether `this < that` under the total order defined by this
    /// comparator.
    fn lt(&self, this: &Self::Key, that: &Self::Key) -> bool {
        self.cmp(this, that).is_lt()
    }
}

/// A zero-sized comparator that delegates to the [`Ord`] implementation
/// of its type parameter `T`.
pub struct OrdComparator<T: ?Sized + Ord>(PhantomData<fn(&T)>);

impl<T: ?Sized + Ord> Default for OrdComparator<T> {
    fn default() -> Self {
        Self(PhantomData)
    }
}

impl<T: ?Sized + Ord> Clone for OrdComparator<T> {
    fn clone(&self) -> Self {
        Self(PhantomData)
    }
}

impl<T: ?Sized + Ord> Copy for OrdComparator<T> {}

impl<T: ?Sized + Ord> Comparator for OrdComparator<T> {
    type Key = T;

    fn cmp(&self, this: &T, that: &T) -> Ordering {
        this.cmp(that)
    }

    fn eq(&self, this: &T, that: &T) -> bool {
        this == that
    }
    fn ne(&self, this: &T, that: &T) -> bool {
        this != that
    }

    fn ge(&self, this: &T, that: &T) -> bool {
        this >= that
    }
    fn gt(&self, this: &T, that: &T) -> bool {
        this > that
    }
    fn le(&self, this: &T, that: &T) -> bool {
        this <= that
    }
    fn lt(&self, this: &T, that: &T) -> bool {
        this < that
    }
}

/// A type that can be used as a lookup key in collections that are sorted by comparators of
/// type `C`.
///
/// For example, if `MyComparator` is a [`Comparator<str>`], then you may wish to implement
/// `LookupKey<MyComparator>` for both `String` and `str` in order that keys of those types
/// can be used to search collections ordered by a comparator of type `MyComparator`.  Note
/// that you must provide such implementation even for the reflexive/no-op case, which will
/// almost always be desirable.
pub trait LookupKey<C: Comparator> {
    /// Returns a reference to the comparison key type.
    fn key(&self) -> &C::Key;
}

impl<T: ?Sized + Ord, K: ?Sized + Borrow<T>> LookupKey<OrdComparator<T>> for K {
    fn key(&self) -> &T {
        self.borrow()
    }
}

/// A helper trait implemented on potential storage key types, used to identify their default
/// comparison type for `Ord`-based comparisons.
///
/// This is only really used when collections are left to select the default [`OrdComparator`]
/// comparator, which essentially converts copse's collections into those already provided by
/// the standard library.  This trait is therefore a convenience, but of relatively little value.
///
/// For example, a collection that stores `String` under the default comparator will use `str`
/// as the comparison type owing to the implementation of this trait for `String`.
pub trait OrdStoredKey: LookupKey<OrdComparator<Self::DefaultComparisonKey>> {
    /// The comparison type to be used by collections storing keys of `Self` type and using the
    /// default [`OrdComparator`] comparator.
    type DefaultComparisonKey: ?Sized + Ord;
}

macro_rules! ord_keys {
    // end of recursion
    () => {};

    // implement type and recurse
    ($(#[$attrs:meta])* $({$($g:tt)+})? $t:ty => $m:ty $(, $($rest:tt)*)?) => {
        $(#[$attrs])*
        impl$(<$($g)+>)? OrdStoredKey for $t {
            type DefaultComparisonKey = $m;
        }

        $(ord_keys!($($rest)*);)?
    };

    // delegate to a reflexive implementation if no State is specified
    ($(#[$attrs:meta])* $({$($g:tt)+})? $t:ty $(, $($rest:tt)*)?) => {
        ord_keys!($(#[$attrs])* $({$($g)+})? $t => Self $(, $($rest)*)?);
    };
}

ord_keys! {
    (),
    bool, char,
    i8, u8,
    i16, u16,
    i32, u32,
    i64, u64,
    i128, u128,
    isize, usize,
    alloc::string::String => str, str,
    alloc::ffi::CString => core::ffi::CStr, core::ffi::CStr,
    {B: ?Sized + Ord + Clone} alloc::borrow::Cow<'_, B> => B,
    {T: ?Sized + Ord} &T => T,
    {T: ?Sized + Ord} &mut T => T,
    {T: ?Sized + Ord} alloc::rc::Rc<T> => T,
    {T: ?Sized + Ord} alloc::sync::Arc<T> => T,
    {T: Ord, const N: usize} [T; N] => [T], {T: Ord} [T],
    #[cfg(feature = "std")] std::ffi::OsString => std::ffi::OsStr, #[cfg(feature = "std")] std::ffi::OsStr,
    #[cfg(feature = "std")] std::path::PathBuf => std::path::Path, #[cfg(feature = "std")] std::path::Path,
    {T: Ord, #[cfg(feature = "allocator_api")] A: alloc::alloc::Allocator} A!(Vec<T, A>) => [T],
    {T: Ord + ?Sized, #[cfg(feature = "allocator_api")] A: alloc::alloc::Allocator} A!(Box<T, A>) => T,
}
