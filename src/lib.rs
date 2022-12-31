//! Direct ports of the standard library's [`BTreeMap`][std::collections::BTreeMap] and
//! [`BTreeSet`][std::collections::BTreeSet] collections, but which sort according to a specified
//! [`Comparator`] rather than relying upon the [`Ord`] trait.
//!
//! This is primarily useful when the [`Comparator`] is not defined until runtime, and therefore
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
//! be performed using the [`Comparator<T>`] supplied upon collection creation.  This comparator
//! can only compare values of type `&T` for which it was defined, and hence such type must be
//! reachable from any key type `&Q` used to perform lookups in the collection.  copse ensures
//! this via its [`Sortable`] trait, which will typically be implemented by the stored key type
//! `K`; its [`State`][Sortable::State] associated type then specifies the `T` in which
//! comparisons will be performed, and values of type `&Q` can be used as lookup keys provided
//! that `Q: Borrow<T>`.
//!
//! For example, a collection using a `Comparator<str>` comparator can store keys of type
//! `String` because `String` implements `Sortable<State = str>`; moreover, lookups can be
//! performed using keys of type `&str` because `str` implements `Borrow<str>` (due to the
//! reflexive blanket implementation).
//!
//! Implementations of [`Sortable`] are provided for primitive and some common standard library
//! types, but storing keys of other foreign types may require newtyping.
//!
//! # Function item types
//! In addition to the type parameters familiar from the standard library collections, copse's
//! collections are additionally parameterised by the type of the [`Comparator`].  If the
//! comparator type is not explicitly named, it defaults to the type of the [`Ord::cmp`]
//! function for `K::State`.  As noted in the documentation of the [`CmpFn`] type alias, this
//! is only a zero-sized function item type if the unstable `type_alias_impl_trait` feature is
//! enabled; otherwise it is a function pointer type, with ensuing size and indirect call
//! implications.  Collections built using the zero-sized function item type can still be
//! used in stable code, however; just not using the default type parameter.  For example:
//!
//! ```rust
//! # use std::cmp::Ord;
//! # use copse::BTreeMap;
//! let mut ord_map = BTreeMap::new(Ord::cmp);
//! # ord_map.insert(123, "hello");
//! ```
//!
//! However, naming this type carries the usual problems associated with anonymous types like
//! closures; in certain situations you may be able to use `impl Comparator` for the type
//! parameter, but in other situations (in stable code) the function pointer may be
//! unavoidable.
//!
//! # Crate feature flags
//! This crate defines a number of feature flags, none of which are enabled by default:
//!
//! * the `std` feature provides [`Sortable`] implementations for some libstd types
//!   that are not available in libcore + liballoc, namely [`OsString`] and [`PathBuf`];
//!
//! * the `unstable` feature enables all other crate features, each of which enables the
//!   like-named unstable compiler feature that is used by the standard library's collection
//!   implementations (and which therefore require a nightly compiler)—most such behaviour
//!   is polyfilled when the features are disabled, so they should rarely be required, but
//!   they are nevertheless included to ease tracking of the stdlib implementations.
//!   
//!   The most visible differences to library users will be:
//!     * `allocator_api` enables the `new_in` methods for use of custom allocators;
//!     * `specialization` adds the collection type name to some panic messages;
//!     * `type_alias_impl_trait`, as mentioned above, ensures that the *default*
//!        [`Comparator`] type parameter for the collections is the zero-sized function
//!        item type of the `K::State::cmp` function.
//!
//! [`Ord`]: std::cmp::Ord
//! [`Ord::cmp`]: std::cmp::Ord::cmp
//! [`OsString`]: std::ffi::OsString
//! [`PathBuf`]: std::path::PathBuf

#![cfg_attr(not(any(feature = "std", test)), no_std)]
#![cfg_attr(feature = "allocator_api", feature(allocator_api))]
#![cfg_attr(feature = "bound_map", feature(bound_map))]
#![cfg_attr(feature = "core_intrinsics", feature(core_intrinsics))]
#![cfg_attr(feature = "dropck_eyepatch", feature(dropck_eyepatch))]
#![cfg_attr(feature = "error_in_core", feature(error_in_core))]
#![cfg_attr(feature = "exact_size_is_empty", feature(exact_size_is_empty))]
#![cfg_attr(feature = "exclusive_range_pattern", feature(exclusive_range_pattern))]
#![cfg_attr(feature = "extend_one", feature(extend_one))]
#![cfg_attr(
    feature = "hasher_prefixfree_extras",
    feature(hasher_prefixfree_extras)
)]
#![cfg_attr(feature = "map_try_insert", feature(map_try_insert))]
#![cfg_attr(feature = "maybe_uninit_slice", feature(maybe_uninit_slice))]
#![cfg_attr(feature = "new_uninit", feature(new_uninit))]
#![cfg_attr(feature = "rustc_attrs", feature(rustc_attrs))]
#![cfg_attr(feature = "slice_ptr_get", feature(slice_ptr_get))]
#![cfg_attr(feature = "specialization", feature(specialization))]
#![cfg_attr(feature = "type_alias_impl_trait", feature(type_alias_impl_trait))]
// documentation controls
#![cfg_attr(docsrs, feature(doc_auto_cfg, doc_cfg))]
#![deny(missing_docs)]
// linting controls
#![allow(clippy::type_complexity)]
#![cfg_attr(feature = "specialization", allow(incomplete_features))]

extern crate alloc;

use cfg_if::cfg_if;
use core::{borrow::Borrow, cmp::Ordering};

#[macro_use]
mod polyfill;

// port of stdlib implementation
#[allow(missing_docs)]
mod btree;
pub use btree::{map, set};
pub use map::BTreeMap;
pub use set::BTreeSet;

mod std_ord {
    use cfg_if::cfg_if;
    use core::cmp::{Ord as StdOrd, Ordering};

    // This trait and its associated type are deliberately named to conflict with
    // the `Ord::cmp` function so that the generated documentation for the [`CmpFn<T>`]
    // type alias more naturally fits with how one might expect to name a function item
    // type.
    pub trait Ord: StdOrd {
        #[allow(non_camel_case_types)]
        type cmp: Copy + Fn(&Self, &Self) -> Ordering;
        fn cmp_fn() -> Self::cmp;
    }

    impl<O: ?Sized + StdOrd> Ord for O {
        cfg_if! {
            if #[cfg(feature = "type_alias_impl_trait")] {
                // With the TAIT feature, we can obtain the (otherwise anonymous)
                // true (zero-sized) function item type.
                type cmp = impl Copy + Fn(&Self, &Self) -> Ordering;
            } else {
                // Otherwise, we just use a function pointer (with ensuing storage)
                // and indirect call implications.
                type cmp = fn(&Self, &Self) -> Ordering;
            }
        }

        fn cmp_fn() -> Self::cmp {
            Self::cmp
        }
    }

    /// Alias for the type of the `<T as Ord>::cmp` function.
    ///
    /// Note that, unless the `type_alias_impl_trait` feature is enabled, this is
    /// just the relevant function pointer type (and therefore is not zero-sized).
    /// However, with that (unstable) feature enabled, this is an alias for the
    /// actual zero-sized function item type.
    pub type CmpFn<T> = <T as Ord>::cmp;
}

pub use std_ord::CmpFn;

/// Alias for the `Ord::cmp` function of `K::State`.
pub type MinCmpFn<K> = CmpFn<<K as Sortable>::State>;

/// A comparator defines a total order over its type parameter `T`.
pub trait Comparator<T: ?Sized> {
    /// Compare two values and return their relative positions
    /// according to the total order defined by this comparator.
    fn cmp(&self, this: &T, that: &T) -> Ordering;
}

// Blanket `Comparator` implementation for all suitable functions and closures
impl<T: ?Sized, F: Fn(&T, &T) -> Ordering> Comparator<T> for F {
    fn cmp(&self, this: &T, that: &T) -> Ordering {
        self(this, that)
    }
}

/// A sortable type.  See the [crate's documentation][crate] for details.
pub trait Sortable: Borrow<Self::State> {
    /// A type that can be borrowed from `Self` and which contains all state necessary
    /// for sorting.
    type State: ?Sized;
}

///////// `Sortable` implementations for standard library types /////////

macro_rules! minimals {
    // end of recursion
    () => {};

    // implement type and recurse
    ($(#[$attrs:meta])* $({$($g:tt)+})? $t:ty => $m:ty $(, $($rest:tt)*)?) => {
        $(#[$attrs])*
        impl$(<$($g)+>)? Sortable for $t {
            type State = $m;
        }

        $(minimals!($($rest)*);)?
    };

    // delegate to a reflexive implementation if no State is specified
    ($(#[$attrs:meta])* $({$($g:tt)+})? $t:ty $(, $($rest:tt)*)?) => {
        minimals!($(#[$attrs])* $({$($g)+})? $t => Self $(, $($rest)*)?);
    };
}

minimals! {
    (),
    bool, char,
    f32, f64,
    i8, u8,
    i16, u16,
    i32, u32,
    i64, u64,
    i128, u128,
    isize, usize,
    alloc::string::String => str,
    alloc::ffi::CString => core::ffi::CStr,
    {B: ?Sized + Clone} alloc::borrow::Cow<'_, B> => B,
    {T: ?Sized} &T => T,
    {T: ?Sized} &mut T => T,
    {T: ?Sized} alloc::rc::Rc<T> => T,
    {T: ?Sized} alloc::sync::Arc<T> => T,
    {T, const N: usize} [T; N] => [T],
    #[cfg(feature = "std")] std::ffi::OsString => std::ffi::OsStr,
    #[cfg(feature = "std")] std::path::PathBuf => std::path::Path,
}

cfg_if! {
    if #[cfg(feature = "allocator_api")] {
        minimals! {
            {T, A: alloc::alloc::Allocator} alloc::vec::Vec<T, A> => [T],
            {T: ?Sized, A: alloc::alloc::Allocator} alloc::boxed::Box<T, A> => T,
        }
    } else {
        minimals! {
            {T} alloc::vec::Vec<T> => [T],
            {T: ?Sized} alloc::boxed::Box<T> => T,
        }
    }
}
