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


#![allow(clippy::type_complexity)]
#![cfg_attr(docsrs, feature(doc_auto_cfg, doc_cfg))] 
#![cfg_attr(not(any(feature = "std", test)), no_std)]
#![cfg_attr(feature = "specialization", allow(incomplete_features))]
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

extern crate alloc;

use alloc::{borrow::Cow, boxed::Box, ffi::CString, rc::Rc, string::String, sync::Arc, vec::Vec};
use cfg_if::cfg_if;
use core::{borrow::Borrow, ffi::CStr, cmp::Ordering};

mod btree;
pub use btree::{*, map::BTreeMap, set::BTreeSet};

cfg_if! {
    if #[cfg(feature = "allocator_api")] {
        use alloc::alloc::{Allocator, Global};
    } else {
        mod mock_alloc {
            use alloc::alloc::Layout;
            use core::ptr::NonNull;

            pub trait Allocator {
                #[inline]
                fn allocate(&self, layout: Layout) -> Result<NonNull<[u8]>, ()> {
                    unsafe {
                        let len = layout.size();
                        let data = if len == 0 {
                            // SAFETY: align is guaranteed to be non-zero
                            layout.align() as _
                        } else {
                            // SAFETY: `layout` is non-zero in size,
                            NonNull::new(alloc::alloc::alloc(layout)).ok_or(())?.as_ptr()
                        };
                        Ok(NonNull::new_unchecked(core::ptr::slice_from_raw_parts_mut(
                            data, len,
                        )))
                    }
                }

                #[inline]
                unsafe fn deallocate(&self, ptr: NonNull<u8>, layout: Layout) {
                    if layout.size() != 0 {
                        // SAFETY: `layout` is non-zero in size,
                        // other conditions must be upheld by the caller
                        unsafe { alloc::alloc::dealloc(ptr.as_ptr(), layout) }
                    }
                }
            }

            #[derive(Copy, Clone, Debug)]
            pub struct Global;

            impl Allocator for Global {}
        }

        use mock_alloc::{Allocator, Global};
    }
}

/// A sortable type.  See the [crate's documentation][crate] for details.
pub trait Sortable: Borrow<Self::State> {
    /// A type that can be borrowed from `Self` and which contains all state necessary
    /// for sorting.
    type State: ?Sized;
}

mod std_ord {
    use cfg_if::cfg_if;
    use core::cmp::Ordering;

    pub trait StdOrd: Ord {
        #[allow(non_camel_case_types)]
        type cmp: Copy + Fn(&Self, &Self) -> Ordering;
        fn cmp_fn() -> Self::cmp;
    }

    impl<O: ?Sized + Ord> StdOrd for O {
        cfg_if! {
            if #[cfg(feature = "type_alias_impl_trait")] {
                type cmp = impl Copy + Fn(&Self, &Self) -> Ordering;
            } else {
                type cmp = fn(&Self, &Self) -> Ordering;
            }
        }

        fn cmp_fn() -> Self::cmp {
            Self::cmp
        }
    }
}

use std_ord::StdOrd;
use StdOrd as Ord;

/// Alias for the type of the `<T as Ord>::cmp` function.
///
/// Note that, unless the `type_alias_impl_trait` feature is enabled, this is
/// just the relevant function pointer type (and therefore is not zero-sized).
/// However, with that (unstable) feature enabled, this is an alias for the
/// actual zero-sized function item type.
pub type CmpFn<T> = <T as Ord>::cmp;

/// Alias for the `Ord::cmp` function of `K::State`.
pub type MinCmpFn<K> = CmpFn<<K as Sortable>::State>;

macro_rules! minimals {
    () => {};

    ($t:ty => $m:ty $(, $($rest:tt)*)?) => {
        impl Sortable for $t {
            type State = $m;
        }

        $(minimals!($($rest)*);)?
    };

    ($t:ty $(, $($rest:tt)*)?) => {
        minimals!($t => Self $(, $($rest)*)?);
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
    String => str,
    CString => CStr,
}

cfg_if! {
    if #[cfg(any(feature = "std"))] {
        use std::{
            ffi::{OsString, OsStr},
            path::{PathBuf, Path},
        };

        #[cfg_attr(docsrs, doc(cfg(feature = "std")))]
        impl Sortable for OsString {
            type State = OsStr;
        }

        #[cfg_attr(docsrs, doc(cfg(feature = "std")))]
        impl Sortable for PathBuf {
            type State = Path;
        }
    }
}

impl<B: ?Sized + Clone> Sortable for Cow<'_, B> {
    type State = B;
}

impl<T: ?Sized> Sortable for &T {
    type State = T;
}

impl<T: ?Sized> Sortable for &mut T {
    type State = T;
}

impl<T: ?Sized> Sortable for Rc<T> {
    type State = T;
}

impl<T: ?Sized> Sortable for Arc<T> {
    type State = T;
}

cfg_if! {
    if #[cfg(feature = "allocator_api")] {
        impl<T, A: Allocator> Sortable for Vec<T, A> {
            type State = [T];
        }

        impl<T: ?Sized, A: Allocator> Sortable for Box<T, A> {
            type State = T;
        }
    } else {
        impl<T> Sortable for Vec<T> {
            type State = [T];
        }

        impl<T: ?Sized> Sortable for Box<T> {
            type State = T;
        }
    }
}

impl<T, const N: usize> Sortable for [T; N] {
    type State = [T];
}

/// A comparator compares two values to determine their relative positions
/// according to the total order that it defines over their type `T`.
pub trait Comparator<T: ?Sized> {
    fn cmp(&self, this: &T, that: &T) -> Ordering;
}

impl<T: ?Sized, F: Fn(&T, &T) -> Ordering> Comparator<T> for F {
    fn cmp(&self, this: &T, that: &T) -> Ordering {
        self(this, that)
    }
}
