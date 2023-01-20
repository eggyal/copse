//! Defaults that enable copse's collections to behave as per those of the standard
//! library, namely using the [`Ord`] trait for comparisons rather than any user-
//! supplied [`TotalOrder`].
//!
//! Use of these defaults negates the purpose of the copse crate, and indicates that
//! you should probably be using the standard library's collections instead.

use crate::{SortableBy, TotalOrder};
use alloc::{boxed::Box, vec::Vec};
use core::{borrow::Borrow, cmp::Ordering, marker::PhantomData};

/// A zero-sized total order that delegates to the [`Ord`] implementation
/// of its type parameter `T`.
pub struct OrdTotalOrder<T: ?Sized + Ord>(PhantomData<fn(&T)>);

impl<T: ?Sized + Ord> Default for OrdTotalOrder<T> {
    fn default() -> Self {
        Self(PhantomData)
    }
}

impl<T: ?Sized + Ord> Clone for OrdTotalOrder<T> {
    fn clone(&self) -> Self {
        Self(PhantomData)
    }
}

impl<T: ?Sized + Ord> Copy for OrdTotalOrder<T> {}

impl<T: ?Sized + Ord> TotalOrder for OrdTotalOrder<T> {
    type OrderedType = T;

    // Delegate to `T`'s implementation of [`Ord`].
    fn cmp(&self, this: &T, that: &T) -> Ordering {
        this.cmp(that)
    }

    // The default implementations of the following methods are overidden so that
    // they delegate to `T`'s implementations of [`PartialEq`] and [`PartialOrd`]
    // rather than merely using its implementation of [`Ord`].
    //
    // If, as required by those traits, `T`'s implementations are consistent with
    // one another, then these overrides will have no effect.  They are provided
    // for (erroneous) cases where the implementations are inconsistent (such as
    // in `liballoc::collections::binary_heap::tests::panic_safe`), thus enabling
    // copse to imitate liballoc with greater fidelity.

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

impl<T: ?Sized + Ord, K: ?Sized + Borrow<T>> SortableBy<OrdTotalOrder<T>> for K {
    fn key(&self) -> &T {
        self.borrow()
    }
}

/// A helper trait implemented on potential storage key types, used to identify their default
/// comparison type for [`Ord`]-based comparisons.
///
/// This is only really used when collections are left to select the default [`OrdTotalOrder`]
/// total order, which essentially converts copse's collections into those already provided by
/// the standard library.  This trait is therefore a convenience, but of relatively little value.
///
/// For example, a collection that stores [`String`] under the default total order will use
/// [`str`] as the comparison type owing to the implementation of this trait for [`String`].
pub trait OrdStoredKey: SortableBy<OrdTotalOrder<Self::DefaultComparisonKey>> {
    /// The comparison type to be used by collections storing keys of `Self` type and using the
    /// default [`OrdTotalOrder`] total order.
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
