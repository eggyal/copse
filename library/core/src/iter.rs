//! Utiilities for working with iterators.

use crate::{cmp::*, polyfill::*};

/// An extension trait for iterators, providing contextual comparisons.
///
/// This extends the standard library's main iterator trait. For more about the
/// concept of iterators generally, please see the [standard libary's documentation].
/// In particular, you may want to know how to [implement `Iterator`][impl].
///
/// [standard libary's documentation]: core::iter
/// [impl]: core::iter#implementing-iterator
pub trait ContextualIterator: Iterator {
    /// Returns the maximum element of an iterator.
    ///
    /// If several elements are equally maximum, the last element is
    /// returned. If the iterator is empty, [`None`] is returned.
    ///
    /// Note that [`f32`]/[`f64`] shouldn't implement [`ContextualOrd`] due to NaN
    /// being incomparable. You can work around this by using [`Iterator::reduce`]:
    /// ```
    /// assert_eq!(
    ///     [2.4, f32::NAN, 1.3]
    ///         .into_iter()
    ///         .reduce(f32::max)
    ///         .unwrap(),
    ///     2.4
    /// );
    /// ```
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// use contextual_core::prelude::*;
    ///
    /// let a = [1, 2, 3];
    /// let b: Vec<u32> = Vec::new();
    ///
    /// assert_eq!(a.iter().contextual_max(&NoContext), Some(&3));
    /// assert_eq!(b.iter().contextual_max(&NoContext), None);
    /// ```
    #[inline]
    fn contextual_max<C>(self, context: &C) -> Option<Self::Item>
    where
        Self: Sized,
        Self::Item: ContextualOrd<C>,
    {
        self.max_by(|a, b| a.contextual_cmp(b, context))
    }

    /// Returns the minimum element of an iterator.
    ///
    /// If several elements are equally minimum, the first element is returned.
    /// If the iterator is empty, [`None`] is returned.
    ///
    /// Note that [`f32`]/[`f64`] shouldn't implement [`ContextualOrd`] due to NaN
    /// being incomparable. You can work around this by using [`Iterator::reduce`]:
    /// ```
    /// assert_eq!(
    ///     [2.4, f32::NAN, 1.3]
    ///         .into_iter()
    ///         .reduce(f32::min)
    ///         .unwrap(),
    ///     1.3
    /// );
    /// ```
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// use contextual_core::prelude::*;
    ///
    /// let a = [1, 2, 3];
    /// let b: Vec<u32> = Vec::new();
    ///
    /// assert_eq!(a.iter().contextual_min(&NoContext), Some(&1));
    /// assert_eq!(b.iter().contextual_min(&NoContext), None);
    /// ```
    #[inline]
    fn contextual_min<C>(self, context: &C) -> Option<Self::Item>
    where
        Self: Sized,
        Self::Item: ContextualOrd<C>,
    {
        self.min_by(|a, b| a.contextual_cmp(b, context))
    }

    /// Returns the element that gives the maximum value from the
    /// specified function.
    ///
    /// If several elements are equally maximum, the last element is
    /// returned. If the iterator is empty, [`None`] is returned.
    ///
    /// # Examples
    ///
    /// ```
    /// use contextual_core::prelude::*;
    ///
    /// let a = [-3_i32, 0, 1, 5, -10];
    /// assert_eq!(*a.iter().contextual_max_by_key(|x| x.abs(), &NoContext).unwrap(), -10);
    /// ```
    #[inline]
    fn contextual_max_by_key<B, F, C>(self, f: F, context: &C) -> Option<Self::Item>
    where
        B: ContextualOrd<C>,
        Self: Sized,
        F: FnMut(&Self::Item) -> B,
    {
        #[inline]
        fn key<T, B>(mut f: impl FnMut(&T) -> B) -> impl FnMut(T) -> (B, T) {
            move |x| (f(&x), x)
        }

        #[inline]
        fn compare<T, B: ContextualOrd<C>, C>(
            (x_p, _): &(B, T),
            (y_p, _): &(B, T),
            context: &C,
        ) -> Ordering {
            x_p.contextual_cmp(y_p, context)
        }

        let (_, x) = self.map(key(f)).max_by(|a, b| compare(a, b, context))?;
        Some(x)
    }

    /// Returns the element that gives the minimum value from the
    /// specified function.
    ///
    /// If several elements are equally minimum, the first element is
    /// returned. If the iterator is empty, [`None`] is returned.
    ///
    /// # Examples
    ///
    /// ```
    /// use contextual_core::prelude::*;
    ///
    /// let a = [-3_i32, 0, 1, 5, -10];
    /// assert_eq!(*a.iter().contextual_min_by_key(|x| x.abs(), &NoContext).unwrap(), 0);
    /// ```
    #[inline]
    fn contextual_min_by_key<B, F, C>(self, f: F, context: &C) -> Option<Self::Item>
    where
        B: ContextualOrd<C>,
        Self: Sized,
        F: FnMut(&Self::Item) -> B,
    {
        #[inline]
        fn key<T, B>(mut f: impl FnMut(&T) -> B) -> impl FnMut(T) -> (B, T) {
            move |x| (f(&x), x)
        }

        #[inline]
        fn compare<T, B: ContextualOrd<C>, C>(
            (x_p, _): &(B, T),
            (y_p, _): &(B, T),
            context: &C,
        ) -> Ordering {
            x_p.contextual_cmp(y_p, context)
        }

        let (_, x) = self.map(key(f)).min_by(|a, b| compare(a, b, context))?;
        Some(x)
    }

    /// [Lexicographically](Ord#lexicographical-comparison) compares the elements of this [`Iterator`] with those
    /// of another.
    ///
    /// # Examples
    ///
    /// ```
    /// use contextual_core::prelude::*;
    /// use std::cmp::Ordering;
    ///
    /// assert_eq!([1].iter().contextual_cmp([1].iter(), &NoContext), Ordering::Equal);
    /// assert_eq!([1].iter().contextual_cmp([1, 2].iter(), &NoContext), Ordering::Less);
    /// assert_eq!([1, 2].iter().contextual_cmp([1].iter(), &NoContext), Ordering::Greater);
    /// ```
    fn contextual_cmp<I, C>(self, other: I, context: &C) -> Ordering
    where
        I: IntoIterator<Item = Self::Item>,
        Self::Item: ContextualOrd<C>,
        Self: Sized,
    {
        #[allow(unstable_name_collisions)]
        self.cmp_by(other, |x, y| x.contextual_cmp(&y, context))
    }

    /// [Lexicographically](Ord#lexicographical-comparison) compares the elements of this [`Iterator`] with those
    /// of another.
    ///
    /// # Examples
    ///
    /// ```
    /// use contextual_core::prelude::*;
    /// use std::cmp::Ordering;
    ///
    /// assert_eq!([1.].iter().contextual_partial_cmp([1.].iter(), &NoContext), Some(Ordering::Equal));
    /// assert_eq!([1.].iter().contextual_partial_cmp([1., 2.].iter(), &NoContext), Some(Ordering::Less));
    /// assert_eq!([1., 2.].iter().contextual_partial_cmp([1.].iter(), &NoContext), Some(Ordering::Greater));
    ///
    /// assert_eq!([f64::NAN].iter().partial_cmp([1.].iter()), None);
    /// ```
    fn contextual_partial_cmp<I, C>(self, other: I, context: &C) -> Option<Ordering>
    where
        I: IntoIterator,
        Self::Item: ContextualPartialOrd<C, <I as IntoIterator>::Item>,
        Self: Sized,
    {
        #[allow(unstable_name_collisions)]
        self.partial_cmp_by(other, |x, y| x.contextual_partial_cmp(&y, context))
    }

    /// Determines if the elements of this [`Iterator`] are equal to those of
    /// another.
    ///
    /// # Examples
    ///
    /// ```
    /// use contextual_core::prelude::*;
    ///
    /// assert_eq!([1].iter().contextual_eq([1].iter(), &NoContext), true);
    /// assert_eq!([1].iter().contextual_eq([1, 2].iter(), &NoContext), false);
    /// ```
    fn contextual_eq<I, C>(self, other: I, context: &C) -> bool
    where
        I: IntoIterator,
        Self::Item: ContextualPartialEq<C, <I as IntoIterator>::Item>,
        Self: Sized,
    {
        #[allow(unstable_name_collisions)]
        self.eq_by(other, |x, y| x.contextual_eq(&y, context))
    }

    /// Determines if the elements of this [`Iterator`] are unequal to those of
    /// another.
    ///
    /// # Examples
    ///
    /// ```
    /// use contextual_core::prelude::*;
    ///
    /// assert_eq!([1].iter().contextual_ne([1].iter(), &NoContext), false);
    /// assert_eq!([1].iter().contextual_ne([1, 2].iter(), &NoContext), true);
    /// ```
    fn contextual_ne<I, C>(self, other: I, context: &C) -> bool
    where
        I: IntoIterator,
        Self::Item: ContextualPartialOrd<C, <I as IntoIterator>::Item>,
        Self: Sized,
    {
        !self.contextual_eq(other, context)
    }

    /// Determines if the elements of this [`Iterator`] are [lexicographically](Ord#lexicographical-comparison)
    /// less than those of another.
    ///
    /// # Examples
    ///
    /// ```
    /// use contextual_core::prelude::*;
    ///
    /// assert_eq!([1].iter().contextual_lt([1].iter(), &NoContext), false);
    /// assert_eq!([1].iter().contextual_lt([1, 2].iter(), &NoContext), true);
    /// assert_eq!([1, 2].iter().contextual_lt([1].iter(), &NoContext), false);
    /// assert_eq!([1, 2].iter().contextual_lt([1, 2].iter(), &NoContext), false);
    /// ```
    fn contextual_lt<I, C>(self, other: I, context: &C) -> bool
    where
        I: IntoIterator,
        Self::Item: ContextualPartialOrd<C, <I as IntoIterator>::Item>,
        Self: Sized,
    {
        self.contextual_partial_cmp(other, context) == Some(Ordering::Less)
    }

    /// Determines if the elements of this [`Iterator`] are [lexicographically](Ord#lexicographical-comparison)
    /// less or equal to those of another.
    ///
    /// # Examples
    ///
    /// ```
    /// use contextual_core::prelude::*;
    ///
    /// assert_eq!([1].iter().contextual_le([1].iter(), &NoContext), true);
    /// assert_eq!([1].iter().contextual_le([1, 2].iter(), &NoContext), true);
    /// assert_eq!([1, 2].iter().contextual_le([1].iter(), &NoContext), false);
    /// assert_eq!([1, 2].iter().contextual_le([1, 2].iter(), &NoContext), true);
    /// ```
    fn contextual_le<I, C>(self, other: I, context: &C) -> bool
    where
        I: IntoIterator,
        Self::Item: ContextualPartialOrd<C, <I as IntoIterator>::Item>,
        Self: Sized,
    {
        matches!(
            self.contextual_partial_cmp(other, context),
            Some(Ordering::Less | Ordering::Equal)
        )
    }

    /// Determines if the elements of this [`Iterator`] are [lexicographically](Ord#lexicographical-comparison)
    /// greater than those of another.
    ///
    /// # Examples
    ///
    /// ```
    /// use contextual_core::prelude::*;
    ///
    /// assert_eq!([1].iter().contextual_gt([1].iter(), &NoContext), false);
    /// assert_eq!([1].iter().contextual_gt([1, 2].iter(), &NoContext), false);
    /// assert_eq!([1, 2].iter().contextual_gt([1].iter(), &NoContext), true);
    /// assert_eq!([1, 2].iter().contextual_gt([1, 2].iter(), &NoContext), false);
    /// ```
    fn contextual_gt<I, C>(self, other: I, context: &C) -> bool
    where
        I: IntoIterator,
        Self::Item: ContextualPartialOrd<C, <I as IntoIterator>::Item>,
        Self: Sized,
    {
        self.contextual_partial_cmp(other, context) == Some(Ordering::Greater)
    }

    /// Determines if the elements of this [`Iterator`] are [lexicographically](Ord#lexicographical-comparison)
    /// greater than or equal to those of another.
    ///
    /// # Examples
    ///
    /// ```
    /// use contextual_core::prelude::*;
    ///
    /// assert_eq!([1].iter().contextual_ge([1].iter(), &NoContext), true);
    /// assert_eq!([1].iter().contextual_ge([1, 2].iter(), &NoContext), false);
    /// assert_eq!([1, 2].iter().contextual_ge([1].iter(), &NoContext), true);
    /// assert_eq!([1, 2].iter().contextual_ge([1, 2].iter(), &NoContext), true);
    /// ```
    fn contextual_ge<I, C>(self, other: I, context: &C) -> bool
    where
        I: IntoIterator,
        Self::Item: ContextualPartialOrd<C, <I as IntoIterator>::Item>,
        Self: Sized,
    {
        matches!(
            self.contextual_partial_cmp(other, context),
            Some(Ordering::Greater | Ordering::Equal)
        )
    }

    /// Checks if the elements of this iterator are sorted.
    ///
    /// That is, for each element `a` and its following element `b`, `a <= b` must hold. If the
    /// iterator yields exactly zero or one element, `true` is returned.
    ///
    /// Note that if `Self::Item` is only `ContextualPartialOrd`, but not `ContextualOrd`, the
    /// above definition implies that this function returns `false` if any two consecutive items
    /// are not comparable.
    ///
    /// # Examples
    ///
    /// ```
    /// use contextual_core::prelude::*;
    ///
    /// assert!([1, 2, 2, 9].iter().contextual_is_sorted(&NoContext));
    /// assert!(![1, 3, 2, 4].iter().contextual_is_sorted(&NoContext));
    /// assert!([0].iter().contextual_is_sorted(&NoContext));
    /// assert!(std::iter::empty::<i32>().contextual_is_sorted(&NoContext));
    /// assert!(![0.0, 1.0, f32::NAN].iter().contextual_is_sorted(&NoContext));
    /// ```
    #[inline]
    #[cfg(feature = "is_sorted")]
    #[allow(clippy::wrong_self_convention)]
    fn contextual_is_sorted<C>(self, context: &C) -> bool
    where
        Self: Sized,
        Self::Item: ContextualPartialOrd<C, Self::Item>,
    {
        #[allow(unstable_name_collisions)]
        self.is_sorted_by(|a, b| a.contextual_partial_cmp(b, context))
    }

    /// Checks if the elements of this iterator are sorted using the given key extraction
    /// function.
    ///
    /// Instead of comparing the iterator's elements directly, this function compares the keys of
    /// the elements, as determined by `f`. Apart from that, it's equivalent to [`contextual_is_sorted`];
    /// see its documentation for more information.
    ///
    /// [`contextual_is_sorted`]: ContextualIterator::contextual_is_sorted
    ///
    /// # Examples
    ///
    /// ```
    /// use contextual_core::prelude::*;
    ///
    /// assert!(["c", "bb", "aaa"].iter().contextual_is_sorted_by_key(|s| s.len(), &NoContext));
    /// assert!(![-2i32, -1, 0, 3].iter().contextual_is_sorted_by_key(|n| n.abs(), &NoContext));
    /// ```
    #[cfg(feature = "is_sorted")]
    #[allow(clippy::wrong_self_convention)]
    fn contextual_is_sorted_by_key<F, K, C>(self, f: F, context: &C) -> bool
    where
        Self: Sized,
        F: FnMut(Self::Item) -> K,
        K: ContextualPartialOrd<C, K>,
    {
        #[allow(unstable_name_collisions)]
        self.map(f).contextual_is_sorted(context)
    }
}

impl<I: Iterator> ContextualIterator for I {}
