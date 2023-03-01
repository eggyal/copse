// This is pretty much entirely stolen from TreeSet, since BTreeMap has an identical interface
// to TreeMap

use alloc::vec::Vec;
use core::cmp::Ordering::{self, Equal, Greater, Less};
use core::cmp::{max, min};
use core::fmt::{self, Debug};
use core::hash::{Hash, Hasher};
use core::iter::{FromIterator, FusedIterator, Peekable};
use core::mem::ManuallyDrop;
use core::ops::{BitAnd, BitOr, BitXor, Deref, DerefMut, RangeBounds, Sub};

use super::map::{BTreeMap, Keys};
use super::merge_iter::MergeIterInner;
use super::set_val::SetValZST;
use super::Recover;

use crate::polyfill::*;
use contextual_core::{borrow::ContextualBorrow, prelude::*};

// FIXME(conventions): implement bounded iterators

/// An ordered set based on a B-Tree.
///
/// See [`BTreeMap`]'s documentation for a detailed discussion of this collection's performance
/// benefits and drawbacks.
///
/// It is a logic error for an item or runtime context to be modified (except via the [`context_mut`]
/// method) in such a way that the item's ordering relative to any other item, as determined by that
/// runtime context, changes while they are in the set. This is normally only possible through the
/// [`context_mut_unchecked`] method, [`Cell`], [`RefCell`], global state, I/O, or unsafe code. The
/// behavior resulting from such a logic error is not specified, but will be encapsulated to the
/// `BTreeSet` that observed the logic error and not result in undefined behavior. This could include
/// panics, incorrect results, aborts, memory leaks, and non-termination.
///
/// Iterators returned by [`BTreeSet::iter`] produce their items in order, and take worst-case
/// logarithmic and amortized constant time per item returned.
///
/// [`context_mut`]: Self::context_mut
/// [`context_mut_unchecked`]: Self::context_mut_unchecked
/// [`Cell`]: core::cell::Cell
/// [`RefCell`]: core::cell::RefCell
///
/// # Examples
///
/// ```
/// use contextual_alloc::collections::BTreeSet;
///
/// // Type inference lets us omit an explicit type signature (which
/// // would be `BTreeSet<&str>` in this example).
/// let mut books = BTreeSet::default();
///
/// // Add some books.
/// books.insert("A Dance With Dragons");
/// books.insert("To Kill a Mockingbird");
/// books.insert("The Odyssey");
/// books.insert("The Great Gatsby");
///
/// // Check for a specific one.
/// if !books.contains("The Winds of Winter") {
///     println!("We have {} books, but The Winds of Winter ain't one.",
///              books.len());
/// }
///
/// // Remove a book.
/// books.remove("The Odyssey");
///
/// // Iterate over everything.
/// for book in &books {
///     println!("{book}");
/// }
/// ```
///
/// A `BTreeSet` with a known list of items can be initialized from an array:
///
/// ```
/// use contextual_alloc::collections::BTreeSet;
///
/// let set = BTreeSet::from([1, 2, 3]);
/// ```
pub struct BTreeSet<T, C = NoContext, A: Allocator + Clone = Global> {
    map: BTreeMap<T, SetValZST, C, A>,
}

impl<T: Hash, C, A: Allocator + Clone> Hash for BTreeSet<T, C, A> {
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.map.hash(state)
    }
}

impl<T: ContextualPartialEq<C>, C: Eq, A: Allocator + Clone> PartialEq for BTreeSet<T, C, A> {
    fn eq(&self, other: &Self) -> bool {
        self.map == other.map
    }
}

impl<T: ContextualEq<C>, C: Eq, A: Allocator + Clone> Eq for BTreeSet<T, C, A> {}

impl<T: ContextualPartialOrd<C>, C: Eq, A: Allocator + Clone> PartialOrd for BTreeSet<T, C, A> {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        self.map.partial_cmp(&other.map)
    }
}

// contextual_alloc::collections::BTreeSet does not impl Ord because there is no relative ordering when self.map.context and other.map.context differ

impl<T: Clone, C: Clone, A: Allocator + Clone> Clone for BTreeSet<T, C, A> {
    fn clone(&self) -> Self {
        BTreeSet { map: self.map.clone() }
    }

    fn clone_from(&mut self, other: &Self) {
        self.map.clone_from(&other.map);
    }
}

/// An iterator over the items of a `BTreeSet`.
///
/// This `struct` is created by the [`iter`] method on [`BTreeSet`].
/// See its documentation for more.
///
/// [`iter`]: BTreeSet::iter
#[must_use = "iterators are lazy and do nothing unless consumed"]
pub struct Iter<'a, T: 'a> {
    iter: Keys<'a, T, SetValZST>,
}

impl<T: fmt::Debug> fmt::Debug for Iter<'_, T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_tuple("Iter").field(&self.iter.clone()).finish()
    }
}

/// An owning iterator over the items of a `BTreeSet`.
///
/// This `struct` is created by the [`into_iter`] method on [`BTreeSet`]
/// (provided by the [`IntoIterator`] trait). See its documentation for more.
///
/// [`into_iter`]: BTreeSet#method.into_iter
/// [`IntoIterator`]: core::iter::IntoIterator
#[derive(Debug)]
pub struct IntoIter<T, A: Allocator + Clone = Global> {
    iter: super::map::IntoIter<T, SetValZST, A>,
}

/// An iterator over a sub-range of items in a `BTreeSet`.
///
/// This `struct` is created by the [`range`] method on [`BTreeSet`].
/// See its documentation for more.
///
/// [`range`]: BTreeSet::range
#[must_use = "iterators are lazy and do nothing unless consumed"]
#[derive(Debug)]
pub struct Range<'a, T: 'a> {
    iter: super::map::Range<'a, T, SetValZST>,
}

/// A lazy iterator producing elements in the difference of `BTreeSet`s.
///
/// This `struct` is created by the [`difference`] method on [`BTreeSet`].
/// See its documentation for more.
///
/// [`difference`]: BTreeSet::difference
#[must_use = "this returns the difference as an iterator, \
              without modifying either input set"]
pub struct Difference<'a, T: 'a, C = NoContext, A: Allocator + Clone = Global> {
    inner: DifferenceInner<'a, T, C, A>,
    context: &'a C,
}
enum DifferenceInner<'a, T: 'a, C, A: Allocator + Clone> {
    Stitch {
        // iterate all of `self` and some of `other`, spotting matches along the way
        self_iter: Iter<'a, T>,
        other_iter: Peekable<Iter<'a, T>>,
    },
    Search {
        // iterate `self`, look up in `other`
        self_iter: Iter<'a, T>,
        other_set: &'a BTreeSet<T, C, A>,
    },
    Iterate(Iter<'a, T>), // simply produce all elements in `self`
}

// Explicit Debug impl necessary because of issue #26925
impl<T: Debug, C, A: Allocator + Clone> Debug for DifferenceInner<'_, T, C, A> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            DifferenceInner::Stitch { self_iter, other_iter } => f
                .debug_struct("Stitch")
                .field("self_iter", self_iter)
                .field("other_iter", other_iter)
                .finish(),
            DifferenceInner::Search { self_iter, other_set } => f
                .debug_struct("Search")
                .field("self_iter", self_iter)
                .field("other_iter", other_set)
                .finish(),
            DifferenceInner::Iterate(x) => f.debug_tuple("Iterate").field(x).finish(),
        }
    }
}

impl<T: fmt::Debug, C, A: Allocator + Clone> fmt::Debug for Difference<'_, T, C, A> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_tuple("Difference").field(&self.inner).finish()
    }
}

/// A lazy iterator producing elements in the symmetric difference of `BTreeSet`s.
///
/// This `struct` is created by the [`symmetric_difference`] method on
/// [`BTreeSet`]. See its documentation for more.
///
/// [`symmetric_difference`]: BTreeSet::symmetric_difference
#[must_use = "this returns the difference as an iterator, \
              without modifying either input set"]
pub struct SymmetricDifference<'a, T: 'a, C = NoContext>(MergeIterInner<Iter<'a, T>>, &'a C);

impl<T: fmt::Debug, C> fmt::Debug for SymmetricDifference<'_, T, C> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_tuple("SymmetricDifference").field(&self.0).finish()
    }
}

/// A lazy iterator producing elements in the intersection of `BTreeSet`s.
///
/// This `struct` is created by the [`intersection`] method on [`BTreeSet`].
/// See its documentation for more.
///
/// [`intersection`]: BTreeSet::intersection
#[must_use = "this returns the intersection as an iterator, \
              without modifying either input set"]
pub struct Intersection<'a, T: 'a, C = NoContext, A: Allocator + Clone = Global> {
    inner: IntersectionInner<'a, T, C, A>,
    context: &'a C,
}
enum IntersectionInner<'a, T: 'a, C, A: Allocator + Clone> {
    Stitch {
        // iterate similarly sized sets jointly, spotting matches along the way
        a: Iter<'a, T>,
        b: Iter<'a, T>,
    },
    Search {
        // iterate a small set, look up in the large set
        small_iter: Iter<'a, T>,
        large_set: &'a BTreeSet<T, C, A>,
    },
    Answer(Option<&'a T>), // return a specific element or emptiness
}

// Explicit Debug impl necessary because of issue #26925
impl<T: Debug, C, A: Allocator + Clone> Debug for IntersectionInner<'_, T, C, A> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            IntersectionInner::Stitch { a, b } => {
                f.debug_struct("Stitch").field("a", a).field("b", b).finish()
            }
            IntersectionInner::Search { small_iter, large_set } => f
                .debug_struct("Search")
                .field("small_iter", small_iter)
                .field("large_set", large_set)
                .finish(),
            IntersectionInner::Answer(x) => f.debug_tuple("Answer").field(x).finish(),
        }
    }
}

impl<T: Debug, C, A: Allocator + Clone> Debug for Intersection<'_, T, C, A> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_tuple("Intersection").field(&self.inner).finish()
    }
}

/// A lazy iterator producing elements in the union of `BTreeSet`s.
///
/// This `struct` is created by the [`union`] method on [`BTreeSet`].
/// See its documentation for more.
///
/// [`union`]: BTreeSet::union
#[must_use = "this returns the union as an iterator, \
              without modifying either input set"]
pub struct Union<'a, T: 'a, C = NoContext>(MergeIterInner<Iter<'a, T>>, &'a C);

impl<T: fmt::Debug, C> fmt::Debug for Union<'_, T, C> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_tuple("Union").field(&self.0).finish()
    }
}

// This constant is used by functions that compare two sets.
// It estimates the relative size at which searching performs better
// than iterating, based on the benchmarks in
// https://github.com/ssomers/rust_bench_btreeset_intersection.
// It's used to divide rather than multiply sizes, to rule out overflow,
// and it's a power of two to make that division cheap.
const ITER_PERFORMANCE_TIPPING_SIZE_DIFF: usize = 16;

impl<T, C> BTreeSet<T, C> {
    /// Makes a new, empty `BTreeSet` ordered by the given `context`.
    ///
    /// Does not allocate anything on its own.
    ///
    /// # Examples
    ///
    /// ```
    /// use contextual_alloc::{collections::BTreeSet, contextual_core::contextual};
    ///
    /// // define a runtime context
    /// struct OrderByNthByte {
    ///     n: usize, // runtime state
    /// }
    ///
    /// contextual! {
    ///     fn cmp(&self, other: &[u8], context: &OrderByNthByte) -> Ordering {
    ///         self.get(context.n).cmp(&other.get(context.n))
    ///     }
    ///     fn borrow(self: &str, _: &OrderByNthByte) -> &[u8], delegating cmp { self.as_bytes() }
    ///     fn borrow(self: &String, _: &OrderByNthByte) -> &str, delegating cmp { self }
    /// }
    ///
    /// // create a set using our runtime context
    /// let mut set = BTreeSet::new(OrderByNthByte { n: 9 });
    ///
    /// // entries can now be inserted into the empty set
    /// assert!(set.insert("abcdefghij".to_string()));
    /// ```
    #[must_use]
    pub const fn new(context: C) -> BTreeSet<T, C> {
        BTreeSet { map: BTreeMap::new(context) }
    }
}

impl<T, C, A: Allocator + Clone> BTreeSet<T, C, A> {
    decorate_if! {
        if #[cfg(feature = "btreemap_alloc")] {
            /// Makes a new `BTreeSet` with a reasonable choice of B ordered by the given `context`.
            ///
            /// # Examples
            ///
            /// Basic usage:
            ///
            /// ```
            /// # #![feature(allocator_api)]
            /// use contextual_alloc::{collections::BTreeSet, contextual_core::NoContext};
            /// use std::alloc::Global;
            ///
            /// let mut set = BTreeSet::<_>::new_in(NoContext::default(), Global);
            ///
            /// // entries can now be inserted into the empty set
            /// set.insert("a".to_string());
            /// ```
            pub
        }
        fn new_in(context: C, alloc: A) -> BTreeSet<T, C, A> {
            BTreeSet { map: BTreeMap::new_in(context, alloc) }
        }
    }

    /// Constructs a double-ended iterator over a sub-range of elements in the set.
    /// The simplest way is to use the range syntax `min..max`, thus `range(min..max)` will
    /// yield elements from min (inclusive) to max (exclusive).
    /// The range may also be entered as `(Bound<T>, Bound<T>)`, so for example
    /// `range((Excluded(4), Included(10)))` will yield a left-exclusive, right-inclusive
    /// range from 4 to 10.
    ///
    /// # Panics
    ///
    /// Panics if range `start > end`.
    /// Panics if range `start == end` and both bounds are `Excluded`.
    ///
    /// # Examples
    ///
    /// ```
    /// use contextual_alloc::collections::BTreeSet;
    /// use std::ops::Bound::Included;
    ///
    /// let mut set = BTreeSet::default();
    /// set.insert(3);
    /// set.insert(5);
    /// set.insert(8);
    /// for &elem in set.range::<i32, _>((Included(&4), Included(&8))) {
    ///     println!("{elem}");
    /// }
    /// assert_eq!(Some(&5), set.range(4..).next());
    /// ```
    pub fn range<K: ?Sized, R>(&self, range: R) -> Range<'_, T>
    where
        K: ContextualOrd<C>,
        T: ContextualOrd<C> + ContextualBorrow<K, C>,
        R: RangeBounds<K>,
    {
        Range { iter: self.map.range(range) }
    }

    /// Visits the elements representing the difference,
    /// i.e., the elements that are in `self` but not in `other`,
    /// in ascending order.
    ///
    /// # Examples
    ///
    /// ```
    /// use contextual_alloc::collections::BTreeSet;
    ///
    /// let mut a = BTreeSet::default();
    /// a.insert(1);
    /// a.insert(2);
    ///
    /// let mut b = BTreeSet::default();
    /// b.insert(2);
    /// b.insert(3);
    ///
    /// let diff: Vec<_> = a.difference(&b).cloned().collect();
    /// assert_eq!(diff, [1]);
    /// ```
    pub fn difference<'a>(&'a self, other: &'a BTreeSet<T, C, A>) -> Difference<'a, T, C, A>
    where
        T: ContextualOrd<C>,
    {
        let (self_min, self_max) =
            if let (Some(self_min), Some(self_max)) = (self.first(), self.last()) {
                (self_min, self_max)
            } else {
                return Difference {
                    inner: DifferenceInner::Iterate(self.iter()),
                    context: &self.map.context,
                };
            };
        let (other_min, other_max) =
            if let (Some(other_min), Some(other_max)) = (other.first(), other.last()) {
                (other_min, other_max)
            } else {
                return Difference {
                    inner: DifferenceInner::Iterate(self.iter()),
                    context: &self.map.context,
                };
            };
        Difference {
            inner: match (
                self_min.contextual_cmp(other_max, &self.map.context),
                self_max.contextual_cmp(other_min, &self.map.context),
            ) {
                (Greater, _) | (_, Less) => DifferenceInner::Iterate(self.iter()),
                (Equal, _) => {
                    let mut self_iter = self.iter();
                    self_iter.next();
                    DifferenceInner::Iterate(self_iter)
                }
                (_, Equal) => {
                    let mut self_iter = self.iter();
                    self_iter.next_back();
                    DifferenceInner::Iterate(self_iter)
                }
                _ if self.len() <= other.len() / ITER_PERFORMANCE_TIPPING_SIZE_DIFF => {
                    DifferenceInner::Search { self_iter: self.iter(), other_set: other }
                }
                _ => DifferenceInner::Stitch {
                    self_iter: self.iter(),
                    other_iter: other.iter().peekable(),
                },
            },
            context: &self.map.context,
        }
    }

    /// Visits the elements representing the symmetric difference,
    /// i.e., the elements that are in `self` or in `other` but not in both,
    /// in ascending order.
    ///
    /// # Examples
    ///
    /// ```
    /// use contextual_alloc::collections::BTreeSet;
    ///
    /// let mut a = BTreeSet::default();
    /// a.insert(1);
    /// a.insert(2);
    ///
    /// let mut b = BTreeSet::default();
    /// b.insert(2);
    /// b.insert(3);
    ///
    /// let sym_diff: Vec<_> = a.symmetric_difference(&b).cloned().collect();
    /// assert_eq!(sym_diff, [1, 3]);
    /// ```
    pub fn symmetric_difference<'a>(
        &'a self,
        other: &'a BTreeSet<T, C, A>,
    ) -> SymmetricDifference<'a, T, C>
    where
        T: ContextualOrd<C>,
    {
        SymmetricDifference(MergeIterInner::new(self.iter(), other.iter()), &self.map.context)
    }

    /// Visits the elements representing the intersection,
    /// i.e., the elements that are both in `self` and `other`,
    /// in ascending order.
    ///
    /// # Examples
    ///
    /// ```
    /// use contextual_alloc::collections::BTreeSet;
    ///
    /// let mut a = BTreeSet::default();
    /// a.insert(1);
    /// a.insert(2);
    ///
    /// let mut b = BTreeSet::default();
    /// b.insert(2);
    /// b.insert(3);
    ///
    /// let intersection: Vec<_> = a.intersection(&b).cloned().collect();
    /// assert_eq!(intersection, [2]);
    /// ```
    pub fn intersection<'a>(&'a self, other: &'a BTreeSet<T, C, A>) -> Intersection<'a, T, C, A>
    where
        T: ContextualOrd<C>,
    {
        let (self_min, self_max) =
            if let (Some(self_min), Some(self_max)) = (self.first(), self.last()) {
                (self_min, self_max)
            } else {
                return Intersection {
                    inner: IntersectionInner::Answer(None),
                    context: &self.map.context,
                };
            };
        let (other_min, other_max) =
            if let (Some(other_min), Some(other_max)) = (other.first(), other.last()) {
                (other_min, other_max)
            } else {
                return Intersection {
                    inner: IntersectionInner::Answer(None),
                    context: &self.map.context,
                };
            };
        Intersection {
            inner: match (
                self_min.contextual_cmp(other_max, &self.map.context),
                self_max.contextual_cmp(other_min, &self.map.context),
            ) {
                (Greater, _) | (_, Less) => IntersectionInner::Answer(None),
                (Equal, _) => IntersectionInner::Answer(Some(self_min)),
                (_, Equal) => IntersectionInner::Answer(Some(self_max)),
                _ if self.len() <= other.len() / ITER_PERFORMANCE_TIPPING_SIZE_DIFF => {
                    IntersectionInner::Search { small_iter: self.iter(), large_set: other }
                }
                _ if other.len() <= self.len() / ITER_PERFORMANCE_TIPPING_SIZE_DIFF => {
                    IntersectionInner::Search { small_iter: other.iter(), large_set: self }
                }
                _ => IntersectionInner::Stitch { a: self.iter(), b: other.iter() },
            },
            context: &self.map.context,
        }
    }

    /// Visits the elements representing the union,
    /// i.e., all the elements in `self` or `other`, without duplicates,
    /// in ascending order.
    ///
    /// # Examples
    ///
    /// ```
    /// use contextual_alloc::collections::BTreeSet;
    ///
    /// let mut a = BTreeSet::default();
    /// a.insert(1);
    ///
    /// let mut b = BTreeSet::default();
    /// b.insert(2);
    ///
    /// let union: Vec<_> = a.union(&b).cloned().collect();
    /// assert_eq!(union, [1, 2]);
    /// ```
    pub fn union<'a>(&'a self, other: &'a BTreeSet<T, C, A>) -> Union<'a, T, C>
    where
        T: ContextualOrd<C>,
    {
        Union(MergeIterInner::new(self.iter(), other.iter()), &self.map.context)
    }

    /// Clears the set, removing all elements.
    ///
    /// # Examples
    ///
    /// ```
    /// use contextual_alloc::collections::BTreeSet;
    ///
    /// let mut v = BTreeSet::default();
    /// v.insert(1);
    /// v.clear();
    /// assert!(v.is_empty());
    /// ```
    pub fn clear(&mut self)
    where
        A: Clone,
        C: Clone,
    {
        self.map.clear()
    }

    /// Returns `true` if the set contains an element equal to the value.
    ///
    /// The value may be any borrowed form of the set's element type,
    /// but the ordering on the borrowed form *must* match the
    /// ordering on the element type.
    ///
    /// # Examples
    ///
    /// ```
    /// use contextual_alloc::collections::BTreeSet;
    ///
    /// let set = BTreeSet::from([1, 2, 3]);
    /// assert_eq!(set.contains(&1), true);
    /// assert_eq!(set.contains(&4), false);
    /// ```
    pub fn contains<Q: ?Sized>(&self, value: &Q) -> bool
    where
        T: ContextualOrd<C> + ContextualBorrow<Q, C>,
        Q: ContextualOrd<C>,
    {
        self.map.contains_key(value)
    }

    /// Returns a reference to the element in the set, if any, that is equal to
    /// the value.
    ///
    /// The value may be any borrowed form of the set's element type,
    /// but the ordering on the borrowed form *must* match the
    /// ordering on the element type.
    ///
    /// # Examples
    ///
    /// ```
    /// use contextual_alloc::collections::BTreeSet;
    ///
    /// let set = BTreeSet::from([1, 2, 3]);
    /// assert_eq!(set.get(&2), Some(&2));
    /// assert_eq!(set.get(&4), None);
    /// ```
    pub fn get<Q: ?Sized>(&self, value: &Q) -> Option<&T>
    where
        T: ContextualOrd<C> + ContextualBorrow<T, C> + ContextualBorrow<Q, C>,
        Q: ContextualOrd<C>,
    {
        Recover::get(&self.map, value)
    }

    /// Returns `true` if `self` has no elements in common with `other`.
    /// This is equivalent to checking for an empty intersection.
    ///
    /// # Examples
    ///
    /// ```
    /// use contextual_alloc::collections::BTreeSet;
    ///
    /// let a = BTreeSet::from([1, 2, 3]);
    /// let mut b = BTreeSet::default();
    ///
    /// assert_eq!(a.is_disjoint(&b), true);
    /// b.insert(4);
    /// assert_eq!(a.is_disjoint(&b), true);
    /// b.insert(1);
    /// assert_eq!(a.is_disjoint(&b), false);
    /// ```
    #[must_use]
    pub fn is_disjoint(&self, other: &BTreeSet<T, C, A>) -> bool
    where
        T: ContextualBorrow<T, C> + ContextualOrd<C>,
    {
        self.intersection(other).next().is_none()
    }

    /// Returns `true` if the set is a subset of another,
    /// i.e., `other` contains at least all the elements in `self`.
    ///
    /// # Examples
    ///
    /// ```
    /// use contextual_alloc::collections::BTreeSet;
    ///
    /// let sup = BTreeSet::from([1, 2, 3]);
    /// let mut set = BTreeSet::default();
    ///
    /// assert_eq!(set.is_subset(&sup), true);
    /// set.insert(2);
    /// assert_eq!(set.is_subset(&sup), true);
    /// set.insert(4);
    /// assert_eq!(set.is_subset(&sup), false);
    /// ```
    #[must_use]
    pub fn is_subset(&self, other: &BTreeSet<T, C, A>) -> bool
    where
        T: ContextualBorrow<T, C> + ContextualOrd<C>,
    {
        // Same result as self.difference(other).next().is_none()
        // but the code below is faster (hugely in some cases).
        if self.len() > other.len() {
            return false;
        }
        let (self_min, self_max) =
            if let (Some(self_min), Some(self_max)) = (self.first(), self.last()) {
                (self_min, self_max)
            } else {
                return true; // self is empty
            };
        let (other_min, other_max) =
            if let (Some(other_min), Some(other_max)) = (other.first(), other.last()) {
                (other_min, other_max)
            } else {
                return false; // other is empty
            };
        let mut self_iter = self.iter();
        match self_min.contextual_cmp(other_min, &self.map.context) {
            Less => return false,
            Equal => {
                self_iter.next();
            }
            Greater => (),
        }
        match self_max.contextual_cmp(other_max, &self.map.context) {
            Greater => return false,
            Equal => {
                self_iter.next_back();
            }
            Less => (),
        }
        if self_iter.len() <= other.len() / ITER_PERFORMANCE_TIPPING_SIZE_DIFF {
            for next in self_iter {
                if !other.contains(next) {
                    return false;
                }
            }
        } else {
            let mut other_iter = other.iter();
            other_iter.next();
            other_iter.next_back();
            let mut self_next = self_iter.next();
            while let Some(self1) = self_next {
                match other_iter
                    .next()
                    .map_or(Less, |other1| self1.contextual_cmp(other1, &self.map.context))
                {
                    Less => return false,
                    Equal => self_next = self_iter.next(),
                    Greater => (),
                }
            }
        }
        true
    }

    /// Returns `true` if the set is a superset of another,
    /// i.e., `self` contains at least all the elements in `other`.
    ///
    /// # Examples
    ///
    /// ```
    /// use contextual_alloc::collections::BTreeSet;
    ///
    /// let sub = BTreeSet::from([1, 2]);
    /// let mut set = BTreeSet::default();
    ///
    /// assert_eq!(set.is_superset(&sub), false);
    ///
    /// set.insert(0);
    /// set.insert(1);
    /// assert_eq!(set.is_superset(&sub), false);
    ///
    /// set.insert(2);
    /// assert_eq!(set.is_superset(&sub), true);
    /// ```
    #[must_use]
    pub fn is_superset(&self, other: &BTreeSet<T, C, A>) -> bool
    where
        T: ContextualBorrow<T, C> + ContextualOrd<C>,
    {
        other.is_subset(self)
    }

    /// Returns a reference to the first element in the set, if any.
    /// This element is always the minimum of all elements in the set.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// use contextual_alloc::collections::BTreeSet;
    ///
    /// let mut set = BTreeSet::default();
    /// assert_eq!(set.first(), None);
    /// set.insert(1);
    /// assert_eq!(set.first(), Some(&1));
    /// set.insert(2);
    /// assert_eq!(set.first(), Some(&1));
    /// ```
    #[must_use]
    pub fn first(&self) -> Option<&T>
    where
        T: ContextualOrd<C>,
    {
        self.map.first_key_value().map(|(k, _)| k)
    }

    /// Returns a reference to the last element in the set, if any.
    /// This element is always the maximum of all elements in the set.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// use contextual_alloc::collections::BTreeSet;
    ///
    /// let mut set = BTreeSet::default();
    /// assert_eq!(set.last(), None);
    /// set.insert(1);
    /// assert_eq!(set.last(), Some(&1));
    /// set.insert(2);
    /// assert_eq!(set.last(), Some(&2));
    /// ```
    #[must_use]
    pub fn last(&self) -> Option<&T>
    where
        T: ContextualOrd<C>,
    {
        self.map.last_key_value().map(|(k, _)| k)
    }

    /// Removes the first element from the set and returns it, if any.
    /// The first element is always the minimum element in the set.
    ///
    /// # Examples
    ///
    /// ```
    /// use contextual_alloc::collections::BTreeSet;
    ///
    /// let mut set = BTreeSet::default();
    ///
    /// set.insert(1);
    /// while let Some(n) = set.pop_first() {
    ///     assert_eq!(n, 1);
    /// }
    /// assert!(set.is_empty());
    /// ```
    pub fn pop_first(&mut self) -> Option<T>
    where
        T: ContextualOrd<C>,
    {
        self.map.pop_first().map(|kv| kv.0)
    }

    /// Removes the last element from the set and returns it, if any.
    /// The last element is always the maximum element in the set.
    ///
    /// # Examples
    ///
    /// ```
    /// use contextual_alloc::collections::BTreeSet;
    ///
    /// let mut set = BTreeSet::default();
    ///
    /// set.insert(1);
    /// while let Some(n) = set.pop_last() {
    ///     assert_eq!(n, 1);
    /// }
    /// assert!(set.is_empty());
    /// ```
    pub fn pop_last(&mut self) -> Option<T>
    where
        T: ContextualOrd<C>,
    {
        self.map.pop_last().map(|kv| kv.0)
    }

    /// Adds a value to the set.
    ///
    /// Returns whether the value was newly inserted. That is:
    ///
    /// - If the set did not previously contain an equal value, `true` is
    ///   returned.
    /// - If the set already contained an equal value, `false` is returned, and
    ///   the entry is not updated.
    ///
    /// See the [module-level documentation] for more.
    ///
    /// [module-level documentation]: index.html#insert-and-complex-keys
    ///
    /// # Examples
    ///
    /// ```
    /// use contextual_alloc::collections::BTreeSet;
    ///
    /// let mut set = BTreeSet::default();
    ///
    /// assert_eq!(set.insert(2), true);
    /// assert_eq!(set.insert(2), false);
    /// assert_eq!(set.len(), 1);
    /// ```
    pub fn insert(&mut self, value: T) -> bool
    where
        T: ContextualBorrow<T, C> + ContextualOrd<C>,
    {
        self.map.insert(value, SetValZST::default()).is_none()
    }

    /// Adds a value to the set, replacing the existing element, if any, that is
    /// equal to the value. Returns the replaced element.
    ///
    /// # Examples
    ///
    /// ```
    /// use contextual_alloc::collections::BTreeSet;
    ///
    /// let mut set = BTreeSet::default();
    /// set.insert(Vec::<i32>::new());
    ///
    /// assert_eq!(set.get(&[][..]).unwrap().capacity(), 0);
    /// set.replace(Vec::with_capacity(10));
    /// assert_eq!(set.get(&[][..]).unwrap().capacity(), 10);
    /// ```
    pub fn replace(&mut self, value: T) -> Option<T>
    where
        T: ContextualBorrow<T, C> + ContextualOrd<C>,
    {
        Recover::<T>::replace(&mut self.map, value)
    }

    /// If the set contains an element equal to the value, removes it from the
    /// set and drops it. Returns whether such an element was present.
    ///
    /// The value may be any borrowed form of the set's element type,
    /// but the ordering on the borrowed form *must* match the
    /// ordering on the element type.
    ///
    /// # Examples
    ///
    /// ```
    /// use contextual_alloc::collections::BTreeSet;
    ///
    /// let mut set = BTreeSet::default();
    ///
    /// set.insert(2);
    /// assert_eq!(set.remove(&2), true);
    /// assert_eq!(set.remove(&2), false);
    /// ```
    pub fn remove<Q: ?Sized>(&mut self, value: &Q) -> bool
    where
        T: ContextualOrd<C> + ContextualBorrow<Q, C>,
        Q: ContextualOrd<C>,
    {
        self.map.remove(value).is_some()
    }

    /// Removes and returns the element in the set, if any, that is equal to
    /// the value.
    ///
    /// The value may be any borrowed form of the set's element type,
    /// but the ordering on the borrowed form *must* match the
    /// ordering on the element type.
    ///
    /// # Examples
    ///
    /// ```
    /// use contextual_alloc::collections::BTreeSet;
    ///
    /// let mut set = BTreeSet::from([1, 2, 3]);
    /// assert_eq!(set.take(&2), Some(2));
    /// assert_eq!(set.take(&2), None);
    /// ```
    pub fn take<Q: ?Sized>(&mut self, value: &Q) -> Option<T>
    where
        T: ContextualOrd<C> + ContextualBorrow<T, C> + ContextualBorrow<Q, C>,
        Q: ContextualOrd<C>,
    {
        Recover::take(&mut self.map, value)
    }

    /// Retains only the elements specified by the predicate.
    ///
    /// In other words, remove all elements `e` for which `f(&e)` returns `false`.
    /// The elements are visited in ascending order.
    ///
    /// # Examples
    ///
    /// ```
    /// use contextual_alloc::collections::BTreeSet;
    ///
    /// let mut set = BTreeSet::from([1, 2, 3, 4, 5, 6]);
    /// // Keep only the even numbers.
    /// set.retain(|&k| k % 2 == 0);
    /// assert!(set.iter().eq([2, 4, 6].iter()));
    /// ```
    pub fn retain<F>(&mut self, mut f: F)
    where
        T: ContextualOrd<C>,
        F: FnMut(&T) -> bool,
    {
        self.drain_filter(|v| !f(v));
    }

    /// Moves all elements from `other` into `self`, leaving `other` empty.
    ///
    /// # Examples
    ///
    /// ```
    /// use contextual_alloc::collections::BTreeSet;
    ///
    /// let mut a = BTreeSet::default();
    /// a.insert(1);
    /// a.insert(2);
    /// a.insert(3);
    ///
    /// let mut b = BTreeSet::default();
    /// b.insert(3);
    /// b.insert(4);
    /// b.insert(5);
    ///
    /// a.append(&mut b);
    ///
    /// assert_eq!(a.len(), 5);
    /// assert_eq!(b.len(), 0);
    ///
    /// assert!(a.contains(&1));
    /// assert!(a.contains(&2));
    /// assert!(a.contains(&3));
    /// assert!(a.contains(&4));
    /// assert!(a.contains(&5));
    /// ```
    pub fn append(&mut self, other: &mut Self)
    where
        T: ContextualOrd<C>,
        C: Clone,
        A: Clone,
    {
        self.map.append(&mut other.map);
    }

    /// Splits the collection into two at the value. Returns a new collection
    /// with all elements greater than or equal to the value.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// use contextual_alloc::collections::BTreeSet;
    ///
    /// let mut a = BTreeSet::default();
    /// a.insert(1);
    /// a.insert(2);
    /// a.insert(3);
    /// a.insert(17);
    /// a.insert(41);
    ///
    /// let b = a.split_off(&3);
    ///
    /// assert_eq!(a.len(), 2);
    /// assert_eq!(b.len(), 3);
    ///
    /// assert!(a.contains(&1));
    /// assert!(a.contains(&2));
    ///
    /// assert!(b.contains(&3));
    /// assert!(b.contains(&17));
    /// assert!(b.contains(&41));
    /// ```
    pub fn split_off<Q: ?Sized + ContextualOrd<C>>(&mut self, value: &Q) -> Self
    where
        T: ContextualOrd<C> + ContextualBorrow<Q, C>,
        C: Clone,
        A: Clone,
    {
        BTreeSet { map: self.map.split_off(value) }
    }

    decorate_if! {
        if #[cfg(feature = "btree_drain_filter")] {
            /// Creates an iterator that visits all elements in ascending order and
            /// uses a closure to determine if an element should be removed.
            ///
            /// If the closure returns `true`, the element is removed from the set and
            /// yielded. If the closure returns `false`, or panics, the element remains
            /// in the set and will not be yielded.
            ///
            /// If the iterator is only partially consumed or not consumed at all, each
            /// of the remaining elements is still subjected to the closure and removed
            /// and dropped if it returns `true`.
            ///
            /// It is unspecified how many more elements will be subjected to the
            /// closure if a panic occurs in the closure, or if a panic occurs while
            /// dropping an element, or if the `DrainFilter` itself is leaked.
            ///
            /// # Examples
            ///
            /// Splitting a set into even and odd values, reusing the original set:
            ///
            /// ```
            /// use contextual_alloc::collections::BTreeSet;
            ///
            /// let mut set: BTreeSet<i32> = (0..8).collect();
            /// let evens: BTreeSet<_> = set.drain_filter(|v| v % 2 == 0).collect();
            /// let odds = set;
            /// assert_eq!(evens.into_iter().collect::<Vec<_>>(), vec![0, 2, 4, 6]);
            /// assert_eq!(odds.into_iter().collect::<Vec<_>>(), vec![1, 3, 5, 7]);
            /// ```
            pub
        }
        fn drain_filter<'a, F>(&'a mut self, pred: F) -> DrainFilter<'a, T, F, A>
        where
            T: ContextualOrd<C>,
            F: 'a + FnMut(&T) -> bool,
        {
            let (inner, alloc) = self.map.drain_filter_inner();
            DrainFilter { pred, inner, alloc }
        }
    }

    /// Gets an iterator that visits the elements in the `BTreeSet` in ascending
    /// order.
    ///
    /// # Examples
    ///
    /// ```
    /// use contextual_alloc::collections::BTreeSet;
    ///
    /// let set = BTreeSet::from([1, 2, 3]);
    /// let mut set_iter = set.iter();
    /// assert_eq!(set_iter.next(), Some(&1));
    /// assert_eq!(set_iter.next(), Some(&2));
    /// assert_eq!(set_iter.next(), Some(&3));
    /// assert_eq!(set_iter.next(), None);
    /// ```
    ///
    /// Values returned by the iterator are returned in ascending order:
    ///
    /// ```
    /// use contextual_alloc::collections::BTreeSet;
    ///
    /// let set = BTreeSet::from([3, 1, 2]);
    /// let mut set_iter = set.iter();
    /// assert_eq!(set_iter.next(), Some(&1));
    /// assert_eq!(set_iter.next(), Some(&2));
    /// assert_eq!(set_iter.next(), Some(&3));
    /// assert_eq!(set_iter.next(), None);
    /// ```
    pub fn iter(&self) -> Iter<'_, T> {
        Iter { iter: self.map.keys() }
    }

    decorate_if! {
        /// Returns the number of elements in the set.
        ///
        /// # Examples
        ///
        /// ```
        /// use contextual_alloc::collections::BTreeSet;
        ///
        /// let mut v = BTreeSet::default();
        /// assert_eq!(v.len(), 0);
        /// v.insert(1);
        /// assert_eq!(v.len(), 1);
        /// ```
        #[must_use]
        pub
        if #[cfg(feature = "const_btree_len")] { const }
        fn len(&self) -> usize {
            self.map.len()
        }
    }

    decorate_if! {
        /// Returns `true` if the set contains no elements.
        ///
        /// # Examples
        ///
        /// ```
        /// use contextual_alloc::collections::BTreeSet;
        ///
        /// let mut v = BTreeSet::default();
        /// assert!(v.is_empty());
        /// v.insert(1);
        /// assert!(!v.is_empty());
        /// ```
        #[must_use]
        pub
        if #[cfg(feature = "const_btree_len")] { const }
        fn is_empty(&self) -> bool {
            self.len() == 0
        }
    }

    /// Borrow this set's context.
    pub fn context(&self) -> &C {
        self.map.context()
    }

    /// Mutably borrow this set's context.  When the returned guard is dropped, the
    /// set will be rebuilt.
    pub fn context_mut(&mut self) -> ContextMut<'_, T, C, A>
    where
        T: ContextualBorrow<T, C> + ContextualOrd<C>,
    {
        ContextMut(self.map.context_mut())
    }

    /// Mutably borrow this set's context.  It is a logic error for the context to be
    /// modified in a way that changes the relative ordering of any two items contained
    /// in the set.  The behavior resulting from such a logic error is not specified,
    /// but will be encapsulated to the `BTreeSet` that observed the logic error and
    /// not result in undefined behavior. This could include panics, incorrect results,
    /// aborts, memory leaks, and non-termination.
    ///
    /// If the context might be modified in such a way, consider using [`context_mut`]
    /// instead, which will reorder the set once the guard is dropped so as to uphold
    /// its invariants.
    ///
    /// [`context_mut`]: Self::context_mut
    pub fn context_mut_unchecked(&mut self) -> &mut C {
        self.map.context_mut_unchecked()
    }
}

/// A guard for mutably accessing a `BTreeSet`'s context.  When the guard is dropped,
/// the set will be rebuilt.
pub struct ContextMut<'a, T, C = NoContext, A = Global>(
    super::map::ContextMut<'a, T, SetValZST, C, A>,
)
where
    T: ContextualBorrow<T, C> + ContextualOrd<C>,
    A: Allocator + Clone;

impl<K, C, A> Deref for ContextMut<'_, K, C, A>
where
    K: ContextualBorrow<K, C> + ContextualOrd<C>,
    A: Allocator + Clone,
{
    type Target = C;
    fn deref(&self) -> &Self::Target {
        &self.0
    }
}

impl<K, C, A> DerefMut for ContextMut<'_, K, C, A>
where
    K: ContextualBorrow<K, C> + ContextualOrd<C>,
    A: Allocator + Clone,
{
    fn deref_mut(&mut self) -> &mut Self::Target {
        &mut self.0
    }
}

impl<T: ContextualBorrow<T, C> + ContextualOrd<C>, C: Default> FromIterator<T> for BTreeSet<T, C> {
    fn from_iter<I: IntoIterator<Item = T>>(iter: I) -> BTreeSet<T, C> {
        let mut inputs: Vec<_> = iter.into_iter().collect();

        if inputs.is_empty() {
            return BTreeSet::default();
        }

        // use stable sort to preserve the insertion order.
        let context = C::default();
        inputs.sort_by(|a, b| a.contextual_cmp(b, &context));
        BTreeSet::from_sorted_iter(inputs.into_iter(), context, Global)
    }
}

impl<T: ContextualBorrow<T, C> + ContextualOrd<C>, C, A: Allocator + Clone> BTreeSet<T, C, A> {
    fn from_sorted_iter<I: Iterator<Item = T>>(iter: I, context: C, alloc: A) -> BTreeSet<T, C, A> {
        let iter = iter.map(|k| (k, SetValZST::default()));
        let map = BTreeMap::bulk_build_from_sorted_iter(iter, context, alloc);
        BTreeSet { map }
    }
}

impl<T: ContextualOrd<C>, C: Default, const N: usize> From<[T; N]> for BTreeSet<T, C> {
    /// Converts a `[T; N]` into a `BTreeSet<T>`.
    ///
    /// ```
    /// use contextual_alloc::collections::BTreeSet;
    ///
    /// let set1 = BTreeSet::from([1, 2, 3, 4]);
    /// let set2: BTreeSet<_> = [1, 2, 3, 4].into();
    /// assert_eq!(set1, set2);
    /// ```
    fn from(mut arr: [T; N]) -> Self {
        if N == 0 {
            return BTreeSet::default();
        }

        // use stable sort to preserve the insertion order.
        let context = C::default();
        arr.sort_by(|a, b| a.contextual_cmp(b, &context));
        let iter = IntoIterator::into_iter(arr).map(|k| (k, SetValZST::default()));
        let map = BTreeMap::bulk_build_from_sorted_iter(iter, context, Global);
        BTreeSet { map }
    }
}

impl<T, C, A: Allocator + Clone> IntoIterator for BTreeSet<T, C, A> {
    type Item = T;
    type IntoIter = IntoIter<T, A>;

    /// Gets an iterator for moving out the `BTreeSet`'s contents.
    ///
    /// # Examples
    ///
    /// ```
    /// use contextual_alloc::collections::BTreeSet;
    ///
    /// let set = BTreeSet::from([1, 2, 3, 4]);
    ///
    /// let v: Vec<_> = set.into_iter().collect();
    /// assert_eq!(v, [1, 2, 3, 4]);
    /// ```
    fn into_iter(self) -> IntoIter<T, A> {
        IntoIter { iter: self.map.into_iter() }
    }
}

impl<'a, T, C, A: Allocator + Clone> IntoIterator for &'a BTreeSet<T, C, A> {
    type Item = &'a T;
    type IntoIter = Iter<'a, T>;

    fn into_iter(self) -> Iter<'a, T> {
        self.iter()
    }
}

decorate_if! {
    /// An iterator produced by calling `drain_filter` on BTreeSet.
    if #[cfg(feature = "btree_drain_filter")] { pub }
    struct DrainFilter<'a, T, F, A: Allocator + Clone = Global>
    where
        T: 'a,
        F: 'a + FnMut(&T) -> bool,
    {
        pred: F,
        inner: super::map::DrainFilterInner<'a, T, SetValZST>,
        /// The BTreeMap will outlive this IntoIter so we don't care about drop order for `alloc`.
        alloc: A,
    }
}

impl<T, F, A: Allocator + Clone> Drop for DrainFilter<'_, T, F, A>
where
    F: FnMut(&T) -> bool,
{
    fn drop(&mut self) {
        self.for_each(drop);
    }
}

impl<T, F, A: Allocator + Clone> fmt::Debug for DrainFilter<'_, T, F, A>
where
    T: fmt::Debug,
    F: FnMut(&T) -> bool,
{
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_tuple("DrainFilter").field(&self.inner.peek().map(|(k, _)| k)).finish()
    }
}

impl<'a, T, F, A: Allocator + Clone> Iterator for DrainFilter<'_, T, F, A>
where
    F: 'a + FnMut(&T) -> bool,
{
    type Item = T;

    fn next(&mut self) -> Option<T> {
        let pred = &mut self.pred;
        let mut mapped_pred = |k: &T, _v: &mut SetValZST| pred(k);
        self.inner.next(&mut mapped_pred, self.alloc.clone()).map(|(k, _)| k)
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        self.inner.size_hint()
    }
}

impl<T, F, A: Allocator + Clone> FusedIterator for DrainFilter<'_, T, F, A> where
    F: FnMut(&T) -> bool
{
}

impl<T: ContextualBorrow<T, C> + ContextualOrd<C>, C, A: Allocator + Clone> Extend<T>
    for BTreeSet<T, C, A>
{
    #[inline]
    fn extend<Iter: IntoIterator<Item = T>>(&mut self, iter: Iter) {
        iter.into_iter().for_each(move |elem| {
            self.insert(elem);
        });
    }

    #[inline]
    #[cfg(feature = "extend_one")]
    fn extend_one(&mut self, elem: T) {
        self.insert(elem);
    }
}

impl<'a, T: 'a + ContextualBorrow<T, C> + ContextualOrd<C> + Copy, C, A: Allocator + Clone>
    Extend<&'a T> for BTreeSet<T, C, A>
{
    fn extend<I: IntoIterator<Item = &'a T>>(&mut self, iter: I) {
        self.extend(iter.into_iter().cloned());
    }

    #[inline]
    #[cfg(feature = "extend_one")]
    fn extend_one(&mut self, &elem: &'a T) {
        self.insert(elem);
    }
}

impl<T, C: Default> Default for BTreeSet<T, C> {
    /// Creates an empty `BTreeSet` ordered by the `Ord` trait.
    fn default() -> BTreeSet<T, C> {
        BTreeSet::new(C::default())
    }
}

impl<T: ContextualBorrow<T, C> + ContextualOrd<C> + Clone, C: Clone, A: Allocator + Clone>
    Sub<&BTreeSet<T, C, A>> for &BTreeSet<T, C, A>
{
    type Output = BTreeSet<T, C, A>;

    /// Returns the difference of `self` and `rhs` as a new `BTreeSet<T>`.
    ///
    /// # Examples
    ///
    /// ```
    /// use contextual_alloc::collections::BTreeSet;
    ///
    /// let a = BTreeSet::from([1, 2, 3]);
    /// let b = BTreeSet::from([3, 4, 5]);
    ///
    /// let result = &a - &b;
    /// assert_eq!(result, BTreeSet::from([1, 2]));
    /// ```
    fn sub(self, rhs: &BTreeSet<T, C, A>) -> BTreeSet<T, C, A> {
        BTreeSet::from_sorted_iter(
            self.difference(rhs).cloned(),
            self.map.context.clone(),
            ManuallyDrop::into_inner(self.map.alloc.clone()),
        )
    }
}

impl<T: ContextualBorrow<T, C> + ContextualOrd<C> + Clone, C: Clone, A: Allocator + Clone>
    BitXor<&BTreeSet<T, C, A>> for &BTreeSet<T, C, A>
{
    type Output = BTreeSet<T, C, A>;

    /// Returns the symmetric difference of `self` and `rhs` as a new `BTreeSet<T>`.
    ///
    /// # Examples
    ///
    /// ```
    /// use contextual_alloc::collections::BTreeSet;
    ///
    /// let a = BTreeSet::from([1, 2, 3]);
    /// let b = BTreeSet::from([2, 3, 4]);
    ///
    /// let result = &a ^ &b;
    /// assert_eq!(result, BTreeSet::from([1, 4]));
    /// ```
    fn bitxor(self, rhs: &BTreeSet<T, C, A>) -> BTreeSet<T, C, A> {
        BTreeSet::from_sorted_iter(
            self.symmetric_difference(rhs).cloned(),
            self.map.context.clone(),
            ManuallyDrop::into_inner(self.map.alloc.clone()),
        )
    }
}

impl<T: ContextualBorrow<T, C> + ContextualOrd<C> + Clone, C: Clone, A: Allocator + Clone>
    BitAnd<&BTreeSet<T, C, A>> for &BTreeSet<T, C, A>
{
    type Output = BTreeSet<T, C, A>;

    /// Returns the intersection of `self` and `rhs` as a new `BTreeSet<T>`.
    ///
    /// # Examples
    ///
    /// ```
    /// use contextual_alloc::collections::BTreeSet;
    ///
    /// let a = BTreeSet::from([1, 2, 3]);
    /// let b = BTreeSet::from([2, 3, 4]);
    ///
    /// let result = &a & &b;
    /// assert_eq!(result, BTreeSet::from([2, 3]));
    /// ```
    fn bitand(self, rhs: &BTreeSet<T, C, A>) -> BTreeSet<T, C, A> {
        BTreeSet::from_sorted_iter(
            self.intersection(rhs).cloned(),
            self.map.context.clone(),
            ManuallyDrop::into_inner(self.map.alloc.clone()),
        )
    }
}

impl<T: ContextualBorrow<T, C> + ContextualOrd<C> + Clone, C: Clone, A: Allocator + Clone>
    BitOr<&BTreeSet<T, C, A>> for &BTreeSet<T, C, A>
{
    type Output = BTreeSet<T, C, A>;

    /// Returns the union of `self` and `rhs` as a new `BTreeSet<T>`.
    ///
    /// # Examples
    ///
    /// ```
    /// use contextual_alloc::collections::BTreeSet;
    ///
    /// let a = BTreeSet::from([1, 2, 3]);
    /// let b = BTreeSet::from([3, 4, 5]);
    ///
    /// let result = &a | &b;
    /// assert_eq!(result, BTreeSet::from([1, 2, 3, 4, 5]));
    /// ```
    fn bitor(self, rhs: &BTreeSet<T, C, A>) -> BTreeSet<T, C, A> {
        BTreeSet::from_sorted_iter(
            self.union(rhs).cloned(),
            self.map.context.clone(),
            ManuallyDrop::into_inner(self.map.alloc.clone()),
        )
    }
}

impl<T: Debug, C, A: Allocator + Clone> Debug for BTreeSet<T, C, A> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_set().entries(self.iter()).finish()
    }
}

impl<T> Clone for Iter<'_, T> {
    fn clone(&self) -> Self {
        Iter { iter: self.iter.clone() }
    }
}
impl<'a, T> Iterator for Iter<'a, T> {
    type Item = &'a T;

    fn next(&mut self) -> Option<&'a T> {
        self.iter.next()
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        self.iter.size_hint()
    }

    fn last(mut self) -> Option<&'a T> {
        self.next_back()
    }

    fn min(mut self) -> Option<&'a T> {
        self.next()
    }

    fn max(mut self) -> Option<&'a T> {
        self.next_back()
    }
}
impl<'a, T> DoubleEndedIterator for Iter<'a, T> {
    fn next_back(&mut self) -> Option<&'a T> {
        self.iter.next_back()
    }
}
impl<T> ExactSizeIterator for Iter<'_, T> {
    fn len(&self) -> usize {
        self.iter.len()
    }
}

impl<T> FusedIterator for Iter<'_, T> {}

impl<T, A: Allocator + Clone> Iterator for IntoIter<T, A> {
    type Item = T;

    fn next(&mut self) -> Option<T> {
        self.iter.next().map(|(k, _)| k)
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        self.iter.size_hint()
    }
}
impl<T, A: Allocator + Clone> DoubleEndedIterator for IntoIter<T, A> {
    fn next_back(&mut self) -> Option<T> {
        self.iter.next_back().map(|(k, _)| k)
    }
}
impl<T, A: Allocator + Clone> ExactSizeIterator for IntoIter<T, A> {
    fn len(&self) -> usize {
        self.iter.len()
    }
}

impl<T, A: Allocator + Clone> FusedIterator for IntoIter<T, A> {}

impl<T> Clone for Range<'_, T> {
    fn clone(&self) -> Self {
        Range { iter: self.iter.clone() }
    }
}

impl<'a, T> Iterator for Range<'a, T> {
    type Item = &'a T;

    fn next(&mut self) -> Option<&'a T> {
        self.iter.next().map(|(k, _)| k)
    }

    fn last(mut self) -> Option<&'a T> {
        self.next_back()
    }

    fn min(mut self) -> Option<&'a T> {
        self.next()
    }

    fn max(mut self) -> Option<&'a T> {
        self.next_back()
    }
}

impl<'a, T> DoubleEndedIterator for Range<'a, T> {
    fn next_back(&mut self) -> Option<&'a T> {
        self.iter.next_back().map(|(k, _)| k)
    }
}

impl<T> FusedIterator for Range<'_, T> {}

impl<T, C, A: Allocator + Clone> Clone for Difference<'_, T, C, A> {
    fn clone(&self) -> Self {
        Difference {
            inner: match &self.inner {
                DifferenceInner::Stitch { self_iter, other_iter } => DifferenceInner::Stitch {
                    self_iter: self_iter.clone(),
                    other_iter: other_iter.clone(),
                },
                DifferenceInner::Search { self_iter, other_set } => {
                    DifferenceInner::Search { self_iter: self_iter.clone(), other_set }
                }
                DifferenceInner::Iterate(iter) => DifferenceInner::Iterate(iter.clone()),
            },
            context: self.context,
        }
    }
}
impl<'a, T: ContextualBorrow<T, C> + ContextualOrd<C>, C, A: Allocator + Clone> Iterator
    for Difference<'a, T, C, A>
{
    type Item = &'a T;

    fn next(&mut self) -> Option<&'a T> {
        match &mut self.inner {
            DifferenceInner::Stitch { self_iter, other_iter } => {
                let mut self_next = self_iter.next()?;
                loop {
                    match other_iter.peek().map_or(Less, |&other_next| {
                        self_next.contextual_cmp(other_next, &self.context)
                    }) {
                        Less => return Some(self_next),
                        Equal => {
                            self_next = self_iter.next()?;
                            other_iter.next();
                        }
                        Greater => {
                            other_iter.next();
                        }
                    }
                }
            }
            DifferenceInner::Search { self_iter, other_set } => loop {
                let self_next = self_iter.next()?;
                if !other_set.contains(self_next) {
                    return Some(self_next);
                }
            },
            DifferenceInner::Iterate(iter) => iter.next(),
        }
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        let (self_len, other_len) = match &self.inner {
            DifferenceInner::Stitch { self_iter, other_iter } => {
                (self_iter.len(), other_iter.len())
            }
            DifferenceInner::Search { self_iter, other_set } => (self_iter.len(), other_set.len()),
            DifferenceInner::Iterate(iter) => (iter.len(), 0),
        };
        (self_len.saturating_sub(other_len), Some(self_len))
    }

    fn min(mut self) -> Option<&'a T> {
        self.next()
    }
}

impl<T: ContextualBorrow<T, C> + ContextualOrd<C>, C, A: Allocator + Clone> FusedIterator
    for Difference<'_, T, C, A>
{
}

impl<T, C> Clone for SymmetricDifference<'_, T, C> {
    fn clone(&self) -> Self {
        SymmetricDifference(self.0.clone(), self.1)
    }
}
impl<'a, T: ContextualOrd<C>, C> Iterator for SymmetricDifference<'a, T, C> {
    type Item = &'a T;

    fn next(&mut self) -> Option<&'a T> {
        loop {
            let (a_next, b_next) = self.0.nexts(|&a, &b| a.contextual_cmp(b, &self.1));
            if a_next.and(b_next).is_none() {
                return a_next.or(b_next);
            }
        }
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        let (a_len, b_len) = self.0.lens();
        // No checked_add, because even if a and b refer to the same set,
        // and T is a zero-sized type, the storage overhead of sets limits
        // the number of elements to less than half the range of usize.
        (0, Some(a_len + b_len))
    }

    fn min(mut self) -> Option<&'a T> {
        self.next()
    }
}

impl<T: ContextualOrd<C>, C> FusedIterator for SymmetricDifference<'_, T, C> {}

impl<T, C: Clone, A: Allocator + Clone> Clone for Intersection<'_, T, C, A> {
    fn clone(&self) -> Self {
        Intersection {
            inner: match &self.inner {
                IntersectionInner::Stitch { a, b } => {
                    IntersectionInner::Stitch { a: a.clone(), b: b.clone() }
                }
                IntersectionInner::Search { small_iter, large_set } => {
                    IntersectionInner::Search { small_iter: small_iter.clone(), large_set }
                }
                IntersectionInner::Answer(answer) => IntersectionInner::Answer(*answer),
            },
            context: self.context,
        }
    }
}
impl<'a, T: ContextualBorrow<T, C> + ContextualOrd<C>, C, A: Allocator + Clone> Iterator
    for Intersection<'a, T, C, A>
{
    type Item = &'a T;

    fn next(&mut self) -> Option<&'a T> {
        match &mut self.inner {
            IntersectionInner::Stitch { a, b } => {
                let mut a_next = a.next()?;
                let mut b_next = b.next()?;
                loop {
                    match a_next.contextual_cmp(b_next, &self.context) {
                        Less => a_next = a.next()?,
                        Greater => b_next = b.next()?,
                        Equal => return Some(a_next),
                    }
                }
            }
            IntersectionInner::Search { small_iter, large_set } => loop {
                let small_next = small_iter.next()?;
                if large_set.contains(small_next) {
                    return Some(small_next);
                }
            },
            IntersectionInner::Answer(answer) => answer.take(),
        }
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        match &self.inner {
            IntersectionInner::Stitch { a, b } => (0, Some(min(a.len(), b.len()))),
            IntersectionInner::Search { small_iter, .. } => (0, Some(small_iter.len())),
            IntersectionInner::Answer(None) => (0, Some(0)),
            IntersectionInner::Answer(Some(_)) => (1, Some(1)),
        }
    }

    fn min(mut self) -> Option<&'a T> {
        self.next()
    }
}

impl<T: ContextualBorrow<T, C> + ContextualOrd<C>, C, A: Allocator + Clone> FusedIterator
    for Intersection<'_, T, C, A>
{
}

impl<T, C> Clone for Union<'_, T, C> {
    fn clone(&self) -> Self {
        Union(self.0.clone(), self.1)
    }
}
impl<'a, T: ContextualOrd<C>, C> Iterator for Union<'a, T, C> {
    type Item = &'a T;

    fn next(&mut self) -> Option<&'a T> {
        let (a_next, b_next) = self.0.nexts(|&a, &b| a.contextual_cmp(b, &self.1));
        a_next.or(b_next)
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        let (a_len, b_len) = self.0.lens();
        // No checked_add - see SymmetricDifference::size_hint.
        (max(a_len, b_len), Some(a_len + b_len))
    }

    fn min(mut self) -> Option<&'a T> {
        self.next()
    }
}

impl<T: ContextualOrd<C>, C> FusedIterator for Union<'_, T, C> {}

#[cfg(test)]
mod tests;
