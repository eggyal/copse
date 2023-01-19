// This is pretty much entirely stolen from TreeSet, since BTreeMap has an identical interface
// to TreeMap

use crate::{LookupKey, OrdStoredKey, OrdTotalOrder, TotalOrder};
use alloc::vec::Vec;
use core::cmp::Ordering::{self, Equal, Greater, Less};
use core::cmp::{max, min};
use core::fmt::{self, Debug};
use core::hash::{Hash, Hasher};
use core::iter::{FromIterator, FusedIterator, Peekable};
use core::mem::ManuallyDrop;
use core::ops::{BitAnd, BitOr, BitXor, RangeBounds, Sub};

use super::map::{BTreeMap, Keys};
use super::merge_iter::MergeIterInner;
use super::set_val::SetValZST;
use super::Recover;

use crate::polyfill::*;

// FIXME(conventions): implement bounded iterators

/// An ordered set based on a B-Tree.
///
/// See [`BTreeMap`]'s documentation for a detailed discussion of this collection's performance
/// benefits and drawbacks.
///
/// It is a logic error for an item or total order to be modified in such a way that the item's
/// ordering relative to any other item, as determined by that total order, changes while they
/// are in the set. This is normally only possible through [`Cell`], [`RefCell`], global state,
/// I/O, or unsafe code. The behavior resulting from such a logic error is not specified, but
/// will be encapsulated to the `BTreeSet` that observed the logic error and not result in
/// undefined behavior. This could include panics, incorrect results, aborts, memory leaks, and
/// non-termination.
///
/// Iterators returned by [`BTreeSet::iter`] produce their items in order, and take worst-case
/// logarithmic and amortized constant time per item returned.
///
/// [`Cell`]: core::cell::Cell
/// [`RefCell`]: core::cell::RefCell
///
/// # Examples
///
/// ```
/// use copse::BTreeSet;
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
/// use copse::BTreeSet;
///
/// let set = BTreeSet::from([1, 2, 3]);
/// ```
pub struct BTreeSet<
    T,
    O = OrdTotalOrder<<T as OrdStoredKey>::DefaultComparisonKey>,
    A: Allocator + Clone = Global,
> {
    map: BTreeMap<T, SetValZST, O, A>,
}

impl<T: Hash, O, A: Allocator + Clone> Hash for BTreeSet<T, O, A> {
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.map.hash(state)
    }
}

impl<T: PartialEq, O, A: Allocator + Clone> PartialEq for BTreeSet<T, O, A> {
    fn eq(&self, other: &BTreeSet<T, O, A>) -> bool {
        self.map.eq(&other.map)
    }
}

impl<T: Eq, O, A: Allocator + Clone> Eq for BTreeSet<T, O, A> {}

impl<T: PartialOrd, O, A: Allocator + Clone> PartialOrd for BTreeSet<T, O, A> {
    fn partial_cmp(&self, other: &BTreeSet<T, O, A>) -> Option<Ordering> {
        self.map.partial_cmp(&other.map)
    }
}

impl<T: Ord, O, A: Allocator + Clone> Ord for BTreeSet<T, O, A> {
    fn cmp(&self, other: &BTreeSet<T, O, A>) -> Ordering {
        self.map.cmp(&other.map)
    }
}

impl<T: Clone, O: Clone, A: Allocator + Clone> Clone for BTreeSet<T, O, A> {
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
pub struct Difference<'a, T: 'a, O, A: Allocator + Clone = Global> {
    inner: DifferenceInner<'a, T, O, A>,
    order: &'a O,
}
enum DifferenceInner<'a, T: 'a, O, A: Allocator + Clone> {
    Stitch {
        // iterate all of `self` and some of `other`, spotting matches along the way
        self_iter: Iter<'a, T>,
        other_iter: Peekable<Iter<'a, T>>,
    },
    Search {
        // iterate `self`, look up in `other`
        self_iter: Iter<'a, T>,
        other_set: &'a BTreeSet<T, O, A>,
    },
    Iterate(Iter<'a, T>), // simply produce all elements in `self`
}

// Explicit Debug impl necessary because of issue #26925
impl<T: Debug, O: TotalOrder, A: Allocator + Clone> Debug for DifferenceInner<'_, T, O, A> {
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

impl<T: fmt::Debug, O: TotalOrder, A: Allocator + Clone> fmt::Debug for Difference<'_, T, O, A> {
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
pub struct SymmetricDifference<'a, T: 'a, O>(MergeIterInner<Iter<'a, T>>, &'a O);

impl<T: fmt::Debug, O> fmt::Debug for SymmetricDifference<'_, T, O> {
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
pub struct Intersection<'a, T: 'a, O, A: Allocator + Clone = Global> {
    inner: IntersectionInner<'a, T, O, A>,
    order: &'a O,
}
enum IntersectionInner<'a, T: 'a, O, A: Allocator + Clone> {
    Stitch {
        // iterate similarly sized sets jointly, spotting matches along the way
        a: Iter<'a, T>,
        b: Iter<'a, T>,
    },
    Search {
        // iterate a small set, look up in the large set
        small_iter: Iter<'a, T>,
        large_set: &'a BTreeSet<T, O, A>,
    },
    Answer(Option<&'a T>), // return a specific element or emptiness
}

// Explicit Debug impl necessary because of issue #26925
impl<T: Debug, O: TotalOrder, A: Allocator + Clone> Debug for IntersectionInner<'_, T, O, A> {
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

impl<T: Debug, O: TotalOrder, A: Allocator + Clone> Debug for Intersection<'_, T, O, A> {
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
pub struct Union<'a, T: 'a, O>(MergeIterInner<Iter<'a, T>>, &'a O);

impl<T: fmt::Debug, O> fmt::Debug for Union<'_, T, O> {
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

impl<T, O> BTreeSet<T, O> {
    /// Makes a new, empty `BTreeSet` ordered by the given `order`.
    ///
    /// Does not allocate anything on its own.
    ///
    /// # Examples
    ///
    /// ```
    /// # use copse::{BTreeSet, LookupKey, TotalOrder};
    /// # use std::cmp::Ordering;
    /// #
    /// // define a total order
    /// struct OrderByNthByte {
    ///     n: usize, // runtime state
    /// }
    ///
    /// impl TotalOrder for OrderByNthByte {
    ///     // etc
    /// #     type OrderedType = [u8];
    /// #     fn cmp(&self, this: &[u8], that: &[u8]) -> Ordering {
    /// #         match (this.get(self.n), that.get(self.n)) {
    /// #             (Some(lhs), Some(rhs)) => lhs.cmp(rhs),
    /// #             (Some(_), None) => Ordering::Greater,
    /// #             (None, Some(_)) => Ordering::Less,
    /// #             (None, None) => Ordering::Equal,
    /// #         }
    /// #     }
    /// }
    ///
    /// // define lookup key types for collections sorted by our total order
    /// # impl LookupKey<OrderByNthByte> for [u8] {
    /// #     fn key(&self) -> &[u8] { self }
    /// # }
    /// # impl LookupKey<OrderByNthByte> for str {
    /// #     fn key(&self) -> &[u8] { self.as_bytes() }
    /// # }
    /// impl LookupKey<OrderByNthByte> for String {
    ///     // etc
    /// #     fn key(&self) -> &[u8] { LookupKey::<OrderByNthByte>::key(self.as_str()) }
    /// }
    ///
    /// // create a set using our total order
    /// let mut set = BTreeSet::new(OrderByNthByte { n: 9 });
    ///
    /// // entries can now be inserted into the empty set
    /// assert!(set.insert("abcdefghij".to_string()));
    /// ```
    #[must_use]
    pub const fn new(order: O) -> BTreeSet<T, O> {
        BTreeSet { map: BTreeMap::new(order) }
    }
}

impl<T, O, A: Allocator + Clone> BTreeSet<T, O, A> {
    decorate_if! {
        if #[cfg(feature = "btreemap_alloc")] {
            /// Makes a new `BTreeSet` with a reasonable choice of B ordered by the given `order`.
            ///
            /// # Examples
            ///
            /// Basic usage:
            ///
            /// ```
            /// # #![feature(allocator_api)]
            /// use copse::{BTreeSet, OrdTotalOrder};
            /// use std::alloc::Global;
            ///
            /// let mut set = BTreeSet::<_>::new_in(OrdTotalOrder::default(), Global);
            ///
            /// // entries can now be inserted into the empty set
            /// set.insert("a".to_string());
            /// ```
            pub
        }
        fn new_in(order: O, alloc: A) -> BTreeSet<T, O, A> {
            BTreeSet { map: BTreeMap::new_in(order, alloc) }
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
    /// use copse::BTreeSet;
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
        K: LookupKey<O>,
        T: LookupKey<O>,
        O: TotalOrder,
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
    /// use copse::BTreeSet;
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
    pub fn difference<'a>(&'a self, other: &'a BTreeSet<T, O, A>) -> Difference<'a, T, O, A>
    where
        T: LookupKey<O>,
        O: TotalOrder,
    {
        let (self_min, self_max) =
            if let (Some(self_min), Some(self_max)) = (self.first(), self.last()) {
                (self_min, self_max)
            } else {
                return Difference {
                    inner: DifferenceInner::Iterate(self.iter()),
                    order: &self.map.order,
                };
            };
        let (other_min, other_max) =
            if let (Some(other_min), Some(other_max)) = (other.first(), other.last()) {
                (other_min, other_max)
            } else {
                return Difference {
                    inner: DifferenceInner::Iterate(self.iter()),
                    order: &self.map.order,
                };
            };
        Difference {
            inner: match (
                self.map.order.cmp(self_min.key(), other_max.key()),
                self.map.order.cmp(self_max.key(), other_min.key()),
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
            order: &self.map.order,
        }
    }

    /// Visits the elements representing the symmetric difference,
    /// i.e., the elements that are in `self` or in `other` but not in both,
    /// in ascending order.
    ///
    /// # Examples
    ///
    /// ```
    /// use copse::BTreeSet;
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
        other: &'a BTreeSet<T, O, A>,
    ) -> SymmetricDifference<'a, T, O>
    where
        T: LookupKey<O>,
        O: TotalOrder,
    {
        SymmetricDifference(MergeIterInner::new(self.iter(), other.iter()), &self.map.order)
    }

    /// Visits the elements representing the intersection,
    /// i.e., the elements that are both in `self` and `other`,
    /// in ascending order.
    ///
    /// # Examples
    ///
    /// ```
    /// use copse::BTreeSet;
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
    pub fn intersection<'a>(&'a self, other: &'a BTreeSet<T, O, A>) -> Intersection<'a, T, O, A>
    where
        T: LookupKey<O>,
        O: TotalOrder,
    {
        let (self_min, self_max) = if let (Some(self_min), Some(self_max)) =
            (self.first(), self.last())
        {
            (self_min, self_max)
        } else {
            return Intersection { inner: IntersectionInner::Answer(None), order: &self.map.order };
        };
        let (other_min, other_max) = if let (Some(other_min), Some(other_max)) =
            (other.first(), other.last())
        {
            (other_min, other_max)
        } else {
            return Intersection { inner: IntersectionInner::Answer(None), order: &self.map.order };
        };
        Intersection {
            inner: match (
                self.map.order.cmp(self_min.key(), other_max.key()),
                self.map.order.cmp(self_max.key(), other_min.key()),
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
            order: &self.map.order,
        }
    }

    /// Visits the elements representing the union,
    /// i.e., all the elements in `self` or `other`, without duplicates,
    /// in ascending order.
    ///
    /// # Examples
    ///
    /// ```
    /// use copse::BTreeSet;
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
    pub fn union<'a>(&'a self, other: &'a BTreeSet<T, O, A>) -> Union<'a, T, O>
    where
        T: LookupKey<O>,
        O: TotalOrder,
    {
        Union(MergeIterInner::new(self.iter(), other.iter()), &self.map.order)
    }

    /// Clears the set, removing all elements.
    ///
    /// # Examples
    ///
    /// ```
    /// use copse::BTreeSet;
    ///
    /// let mut v = BTreeSet::default();
    /// v.insert(1);
    /// v.clear();
    /// assert!(v.is_empty());
    /// ```
    pub fn clear(&mut self)
    where
        A: Clone,
        O: Clone,
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
    /// use copse::BTreeSet;
    ///
    /// let set = BTreeSet::from([1, 2, 3]);
    /// assert_eq!(set.contains(&1), true);
    /// assert_eq!(set.contains(&4), false);
    /// ```
    pub fn contains<Q: ?Sized>(&self, value: &Q) -> bool
    where
        T: LookupKey<O>,
        Q: LookupKey<O>,
        O: TotalOrder,
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
    /// use copse::BTreeSet;
    ///
    /// let set = BTreeSet::from([1, 2, 3]);
    /// assert_eq!(set.get(&2), Some(&2));
    /// assert_eq!(set.get(&4), None);
    /// ```
    pub fn get<Q: ?Sized>(&self, value: &Q) -> Option<&T>
    where
        T: LookupKey<O>,
        Q: LookupKey<O>,
        O: TotalOrder,
    {
        Recover::get(&self.map, value)
    }

    /// Returns `true` if `self` has no elements in common with `other`.
    /// This is equivalent to checking for an empty intersection.
    ///
    /// # Examples
    ///
    /// ```
    /// use copse::BTreeSet;
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
    pub fn is_disjoint(&self, other: &BTreeSet<T, O, A>) -> bool
    where
        T: LookupKey<O>,
        O: TotalOrder,
    {
        self.intersection(other).next().is_none()
    }

    /// Returns `true` if the set is a subset of another,
    /// i.e., `other` contains at least all the elements in `self`.
    ///
    /// # Examples
    ///
    /// ```
    /// use copse::BTreeSet;
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
    pub fn is_subset(&self, other: &BTreeSet<T, O, A>) -> bool
    where
        T: LookupKey<O>,
        O: TotalOrder,
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
        match self.map.order.cmp(self_min.key(), other_min.key()) {
            Less => return false,
            Equal => {
                self_iter.next();
            }
            Greater => (),
        }
        match self.map.order.cmp(self_max.key(), other_max.key()) {
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
                    .map_or(Less, |other1| self.map.order.cmp(self1.key(), other1.key()))
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
    /// use copse::BTreeSet;
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
    pub fn is_superset(&self, other: &BTreeSet<T, O, A>) -> bool
    where
        T: LookupKey<O>,
        O: TotalOrder,
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
    /// use copse::BTreeSet;
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
        T: LookupKey<O>,
        O: TotalOrder,
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
    /// use copse::BTreeSet;
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
        T: LookupKey<O>,
        O: TotalOrder,
    {
        self.map.last_key_value().map(|(k, _)| k)
    }

    /// Removes the first element from the set and returns it, if any.
    /// The first element is always the minimum element in the set.
    ///
    /// # Examples
    ///
    /// ```
    /// use copse::BTreeSet;
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
        T: LookupKey<O>,
        O: TotalOrder,
    {
        self.map.pop_first().map(|kv| kv.0)
    }

    /// Removes the last element from the set and returns it, if any.
    /// The last element is always the maximum element in the set.
    ///
    /// # Examples
    ///
    /// ```
    /// use copse::BTreeSet;
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
        T: LookupKey<O>,
        O: TotalOrder,
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
    /// use copse::BTreeSet;
    ///
    /// let mut set = BTreeSet::default();
    ///
    /// assert_eq!(set.insert(2), true);
    /// assert_eq!(set.insert(2), false);
    /// assert_eq!(set.len(), 1);
    /// ```
    pub fn insert(&mut self, value: T) -> bool
    where
        T: LookupKey<O>,
        O: TotalOrder,
    {
        self.map.insert(value, SetValZST::default()).is_none()
    }

    /// Adds a value to the set, replacing the existing element, if any, that is
    /// equal to the value. Returns the replaced element.
    ///
    /// # Examples
    ///
    /// ```
    /// use copse::BTreeSet;
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
        T: LookupKey<O>,
        O: TotalOrder,
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
    /// use copse::BTreeSet;
    ///
    /// let mut set = BTreeSet::default();
    ///
    /// set.insert(2);
    /// assert_eq!(set.remove(&2), true);
    /// assert_eq!(set.remove(&2), false);
    /// ```
    pub fn remove<Q: ?Sized>(&mut self, value: &Q) -> bool
    where
        T: LookupKey<O>,
        Q: LookupKey<O>,
        O: TotalOrder,
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
    /// use copse::BTreeSet;
    ///
    /// let mut set = BTreeSet::from([1, 2, 3]);
    /// assert_eq!(set.take(&2), Some(2));
    /// assert_eq!(set.take(&2), None);
    /// ```
    pub fn take<Q: ?Sized>(&mut self, value: &Q) -> Option<T>
    where
        T: LookupKey<O>,
        Q: LookupKey<O>,
        O: TotalOrder,
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
    /// use copse::BTreeSet;
    ///
    /// let mut set = BTreeSet::from([1, 2, 3, 4, 5, 6]);
    /// // Keep only the even numbers.
    /// set.retain(|&k| k % 2 == 0);
    /// assert!(set.iter().eq([2, 4, 6].iter()));
    /// ```
    pub fn retain<F>(&mut self, mut f: F)
    where
        T: LookupKey<O>,
        O: TotalOrder,
        F: FnMut(&T) -> bool,
    {
        self.drain_filter(|v| !f(v));
    }

    /// Moves all elements from `other` into `self`, leaving `other` empty.
    ///
    /// # Examples
    ///
    /// ```
    /// use copse::BTreeSet;
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
        T: LookupKey<O>,
        O: Clone + TotalOrder,
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
    /// use copse::BTreeSet;
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
    pub fn split_off<Q: ?Sized + LookupKey<O>>(&mut self, value: &Q) -> Self
    where
        T: LookupKey<O>,
        O: TotalOrder + Clone,
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
            /// use copse::BTreeSet;
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
            T: LookupKey<O>,
            O: TotalOrder,
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
    /// use copse::BTreeSet;
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
    /// use copse::BTreeSet;
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
        /// use copse::BTreeSet;
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
        /// use copse::BTreeSet;
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
}

impl<T: LookupKey<O>, O: TotalOrder + Default> FromIterator<T> for BTreeSet<T, O> {
    fn from_iter<I: IntoIterator<Item = T>>(iter: I) -> BTreeSet<T, O> {
        let mut inputs: Vec<_> = iter.into_iter().collect();

        if inputs.is_empty() {
            return BTreeSet::default();
        }

        // use stable sort to preserve the insertion order.
        let order = O::default();
        inputs.sort_by(|a, b| order.cmp(a.key(), b.key()));
        BTreeSet::from_sorted_iter(inputs.into_iter(), order, Global)
    }
}

impl<T: LookupKey<O>, O: TotalOrder, A: Allocator + Clone> BTreeSet<T, O, A> {
    fn from_sorted_iter<I: Iterator<Item = T>>(iter: I, order: O, alloc: A) -> BTreeSet<T, O, A> {
        let iter = iter.map(|k| (k, SetValZST::default()));
        let map = BTreeMap::bulk_build_from_sorted_iter(iter, order, alloc);
        BTreeSet { map }
    }
}

impl<T: LookupKey<O>, O: TotalOrder + Default, const N: usize> From<[T; N]> for BTreeSet<T, O> {
    /// Converts a `[T; N]` into a `BTreeSet<T>`.
    ///
    /// ```
    /// use copse::BTreeSet;
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
        let order = O::default();
        arr.sort_by(|a, b| order.cmp(a.key(), b.key()));
        let iter = IntoIterator::into_iter(arr).map(|k| (k, SetValZST::default()));
        let map = BTreeMap::bulk_build_from_sorted_iter(iter, order, Global);
        BTreeSet { map }
    }
}

impl<T, O, A: Allocator + Clone> IntoIterator for BTreeSet<T, O, A> {
    type Item = T;
    type IntoIter = IntoIter<T, A>;

    /// Gets an iterator for moving out the `BTreeSet`'s contents.
    ///
    /// # Examples
    ///
    /// ```
    /// use copse::BTreeSet;
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

impl<'a, T, O: TotalOrder, A: Allocator + Clone> IntoIterator for &'a BTreeSet<T, O, A> {
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

impl<T: LookupKey<O>, O: TotalOrder, A: Allocator + Clone> Extend<T> for BTreeSet<T, O, A> {
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

impl<'a, T: 'a + LookupKey<O> + Copy, O: TotalOrder, A: Allocator + Clone> Extend<&'a T>
    for BTreeSet<T, O, A>
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

impl<T, O: Default> Default for BTreeSet<T, O> {
    /// Creates an empty `BTreeSet` ordered by the `Ord` trait.
    fn default() -> BTreeSet<T, O> {
        BTreeSet::new(O::default())
    }
}

impl<T: LookupKey<O> + Clone, O: TotalOrder + Clone, A: Allocator + Clone> Sub<&BTreeSet<T, O, A>>
    for &BTreeSet<T, O, A>
{
    type Output = BTreeSet<T, O, A>;

    /// Returns the difference of `self` and `rhs` as a new `BTreeSet<T>`.
    ///
    /// # Examples
    ///
    /// ```
    /// use copse::BTreeSet;
    ///
    /// let a = BTreeSet::from([1, 2, 3]);
    /// let b = BTreeSet::from([3, 4, 5]);
    ///
    /// let result = &a - &b;
    /// assert_eq!(result, BTreeSet::from([1, 2]));
    /// ```
    fn sub(self, rhs: &BTreeSet<T, O, A>) -> BTreeSet<T, O, A> {
        BTreeSet::from_sorted_iter(
            self.difference(rhs).cloned(),
            self.map.order.clone(),
            ManuallyDrop::into_inner(self.map.alloc.clone()),
        )
    }
}

impl<T: LookupKey<O> + Clone, O: TotalOrder + Clone, A: Allocator + Clone>
    BitXor<&BTreeSet<T, O, A>> for &BTreeSet<T, O, A>
{
    type Output = BTreeSet<T, O, A>;

    /// Returns the symmetric difference of `self` and `rhs` as a new `BTreeSet<T>`.
    ///
    /// # Examples
    ///
    /// ```
    /// use copse::BTreeSet;
    ///
    /// let a = BTreeSet::from([1, 2, 3]);
    /// let b = BTreeSet::from([2, 3, 4]);
    ///
    /// let result = &a ^ &b;
    /// assert_eq!(result, BTreeSet::from([1, 4]));
    /// ```
    fn bitxor(self, rhs: &BTreeSet<T, O, A>) -> BTreeSet<T, O, A> {
        BTreeSet::from_sorted_iter(
            self.symmetric_difference(rhs).cloned(),
            self.map.order.clone(),
            ManuallyDrop::into_inner(self.map.alloc.clone()),
        )
    }
}

impl<T: LookupKey<O> + Clone, O: TotalOrder + Clone, A: Allocator + Clone>
    BitAnd<&BTreeSet<T, O, A>> for &BTreeSet<T, O, A>
{
    type Output = BTreeSet<T, O, A>;

    /// Returns the intersection of `self` and `rhs` as a new `BTreeSet<T>`.
    ///
    /// # Examples
    ///
    /// ```
    /// use copse::BTreeSet;
    ///
    /// let a = BTreeSet::from([1, 2, 3]);
    /// let b = BTreeSet::from([2, 3, 4]);
    ///
    /// let result = &a & &b;
    /// assert_eq!(result, BTreeSet::from([2, 3]));
    /// ```
    fn bitand(self, rhs: &BTreeSet<T, O, A>) -> BTreeSet<T, O, A> {
        BTreeSet::from_sorted_iter(
            self.intersection(rhs).cloned(),
            self.map.order.clone(),
            ManuallyDrop::into_inner(self.map.alloc.clone()),
        )
    }
}

impl<T: LookupKey<O> + Clone, O: TotalOrder + Clone, A: Allocator + Clone> BitOr<&BTreeSet<T, O, A>>
    for &BTreeSet<T, O, A>
{
    type Output = BTreeSet<T, O, A>;

    /// Returns the union of `self` and `rhs` as a new `BTreeSet<T>`.
    ///
    /// # Examples
    ///
    /// ```
    /// use copse::BTreeSet;
    ///
    /// let a = BTreeSet::from([1, 2, 3]);
    /// let b = BTreeSet::from([3, 4, 5]);
    ///
    /// let result = &a | &b;
    /// assert_eq!(result, BTreeSet::from([1, 2, 3, 4, 5]));
    /// ```
    fn bitor(self, rhs: &BTreeSet<T, O, A>) -> BTreeSet<T, O, A> {
        BTreeSet::from_sorted_iter(
            self.union(rhs).cloned(),
            self.map.order.clone(),
            ManuallyDrop::into_inner(self.map.alloc.clone()),
        )
    }
}

impl<T: Debug, O, A: Allocator + Clone> Debug for BTreeSet<T, O, A> {
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

impl<T, O, A: Allocator + Clone> Clone for Difference<'_, T, O, A> {
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
            order: self.order,
        }
    }
}
impl<'a, T: LookupKey<O>, O: TotalOrder, A: Allocator + Clone> Iterator
    for Difference<'a, T, O, A>
{
    type Item = &'a T;

    fn next(&mut self) -> Option<&'a T> {
        match &mut self.inner {
            DifferenceInner::Stitch { self_iter, other_iter } => {
                let mut self_next = self_iter.next()?;
                loop {
                    match other_iter.peek().map_or(Less, |&other_next| {
                        self.order.cmp(self_next.key(), other_next.key())
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

impl<T: LookupKey<O>, O: TotalOrder, A: Allocator + Clone> FusedIterator
    for Difference<'_, T, O, A>
{
}

impl<T, O> Clone for SymmetricDifference<'_, T, O> {
    fn clone(&self) -> Self {
        SymmetricDifference(self.0.clone(), self.1)
    }
}
impl<'a, T: LookupKey<O>, O: TotalOrder> Iterator for SymmetricDifference<'a, T, O> {
    type Item = &'a T;

    fn next(&mut self) -> Option<&'a T> {
        loop {
            let (a_next, b_next) = self.0.nexts(|&a, &b| self.1.cmp(a.key(), b.key()));
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

impl<T: LookupKey<O>, O: TotalOrder> FusedIterator for SymmetricDifference<'_, T, O> {}

impl<T, O: Clone, A: Allocator + Clone> Clone for Intersection<'_, T, O, A> {
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
            order: self.order,
        }
    }
}
impl<'a, T: LookupKey<O>, O: TotalOrder, A: Allocator + Clone> Iterator
    for Intersection<'a, T, O, A>
{
    type Item = &'a T;

    fn next(&mut self) -> Option<&'a T> {
        match &mut self.inner {
            IntersectionInner::Stitch { a, b } => {
                let mut a_next = a.next()?;
                let mut b_next = b.next()?;
                loop {
                    match self.order.cmp(a_next.key(), b_next.key()) {
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

impl<T: LookupKey<O>, O: TotalOrder, A: Allocator + Clone> FusedIterator
    for Intersection<'_, T, O, A>
{
}

impl<T, O> Clone for Union<'_, T, O> {
    fn clone(&self) -> Self {
        Union(self.0.clone(), self.1)
    }
}
impl<'a, T: LookupKey<O>, O: TotalOrder> Iterator for Union<'a, T, O> {
    type Item = &'a T;

    fn next(&mut self) -> Option<&'a T> {
        let (a_next, b_next) = self.0.nexts(|&a, &b| self.1.cmp(a.key(), b.key()));
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

impl<T: LookupKey<O>, O: TotalOrder> FusedIterator for Union<'_, T, O> {}

#[cfg(test)]
mod tests;
