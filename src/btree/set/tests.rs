use super::super::testing::crash_test::{CrashTestDummy, Panic};
use super::super::testing::rng::DeterministicRng;
use super::*;
use alloc::vec::Vec;
use std::cmp::Ordering;
use std::hash::{Hash, Hasher};
use std::iter::FromIterator;
use std::ops::Bound::{Excluded, Included};
use std::panic::{catch_unwind, AssertUnwindSafe};

#[test]
fn test_clone_eq() {
    let mut m = BTreeSet::default();

    m.insert(1);
    m.insert(2);

    assert_eq!(m.clone(), m);
}

#[test]
fn test_iter_min_max() {
    let mut a = BTreeSet::default();
    assert_eq!(a.iter().min(), None);
    assert_eq!(a.iter().max(), None);
    assert_eq!(a.range::<i32, _>(..).min(), None);
    assert_eq!(a.range::<i32, _>(..).max(), None);
    assert_eq!(a.difference(&BTreeSet::default()).min(), None);
    assert_eq!(a.difference(&BTreeSet::default()).max(), None);
    assert_eq!(a.intersection(&a).min(), None);
    assert_eq!(a.intersection(&a).max(), None);
    assert_eq!(a.symmetric_difference(&BTreeSet::default()).min(), None);
    assert_eq!(a.symmetric_difference(&BTreeSet::default()).max(), None);
    assert_eq!(a.union(&a).min(), None);
    assert_eq!(a.union(&a).max(), None);
    a.insert(1);
    a.insert(2);
    assert_eq!(a.iter().min(), Some(&1));
    assert_eq!(a.iter().max(), Some(&2));
    assert_eq!(a.range::<i32, _>(..).min(), Some(&1));
    assert_eq!(a.range::<i32, _>(..).max(), Some(&2));
    assert_eq!(a.difference(&BTreeSet::default()).min(), Some(&1));
    assert_eq!(a.difference(&BTreeSet::default()).max(), Some(&2));
    assert_eq!(a.intersection(&a).min(), Some(&1));
    assert_eq!(a.intersection(&a).max(), Some(&2));
    assert_eq!(a.symmetric_difference(&BTreeSet::default()).min(), Some(&1));
    assert_eq!(a.symmetric_difference(&BTreeSet::default()).max(), Some(&2));
    assert_eq!(a.union(&a).min(), Some(&1));
    assert_eq!(a.union(&a).max(), Some(&2));
}

fn check<F>(a: &[i32], b: &[i32], expected: &[i32], f: F)
where
    F: FnOnce(
        &BTreeSet<i32, MinCmpFn<i32>>,
        &BTreeSet<i32, MinCmpFn<i32>>,
        &mut dyn FnMut(&i32) -> bool,
    ) -> bool,
{
    let mut set_a = BTreeSet::default();
    let mut set_b = BTreeSet::default();

    for x in a {
        assert!(set_a.insert(*x))
    }
    for y in b {
        assert!(set_b.insert(*y))
    }

    let mut i = 0;
    f(&set_a, &set_b, &mut |&x| {
        if i < expected.len() {
            assert_eq!(x, expected[i]);
        }
        i += 1;
        true
    });
    assert_eq!(i, expected.len());
}

#[test]
fn test_intersection() {
    fn check_intersection(a: &[i32], b: &[i32], expected: &[i32]) {
        check(a, b, expected, |x, y, f| x.intersection(y).all(f))
    }

    check_intersection(&[], &[], &[]);
    check_intersection(&[1, 2, 3], &[], &[]);
    check_intersection(&[], &[1, 2, 3], &[]);
    check_intersection(&[2], &[1, 2, 3], &[2]);
    check_intersection(&[1, 2, 3], &[2], &[2]);
    check_intersection(
        &[11, 1, 3, 77, 103, 5, -5],
        &[2, 11, 77, -9, -42, 5, 3],
        &[3, 5, 11, 77],
    );

    if cfg!(miri) {
        // Miri is too slow
        return;
    }

    let large = Vec::from_iter(0..100);
    check_intersection(&[], &large, &[]);
    check_intersection(&large, &[], &[]);
    check_intersection(&[-1], &large, &[]);
    check_intersection(&large, &[-1], &[]);
    check_intersection(&[0], &large, &[0]);
    check_intersection(&large, &[0], &[0]);
    check_intersection(&[99], &large, &[99]);
    check_intersection(&large, &[99], &[99]);
    check_intersection(&[100], &large, &[]);
    check_intersection(&large, &[100], &[]);
    check_intersection(&[11, 5000, 1, 3, 77, 8924], &large, &[1, 3, 11, 77]);
}

#[test]
fn test_intersection_size_hint() {
    let x = BTreeSet::from([3, 4]);
    let y = BTreeSet::from([1, 2, 3]);
    let mut iter = x.intersection(&y);
    assert_eq!(iter.size_hint(), (1, Some(1)));
    assert_eq!(iter.next(), Some(&3));
    assert_eq!(iter.size_hint(), (0, Some(0)));
    assert_eq!(iter.next(), None);

    iter = y.intersection(&y);
    assert_eq!(iter.size_hint(), (0, Some(3)));
    assert_eq!(iter.next(), Some(&1));
    assert_eq!(iter.size_hint(), (0, Some(2)));
}

#[test]
fn test_difference() {
    fn check_difference(a: &[i32], b: &[i32], expected: &[i32]) {
        check(a, b, expected, |x, y, f| x.difference(y).all(f))
    }

    check_difference(&[], &[], &[]);
    check_difference(&[1, 12], &[], &[1, 12]);
    check_difference(&[], &[1, 2, 3, 9], &[]);
    check_difference(&[1, 3, 5, 9, 11], &[3, 9], &[1, 5, 11]);
    check_difference(&[1, 3, 5, 9, 11], &[3, 6, 9], &[1, 5, 11]);
    check_difference(&[1, 3, 5, 9, 11], &[0, 1], &[3, 5, 9, 11]);
    check_difference(&[1, 3, 5, 9, 11], &[11, 12], &[1, 3, 5, 9]);
    check_difference(
        &[-5, 11, 22, 33, 40, 42],
        &[-12, -5, 14, 23, 34, 38, 39, 50],
        &[11, 22, 33, 40, 42],
    );

    if cfg!(miri) {
        // Miri is too slow
        return;
    }

    let large = Vec::from_iter(0..100);
    check_difference(&[], &large, &[]);
    check_difference(&[-1], &large, &[-1]);
    check_difference(&[0], &large, &[]);
    check_difference(&[99], &large, &[]);
    check_difference(&[100], &large, &[100]);
    check_difference(&[11, 5000, 1, 3, 77, 8924], &large, &[5000, 8924]);
    check_difference(&large, &[], &large);
    check_difference(&large, &[-1], &large);
    check_difference(&large, &[100], &large);
}

#[test]
fn test_difference_size_hint() {
    let s246 = BTreeSet::from([2, 4, 6]);
    let s23456 = BTreeSet::from_iter(2..=6);
    let mut iter = s246.difference(&s23456);
    assert_eq!(iter.size_hint(), (0, Some(3)));
    assert_eq!(iter.next(), None);

    let s12345 = BTreeSet::from_iter(1..=5);
    iter = s246.difference(&s12345);
    assert_eq!(iter.size_hint(), (0, Some(3)));
    assert_eq!(iter.next(), Some(&6));
    assert_eq!(iter.size_hint(), (0, Some(0)));
    assert_eq!(iter.next(), None);

    let s34567 = BTreeSet::from_iter(3..=7);
    iter = s246.difference(&s34567);
    assert_eq!(iter.size_hint(), (0, Some(3)));
    assert_eq!(iter.next(), Some(&2));
    assert_eq!(iter.size_hint(), (0, Some(2)));
    assert_eq!(iter.next(), None);

    let s1 = BTreeSet::from_iter(-9..=1);
    iter = s246.difference(&s1);
    assert_eq!(iter.size_hint(), (3, Some(3)));

    let s2 = BTreeSet::from_iter(-9..=2);
    iter = s246.difference(&s2);
    assert_eq!(iter.size_hint(), (2, Some(2)));
    assert_eq!(iter.next(), Some(&4));
    assert_eq!(iter.size_hint(), (1, Some(1)));

    let s23 = BTreeSet::from([2, 3]);
    iter = s246.difference(&s23);
    assert_eq!(iter.size_hint(), (1, Some(3)));
    assert_eq!(iter.next(), Some(&4));
    assert_eq!(iter.size_hint(), (1, Some(1)));

    let s4 = BTreeSet::from([4]);
    iter = s246.difference(&s4);
    assert_eq!(iter.size_hint(), (2, Some(3)));
    assert_eq!(iter.next(), Some(&2));
    assert_eq!(iter.size_hint(), (1, Some(2)));
    assert_eq!(iter.next(), Some(&6));
    assert_eq!(iter.size_hint(), (0, Some(0)));
    assert_eq!(iter.next(), None);

    let s56 = BTreeSet::from([5, 6]);
    iter = s246.difference(&s56);
    assert_eq!(iter.size_hint(), (1, Some(3)));
    assert_eq!(iter.next(), Some(&2));
    assert_eq!(iter.size_hint(), (0, Some(2)));

    let s6 = BTreeSet::from_iter(6..=19);
    iter = s246.difference(&s6);
    assert_eq!(iter.size_hint(), (2, Some(2)));
    assert_eq!(iter.next(), Some(&2));
    assert_eq!(iter.size_hint(), (1, Some(1)));

    let s7 = BTreeSet::from_iter(7..=19);
    iter = s246.difference(&s7);
    assert_eq!(iter.size_hint(), (3, Some(3)));
}

#[test]
fn test_symmetric_difference() {
    fn check_symmetric_difference(a: &[i32], b: &[i32], expected: &[i32]) {
        check(a, b, expected, |x, y, f| x.symmetric_difference(y).all(f))
    }

    check_symmetric_difference(&[], &[], &[]);
    check_symmetric_difference(&[1, 2, 3], &[2], &[1, 3]);
    check_symmetric_difference(&[2], &[1, 2, 3], &[1, 3]);
    check_symmetric_difference(
        &[1, 3, 5, 9, 11],
        &[-2, 3, 9, 14, 22],
        &[-2, 1, 5, 11, 14, 22],
    );
}

#[test]
fn test_symmetric_difference_size_hint() {
    let x = BTreeSet::from([2, 4]);
    let y = BTreeSet::from([1, 2, 3]);
    let mut iter = x.symmetric_difference(&y);
    assert_eq!(iter.size_hint(), (0, Some(5)));
    assert_eq!(iter.next(), Some(&1));
    assert_eq!(iter.size_hint(), (0, Some(4)));
    assert_eq!(iter.next(), Some(&3));
    assert_eq!(iter.size_hint(), (0, Some(1)));
}

#[test]
fn test_union() {
    fn check_union(a: &[i32], b: &[i32], expected: &[i32]) {
        check(a, b, expected, |x, y, f| x.union(y).all(f))
    }

    check_union(&[], &[], &[]);
    check_union(&[1, 2, 3], &[2], &[1, 2, 3]);
    check_union(&[2], &[1, 2, 3], &[1, 2, 3]);
    check_union(
        &[1, 3, 5, 9, 11, 16, 19, 24],
        &[-2, 1, 5, 9, 13, 19],
        &[-2, 1, 3, 5, 9, 11, 13, 16, 19, 24],
    );
}

#[test]
fn test_union_size_hint() {
    let x = BTreeSet::from([2, 4]);
    let y = BTreeSet::from([1, 2, 3]);
    let mut iter = x.union(&y);
    assert_eq!(iter.size_hint(), (3, Some(5)));
    assert_eq!(iter.next(), Some(&1));
    assert_eq!(iter.size_hint(), (2, Some(4)));
    assert_eq!(iter.next(), Some(&2));
    assert_eq!(iter.size_hint(), (1, Some(2)));
}

#[test]
// Only tests the simple function definition with respect to intersection
fn test_is_disjoint() {
    let one = BTreeSet::from([1]);
    let two = BTreeSet::from([2]);
    assert!(one.is_disjoint(&two));
}

#[test]
// Also implicitly tests the trivial function definition of is_superset
fn test_is_subset() {
    fn is_subset(a: &[i32], b: &[i32]) -> bool {
        let set_a = BTreeSet::from_iter(a.iter());
        let set_b = BTreeSet::from_iter(b.iter());
        set_a.is_subset(&set_b)
    }

    assert!(is_subset(&[], &[]));
    assert!(is_subset(&[], &[1, 2]));
    assert!(!is_subset(&[0], &[1, 2]));
    assert!(is_subset(&[1], &[1, 2]));
    assert!(is_subset(&[2], &[1, 2]));
    assert!(!is_subset(&[3], &[1, 2]));
    assert!(!is_subset(&[1, 2], &[1]));
    assert!(is_subset(&[1, 2], &[1, 2]));
    assert!(!is_subset(&[1, 2], &[2, 3]));
    assert!(is_subset(
        &[-5, 11, 22, 33, 40, 42],
        &[-12, -5, 11, 14, 22, 23, 33, 34, 38, 39, 40, 42]
    ));
    assert!(!is_subset(
        &[-5, 11, 22, 33, 40, 42],
        &[-12, -5, 11, 14, 22, 23, 34, 38]
    ));

    if cfg!(miri) {
        // Miri is too slow
        return;
    }

    let large = Vec::from_iter(0..100);
    assert!(is_subset(&[], &large));
    assert!(!is_subset(&large, &[]));
    assert!(!is_subset(&[-1], &large));
    assert!(is_subset(&[0], &large));
    assert!(is_subset(&[1, 2], &large));
    assert!(!is_subset(&[99, 100], &large));
}

#[test]
fn test_is_superset() {
    fn is_superset(a: &[i32], b: &[i32]) -> bool {
        let set_a = BTreeSet::from_iter(a.iter());
        let set_b = BTreeSet::from_iter(b.iter());
        set_a.is_superset(&set_b)
    }

    assert!(is_superset(&[], &[]));
    assert!(!is_superset(&[], &[1, 2]));
    assert!(!is_superset(&[0], &[1, 2]));
    assert!(!is_superset(&[1], &[1, 2]));
    assert!(!is_superset(&[4], &[1, 2]));
    assert!(!is_superset(&[1, 4], &[1, 2]));
    assert!(is_superset(&[1, 2], &[1, 2]));
    assert!(is_superset(&[1, 2, 3], &[1, 3]));
    assert!(is_superset(&[1, 2, 3], &[]));
    assert!(is_superset(&[-1, 1, 2, 3], &[-1, 3]));

    if cfg!(miri) {
        // Miri is too slow
        return;
    }

    let large = Vec::from_iter(0..100);
    assert!(!is_superset(&[], &large));
    assert!(is_superset(&large, &[]));
    assert!(is_superset(&large, &[1]));
    assert!(is_superset(&large, &[50, 99]));
    assert!(!is_superset(&large, &[100]));
    assert!(is_superset(&large, &[0, 99]));
    assert!(!is_superset(&[-1], &large));
    assert!(!is_superset(&[0], &large));
    assert!(!is_superset(&[99, 100], &large));
}

#[test]
fn test_retain() {
    let mut set = BTreeSet::from([1, 2, 3, 4, 5, 6]);
    set.retain(|&k| k % 2 == 0);
    assert_eq!(set.len(), 3);
    assert!(set.contains(&2));
    assert!(set.contains(&4));
    assert!(set.contains(&6));
}

#[test]
fn test_drain_filter() {
    let mut x = BTreeSet::from([1]);
    let mut y = BTreeSet::from([1]);

    x.drain_filter(|_| true);
    y.drain_filter(|_| false);
    assert_eq!(x.len(), 0);
    assert_eq!(y.len(), 1);
}

#[test]
fn test_drain_filter_drop_panic_leak() {
    let a = CrashTestDummy::new(0);
    let b = CrashTestDummy::new(1);
    let c = CrashTestDummy::new(2);
    let mut set = BTreeSet::default();
    set.insert(a.spawn(Panic::Never));
    set.insert(b.spawn(Panic::InDrop));
    set.insert(c.spawn(Panic::Never));

    catch_unwind(move || drop(set.drain_filter(|dummy| dummy.query(true)))).ok();

    assert_eq!(a.queried(), 1);
    assert_eq!(b.queried(), 1);
    assert_eq!(c.queried(), 0);
    assert_eq!(a.dropped(), 1);
    assert_eq!(b.dropped(), 1);
    assert_eq!(c.dropped(), 1);
}

#[test]
fn test_drain_filter_pred_panic_leak() {
    let a = CrashTestDummy::new(0);
    let b = CrashTestDummy::new(1);
    let c = CrashTestDummy::new(2);
    let mut set = BTreeSet::default();
    set.insert(a.spawn(Panic::Never));
    set.insert(b.spawn(Panic::InQuery));
    set.insert(c.spawn(Panic::InQuery));

    catch_unwind(AssertUnwindSafe(|| {
        drop(set.drain_filter(|dummy| dummy.query(true)))
    }))
    .ok();

    assert_eq!(a.queried(), 1);
    assert_eq!(b.queried(), 1);
    assert_eq!(c.queried(), 0);
    assert_eq!(a.dropped(), 1);
    assert_eq!(b.dropped(), 0);
    assert_eq!(c.dropped(), 0);
    assert_eq!(set.len(), 2);
    assert_eq!(set.first().unwrap().id(), 1);
    assert_eq!(set.last().unwrap().id(), 2);
}

#[test]
fn test_clear() {
    let mut x = BTreeSet::default();
    x.insert(1);

    x.clear();
    assert!(x.is_empty());
}
#[test]
fn test_remove() {
    let mut x = BTreeSet::default();
    assert!(x.is_empty());

    x.insert(1);
    x.insert(2);
    x.insert(3);
    x.insert(4);

    assert!(x.remove(&2));
    assert!(!x.remove(&0));
    assert!(!x.remove(&5));
    assert!(x.remove(&1));
    assert!(!x.remove(&2));
    assert!(x.remove(&3));
    assert!(x.remove(&4));
    assert!(!x.remove(&4));
    assert!(x.is_empty());
}

#[test]
fn test_zip() {
    let mut x = BTreeSet::default();
    x.insert(5);
    x.insert(12);
    x.insert(11);

    let mut y = BTreeSet::default();
    y.insert("foo");
    y.insert("bar");

    let x = x;
    let y = y;
    let mut z = x.iter().zip(&y);

    assert_eq!(z.next().unwrap(), (&5, &("bar")));
    assert_eq!(z.next().unwrap(), (&11, &("foo")));
    assert!(z.next().is_none());
}

#[test]
fn test_from_iter() {
    let xs = [1, 2, 3, 4, 5, 6, 7, 8, 9];

    let set = BTreeSet::from_iter(xs.iter());

    for x in &xs {
        assert!(set.contains(x));
    }
}

#[test]
fn test_show() {
    let mut set = BTreeSet::default();
    let empty = BTreeSet::<i32>::default();

    set.insert(1);
    set.insert(2);

    let set_str = format!("{set:?}");

    assert_eq!(set_str, "{1, 2}");
    assert_eq!(format!("{empty:?}"), "{}");
}

#[test]
fn test_extend_ref() {
    let mut a = BTreeSet::default();
    a.insert(1);

    a.extend([2, 3, 4]);

    assert_eq!(a.len(), 4);
    assert!(a.contains(&1));
    assert!(a.contains(&2));
    assert!(a.contains(&3));
    assert!(a.contains(&4));

    let mut b = BTreeSet::default();
    b.insert(5);
    b.insert(6);

    a.extend(&b);

    assert_eq!(a.len(), 6);
    assert!(a.contains(&1));
    assert!(a.contains(&2));
    assert!(a.contains(&3));
    assert!(a.contains(&4));
    assert!(a.contains(&5));
    assert!(a.contains(&6));
}

#[test]
fn test_recovery() {
    #[derive(Debug)]
    struct Foo(&'static str, i32);

    impl Sortable for Foo {
        type State = Self;
    }

    impl PartialEq for Foo {
        fn eq(&self, other: &Self) -> bool {
            self.0 == other.0
        }
    }

    impl Eq for Foo {}

    impl PartialOrd for Foo {
        fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
            self.0.partial_cmp(other.0)
        }
    }

    impl Ord for Foo {
        fn cmp(&self, other: &Self) -> Ordering {
            self.0.cmp(other.0)
        }
    }

    let mut s = BTreeSet::default();
    assert_eq!(s.replace(Foo("a", 1)), None);
    assert_eq!(s.len(), 1);
    assert_eq!(s.replace(Foo("a", 2)), Some(Foo("a", 1)));
    assert_eq!(s.len(), 1);

    {
        let mut it = s.iter();
        assert_eq!(it.next(), Some(&Foo("a", 2)));
        assert_eq!(it.next(), None);
    }

    assert_eq!(s.get(&Foo("a", 1)), Some(&Foo("a", 2)));
    assert_eq!(s.take(&Foo("a", 1)), Some(Foo("a", 2)));
    assert_eq!(s.len(), 0);

    assert_eq!(s.get(&Foo("a", 1)), None);
    assert_eq!(s.take(&Foo("a", 1)), None);

    assert_eq!(s.iter().next(), None);
}

#[allow(dead_code)]
fn assert_covariance() {
    fn set<'new>(v: BTreeSet<&'static str>) -> BTreeSet<&'new str> {
        v
    }
    fn iter<'a, 'new>(v: Iter<'a, &'static str>) -> Iter<'a, &'new str> {
        v
    }
    fn into_iter<'new>(v: IntoIter<&'static str>) -> IntoIter<&'new str> {
        v
    }
    fn range<'a, 'new>(v: Range<'a, &'static str>) -> Range<'a, &'new str> {
        v
    }
    // not applied to Difference, Intersection, SymmetricDifference, Union
}

#[allow(dead_code)]
fn assert_sync() {
    fn set<T: Sortable + Sync>(v: &BTreeSet<T>) -> impl Sync + '_
    where
        T::State: Ord,
    {
        v
    }

    fn iter<T: Sortable + Sync>(v: &BTreeSet<T>) -> impl Sync + '_
    where
        T::State: Ord,
    {
        v.iter()
    }

    fn into_iter<T: Sortable + Sync>(v: BTreeSet<T>) -> impl Sync
    where
        T::State: Ord,
    {
        v.into_iter()
    }

    fn range<T: Sortable + Sync>(v: &BTreeSet<T>) -> impl Sync + '_
    where
        T::State: Ord,
    {
        v.range::<T, _>(..)
    }

    fn drain_filter<T: Sortable + Sync>(v: &mut BTreeSet<T>) -> impl Sync + '_
    where
        T::State: Ord,
    {
        v.drain_filter(|_| false)
    }

    fn difference<T: Sortable + Sync>(v: &BTreeSet<T>) -> impl Sync + '_
    where
        T::State: Ord,
    {
        v.difference(v)
    }

    fn intersection<T: Sortable + Sync>(v: &BTreeSet<T>) -> impl Sync + '_
    where
        T::State: Ord,
    {
        v.intersection(v)
    }

    fn symmetric_difference<T: Sortable + Sync>(v: &BTreeSet<T>) -> impl Sync + '_
    where
        T::State: Ord,
    {
        v.symmetric_difference(v)
    }

    fn union<T: Sortable + Sync>(v: &BTreeSet<T>) -> impl Sync + '_
    where
        T::State: Ord,
    {
        v.union(v)
    }
}

#[allow(dead_code)]
fn assert_send() {
    fn set<T: Sortable + Send>(v: BTreeSet<T>) -> impl Send
    where
        T::State: Ord,
    {
        v
    }

    fn iter<T: Sortable + Send + Sync>(v: &BTreeSet<T>) -> impl Send + '_
    where
        T::State: Ord,
    {
        v.iter()
    }

    fn into_iter<T: Sortable + Send>(v: BTreeSet<T>) -> impl Send
    where
        T::State: Ord,
    {
        v.into_iter()
    }

    fn range<T: Sortable + Send + Sync>(v: &BTreeSet<T>) -> impl Send + '_
    where
        T::State: Ord,
    {
        v.range::<T, _>(..)
    }

    fn drain_filter<T: Sortable + Send>(v: &mut BTreeSet<T>) -> impl Send + '_
    where
        T::State: Ord,
    {
        v.drain_filter(|_| false)
    }

    fn difference<T: Sortable + Send + Sync>(v: &BTreeSet<T>) -> impl Send + '_
    where
        T::State: Ord,
    {
        v.difference(v)
    }

    fn intersection<T: Sortable + Send + Sync>(v: &BTreeSet<T>) -> impl Send + '_
    where
        T::State: Ord,
    {
        v.intersection(v)
    }

    fn symmetric_difference<T: Sortable + Send + Sync>(v: &BTreeSet<T>) -> impl Send + '_
    where
        T::State: Ord,
    {
        v.symmetric_difference(v)
    }

    fn union<T: Sortable + Send + Sync>(v: &BTreeSet<T>) -> impl Send + '_
    where
        T::State: Ord,
    {
        v.union(v)
    }
}

#[allow(dead_code)]
// Check that the member-like functions conditionally provided by #[derive()]
// are not overridden by genuine member functions with a different signature.
fn assert_derives() {
    fn hash<T: Sortable + Hash, H: Hasher>(v: BTreeSet<T>, state: &mut H)
    where
        T::State: Ord,
    {
        v.hash(state);
        // Tested much more thoroughly outside the crate in btree_set_hash.rs
    }
    fn eq<T: Sortable + PartialEq>(v: BTreeSet<T>)
    where
        T::State: Ord,
    {
        let _ = v.eq(&v);
    }
    fn ne<T: Sortable + PartialEq>(v: BTreeSet<T>)
    where
        T::State: Ord,
    {
        let _ = v.ne(&v);
    }
    fn cmp<T: Sortable + Ord>(v: BTreeSet<T>)
    where
        T::State: Ord,
    {
        let _ = v.cmp(&v);
    }
    fn min<T: Sortable + Ord>(v: BTreeSet<T>, w: BTreeSet<T>)
    where
        T::State: Ord,
    {
        let _ = v.min(w);
    }
    fn max<T: Sortable + Ord>(v: BTreeSet<T>, w: BTreeSet<T>)
    where
        T::State: Ord,
    {
        let _ = v.max(w);
    }
    fn clamp<T: Sortable + Ord>(v: BTreeSet<T>, w: BTreeSet<T>, x: BTreeSet<T>)
    where
        T::State: Ord,
    {
        let _ = v.clamp(w, x);
    }
    fn partial_cmp<T: Sortable + PartialOrd>(v: &BTreeSet<T>)
    where
        T::State: Ord,
    {
        let _ = v.partial_cmp(v);
    }
}

#[test]
fn test_ord_absence() {
    fn set<K, C: Copy>(mut set: BTreeSet<K, C>) {
        let _ = set.is_empty();
        let _ = set.len();
        set.clear();
        let _ = set.iter();
        let _ = set.into_iter();
    }

    fn set_debug<K: Debug, C: Copy>(set: BTreeSet<K, C>) {
        format!("{set:?}");
        format!("{:?}", set.iter());
        format!("{:?}", set.into_iter());
    }

    fn set_clone<K: Clone, C: Copy>(mut set: BTreeSet<K, C>) {
        set.clone_from(&set.clone());
    }

    #[derive(Debug, Clone)]
    struct NonOrd;
    set(BTreeSet::<NonOrd, _>::new(()));
    set_debug(BTreeSet::<NonOrd, _>::new(()));
    set_clone(BTreeSet::<NonOrd, _>::new(()));
}

#[test]
fn test_append() {
    let mut a = BTreeSet::default();
    a.insert(1);
    a.insert(2);
    a.insert(3);

    let mut b = BTreeSet::default();
    b.insert(3);
    b.insert(4);
    b.insert(5);

    a.append(&mut b);

    assert_eq!(a.len(), 5);
    assert_eq!(b.len(), 0);

    assert!(a.contains(&1));
    assert!(a.contains(&2));
    assert!(a.contains(&3));
    assert!(a.contains(&4));
    assert!(a.contains(&5));
}

#[test]
fn test_first_last() {
    let mut a = BTreeSet::default();
    assert_eq!(a.first(), None);
    assert_eq!(a.last(), None);
    a.insert(1);
    assert_eq!(a.first(), Some(&1));
    assert_eq!(a.last(), Some(&1));
    a.insert(2);
    assert_eq!(a.first(), Some(&1));
    assert_eq!(a.last(), Some(&2));
    for i in 3..=12 {
        a.insert(i);
    }
    assert_eq!(a.first(), Some(&1));
    assert_eq!(a.last(), Some(&12));
    assert_eq!(a.pop_first(), Some(1));
    assert_eq!(a.pop_last(), Some(12));
    assert_eq!(a.pop_first(), Some(2));
    assert_eq!(a.pop_last(), Some(11));
    assert_eq!(a.pop_first(), Some(3));
    assert_eq!(a.pop_last(), Some(10));
    assert_eq!(a.pop_first(), Some(4));
    assert_eq!(a.pop_first(), Some(5));
    assert_eq!(a.pop_first(), Some(6));
    assert_eq!(a.pop_first(), Some(7));
    assert_eq!(a.pop_first(), Some(8));
    assert_eq!(a.clone().pop_last(), Some(9));
    assert_eq!(a.pop_first(), Some(9));
    assert_eq!(a.pop_first(), None);
    assert_eq!(a.pop_last(), None);
}

// Unlike the function with the same name in map/tests, returns no values.
// Which also means it returns different predetermined pseudo-random keys,
// and the test cases using this function explore slightly different trees.
fn rand_data(len: usize) -> Vec<u32> {
    let mut rng = DeterministicRng::new();
    Vec::from_iter((0..len).map(|_| rng.next()))
}

#[test]
fn test_split_off_empty_right() {
    let mut data = rand_data(173);

    let mut set = BTreeSet::from_iter(data.clone());
    let right = set.split_off(&(data.iter().max().unwrap() + 1));

    data.sort();
    assert!(set.into_iter().eq(data));
    assert!(right.into_iter().eq(None));
}

#[test]
fn test_split_off_empty_left() {
    let mut data = rand_data(314);

    let mut set = BTreeSet::from_iter(data.clone());
    let right = set.split_off(data.iter().min().unwrap());

    data.sort();
    assert!(set.into_iter().eq(None));
    assert!(right.into_iter().eq(data));
}

#[test]
fn test_split_off_large_random_sorted() {
    // Miri is too slow
    let mut data = if cfg!(miri) {
        rand_data(529)
    } else {
        rand_data(1529)
    };
    // special case with maximum height.
    data.sort();

    let mut set = BTreeSet::from_iter(data.clone());
    let key = data[data.len() / 2];
    let right = set.split_off(&key);

    assert!(set
        .into_iter()
        .eq(data.clone().into_iter().filter(|x| *x < key)));
    assert!(right.into_iter().eq(data.into_iter().filter(|x| *x >= key)));
}

#[test]
fn from_array() {
    let set = BTreeSet::from([1, 2, 3, 4]);
    let unordered_duplicates = BTreeSet::from([4, 1, 4, 3, 2]);
    assert_eq!(set, unordered_duplicates);
}

#[cfg_attr(
    feature = "specialization",
    should_panic(expected = "range start is greater than range end in BTreeSet")
)]
#[cfg_attr(
    not(feature = "specialization"),
    should_panic(expected = "range start is greater than range end")
)]
#[test]
fn test_range_panic_1() {
    let mut set = BTreeSet::default();
    set.insert(3);
    set.insert(5);
    set.insert(8);

    let _invalid_range = set.range::<i32, _>((Included(&8), Included(&3)));
}

#[cfg_attr(
    feature = "specialization",
    should_panic(expected = "range start and end are equal and excluded in BTreeSet")
)]
#[cfg_attr(
    not(feature = "specialization"),
    should_panic(expected = "range start and end are equal and excluded")
)]
#[test]
fn test_range_panic_2() {
    let mut set = BTreeSet::default();
    set.insert(3);
    set.insert(5);
    set.insert(8);

    let _invalid_range = set.range::<i32, _>((Excluded(&5), Excluded(&5)));
}
