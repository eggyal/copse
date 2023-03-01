use core::{cmp::Ordering, ops::ControlFlow};

pub trait ControlFlowEnumContinue<B> {
    const CONTINUE: Self;
}

impl<B> ControlFlowEnumContinue<B> for ControlFlow<B, ()> {
    const CONTINUE: Self = ControlFlow::Continue(());
}

pub trait ControlFlowEnumBreak<C> {
    const BREAK: Self;
}

impl<C> ControlFlowEnumBreak<C> for ControlFlow<(), C> {
    const BREAK: Self = ControlFlow::Break(());
}

pub trait ControlFlowEnum<B, C> {
    fn map_break<T, F>(self, f: F) -> ControlFlow<T, C>
    where
        F: FnOnce(B) -> T;
}

impl<B, C> ControlFlowEnum<B, C> for ControlFlow<B, C> {
    fn map_break<T, F>(self, f: F) -> ControlFlow<T, C>
    where
        F: FnOnce(B) -> T,
    {
        match self {
            ControlFlow::Continue(x) => ControlFlow::Continue(x),
            ControlFlow::Break(x) => ControlFlow::Break(f(x)),
        }
    }
}

#[cfg(feature = "is_sorted")]
pub trait IsSorted: Iterator {
    #[allow(clippy::wrong_self_convention)]
    fn is_sorted_by<F>(mut self, compare: F) -> bool
    where
        Self: Sized,
        F: FnMut(&Self::Item, &Self::Item) -> Option<Ordering>,
    {
        #[inline]
        fn check<'a, T>(
            last: &'a mut T,
            mut compare: impl FnMut(&T, &T) -> Option<Ordering> + 'a,
        ) -> impl FnMut(T) -> bool + 'a {
            move |curr| {
                if let Some(Ordering::Greater) | None = compare(last, &curr) {
                    return false;
                }
                *last = curr;
                true
            }
        }

        let mut last = match self.next() {
            Some(e) => e,
            None => return true,
        };

        self.all(check(&mut last, compare))
    }
}

pub trait IterOrderBy: Iterator {
    fn cmp_by<I, F>(self, other: I, cmp: F) -> Ordering
    where
        Self: Sized,
        I: IntoIterator,
        F: FnMut(Self::Item, I::Item) -> Ordering,
    {
        #[inline]
        fn compare<X, Y, F>(mut cmp: F) -> impl FnMut(X, Y) -> ControlFlow<Ordering>
        where
            F: FnMut(X, Y) -> Ordering,
        {
            move |x, y| match cmp(x, y) {
                #[allow(unstable_name_collisions)]
                Ordering::Equal => ControlFlow::CONTINUE,
                non_eq => ControlFlow::Break(non_eq),
            }
        }

        match iter_compare(self, other.into_iter(), compare(cmp)) {
            ControlFlow::Continue(ord) => ord,
            ControlFlow::Break(ord) => ord,
        }
    }

    fn partial_cmp_by<I, F>(self, other: I, partial_cmp: F) -> Option<Ordering>
    where
        Self: Sized,
        I: IntoIterator,
        F: FnMut(Self::Item, I::Item) -> Option<Ordering>,
    {
        #[inline]
        fn compare<X, Y, F>(mut partial_cmp: F) -> impl FnMut(X, Y) -> ControlFlow<Option<Ordering>>
        where
            F: FnMut(X, Y) -> Option<Ordering>,
        {
            move |x, y| match partial_cmp(x, y) {
                #[allow(unstable_name_collisions)]
                Some(Ordering::Equal) => ControlFlow::CONTINUE,
                non_eq => ControlFlow::Break(non_eq),
            }
        }

        match iter_compare(self, other.into_iter(), compare(partial_cmp)) {
            ControlFlow::Continue(ord) => Some(ord),
            ControlFlow::Break(ord) => ord,
        }
    }

    fn eq_by<I, F>(self, other: I, eq: F) -> bool
    where
        Self: Sized,
        I: IntoIterator,
        F: FnMut(Self::Item, I::Item) -> bool,
    {
        #[inline]
        fn compare<X, Y, F>(mut eq: F) -> impl FnMut(X, Y) -> ControlFlow<()>
        where
            F: FnMut(X, Y) -> bool,
        {
            move |x, y| {
                #[allow(unstable_name_collisions)]
                if eq(x, y) { ControlFlow::CONTINUE } else { ControlFlow::BREAK }
            }
        }

        match iter_compare(self, other.into_iter(), compare(eq)) {
            ControlFlow::Continue(ord) => ord == Ordering::Equal,
            ControlFlow::Break(()) => false,
        }
    }
}

#[cfg(feature = "is_sorted")]
impl<I: Iterator> IsSorted for I {}
impl<I: Iterator> IterOrderBy for I {}

#[inline]
fn iter_compare<A, B, F, T>(mut a: A, mut b: B, f: F) -> ControlFlow<T, Ordering>
where
    A: Iterator,
    B: Iterator,
    F: FnMut(A::Item, B::Item) -> ControlFlow<T>,
{
    #[inline]
    fn compare<'a, B, X, T>(
        b: &'a mut B,
        mut f: impl FnMut(X, B::Item) -> ControlFlow<T> + 'a,
    ) -> impl FnMut(X) -> ControlFlow<ControlFlow<T, Ordering>> + 'a
    where
        B: Iterator,
    {
        move |x| match b.next() {
            None => ControlFlow::Break(ControlFlow::Continue(Ordering::Greater)),
            #[allow(unstable_name_collisions)]
            Some(y) => f(x, y).map_break(ControlFlow::Break),
        }
    }

    match a.try_for_each(compare(&mut b, f)) {
        ControlFlow::Continue(()) => ControlFlow::Continue(match b.next() {
            None => Ordering::Equal,
            Some(_) => Ordering::Less,
        }),
        ControlFlow::Break(x) => x,
    }
}
