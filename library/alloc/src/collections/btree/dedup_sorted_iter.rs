use core::iter::Peekable;

use contextual_core::{borrow::ContextualBorrow, cmp::ContextualOrd};

/// A iterator for deduping the key of a sorted iterator.
/// When encountering the duplicated key, only the last key-value pair is yielded.
///
/// Used by [`BTreeMap::bulk_build_from_sorted_iter`][1].
///
/// [1]: crate::collections::BTreeMap::bulk_build_from_sorted_iter
pub struct DedupSortedIter<'a, K, V, C, I>
where
    I: Iterator<Item = (K, V)>,
{
    iter: Peekable<I>,
    context: &'a C,
}

impl<'a, K, V, C, I> DedupSortedIter<'a, K, V, C, I>
where
    I: Iterator<Item = (K, V)>,
{
    pub fn new(iter: I, context: &'a C) -> Self {
        Self { iter: iter.peekable(), context }
    }
}

impl<K, V, C, I> Iterator for DedupSortedIter<'_, K, V, C, I>
where
    K: ContextualOrd<C>,
    I: Iterator<Item = (K, V)>,
{
    type Item = (K, V);

    fn next(&mut self) -> Option<(K, V)> {
        loop {
            let next = match self.iter.next() {
                Some(next) => next,
                None => return None,
            };

            let peeked = match self.iter.peek() {
                Some(peeked) => peeked,
                None => return Some(next),
            };

            if next.0.contextual_ne(&peeked.0, self.context) {
                return Some(next);
            }
        }
    }
}
