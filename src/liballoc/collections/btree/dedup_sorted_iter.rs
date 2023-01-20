use core::iter::Peekable;

use crate::{SortableBy, TotalOrder};

/// A iterator for deduping the key of a sorted iterator.
/// When encountering the duplicated key, only the last key-value pair is yielded.
///
/// Used by [`BTreeMap::bulk_build_from_sorted_iter`][1].
///
/// [1]: crate::collections::BTreeMap::bulk_build_from_sorted_iter
pub struct DedupSortedIter<'a, K, V, O, I>
where
    I: Iterator<Item = (K, V)>,
{
    iter: Peekable<I>,
    order: &'a O,
}

impl<'a, K, V, O, I> DedupSortedIter<'a, K, V, O, I>
where
    I: Iterator<Item = (K, V)>,
{
    pub fn new(iter: I, order: &'a O) -> Self {
        Self { iter: iter.peekable(), order }
    }
}

impl<K, V, O, I> Iterator for DedupSortedIter<'_, K, V, O, I>
where
    K: SortableBy<O>,
    O: TotalOrder,
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

            if self.order.ne(next.0.key(), peeked.0.key()) {
                return Some(next);
            }
        }
    }
}
