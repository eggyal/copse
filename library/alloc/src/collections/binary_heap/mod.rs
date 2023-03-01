//! A priority queue implemented with a binary heap.
//!
//! Insertion and popping the largest element have *C*(log(*n*)) time complexity.
//! Checking the largest element is *C*(1). Converting a vector to a binary heap
//! can be done in-place, and has *C*(*n*) complexity. A binary heap can also be
//! converted to a sorted vector in-place, allowing it to be used for an *C*(*n* * log(*n*))
//! in-place heapsort.
//!
//! # Examples
//!
//! This is a larger example that implements [Dijkstra's algorithm][dijkstra]
//! to solve the [shortest path problem][sssp] on a [directed graph][dir_graph].
//! It shows how to use [`BinaryHeap`] with custom types.
//!
//! [dijkstra]: https://en.wikipedia.org/wiki/Dijkstra%27s_algorithm
//! [sssp]: https://en.wikipedia.org/wiki/Shortest_path_problem
//! [dir_graph]: https://en.wikipedia.org/wiki/Directed_graph
//!
//! ```
//! use contextual_alloc::{collections::BinaryHeap, contextual_core::contextual};
//!
//! #[derive(Copy, Clone)]
//! struct State {
//!     cost: usize,
//!     position: usize,
//! }
//!
//! // A reversed-cost order for `State`
//! struct ReversedCostOrder;
//!
//! contextual! {
//!     fn cmp(&self, other: &State, context: &ReversedCostOrder) -> Ordering {
//!         // Notice that we flip the ordering on costs.
//!         other.cost.cmp(&self.cost)
//!     }
//! }
//!
//! // Each node is represented as a `usize`, for a shorter implementation.
//! struct Edge {
//!     node: usize,
//!     cost: usize,
//! }
//!
//! // Dijkstra's shortest path algorithm.
//!
//! // Start at `start` and use `dist` to track the current shortest distance
//! // to each node. This implementation isn't memory-efficient as it may leave duplicate
//! // nodes in the queue. It also uses `usize::MAX` as a sentinel value,
//! // for a simpler implementation.
//! fn shortest_path(adj_list: &Vec<Vec<Edge>>, start: usize, goal: usize) -> Option<usize> {
//!     // dist[node] = current shortest distance from `start` to `node`
//!     let mut dist: Vec<_> = (0..adj_list.len()).map(|_| usize::MAX).collect();
//!
//!     let mut heap = BinaryHeap::new(ReversedCostOrder);
//!
//!     // We're at `start`, with a zero cost
//!     dist[start] = 0;
//!     heap.push(State { cost: 0, position: start });
//!
//!     // Examine the frontier with lower cost nodes first (min-heap)
//!     while let Some(State { cost, position }) = heap.pop() {
//!         // Alternatively we could have continued to find all shortest paths
//!         if position == goal { return Some(cost); }
//!
//!         // Important as we may have already found a better way
//!         if cost > dist[position] { continue; }
//!
//!         // For each node we can reach, see if we can find a way with
//!         // a lower cost going through this node
//!         for edge in &adj_list[position] {
//!             let next = State { cost: cost + edge.cost, position: edge.node };
//!
//!             // If so, add it to the frontier and continue
//!             if next.cost < dist[next.position] {
//!                 heap.push(next);
//!                 // Relaxation, we have now found a better way
//!                 dist[next.position] = next.cost;
//!             }
//!         }
//!     }
//!
//!     // Goal not reachable
//!     None
//! }
//!
//! fn main() {
//!     // This is the directed graph we're going to use.
//!     // The node numbers correspond to the different states,
//!     // and the edge weights symbolize the cost of moving
//!     // from one node to another.
//!     // Note that the edges are one-way.
//!     //
//!     //                  7
//!     //          +-----------------+
//!     //          |                 |
//!     //          v   1        2    |  2
//!     //          0 -----> 1 -----> 3 ---> 4
//!     //          |        ^        ^      ^
//!     //          |        | 1      |      |
//!     //          |        |        | 3    | 1
//!     //          +------> 2 -------+      |
//!     //           10      |               |
//!     //                   +---------------+
//!     //
//!     // The graph is represented as an adjacency list where each index,
//!     // corresponding to a node value, has a list of outgoing edges.
//!     // Chosen for its efficiency.
//!     let graph = vec![
//!         // Node 0
//!         vec![Edge { node: 2, cost: 10 },
//!              Edge { node: 1, cost: 1 }],
//!         // Node 1
//!         vec![Edge { node: 3, cost: 2 }],
//!         // Node 2
//!         vec![Edge { node: 1, cost: 1 },
//!              Edge { node: 3, cost: 3 },
//!              Edge { node: 4, cost: 1 }],
//!         // Node 3
//!         vec![Edge { node: 0, cost: 7 },
//!              Edge { node: 4, cost: 2 }],
//!         // Node 4
//!         vec![]];
//!
//!     assert_eq!(shortest_path(&graph, 0, 1), Some(1));
//!     assert_eq!(shortest_path(&graph, 0, 3), Some(3));
//!     assert_eq!(shortest_path(&graph, 3, 0), Some(7));
//!     assert_eq!(shortest_path(&graph, 0, 4), Some(5));
//!     assert_eq!(shortest_path(&graph, 4, 0), None);
//! }
//! ```

#![allow(missing_docs)]

use core::fmt;
#[cfg(feature = "trusted_len")]
use core::iter::TrustedLen;
use core::iter::{FromIterator, FusedIterator};
#[cfg(feature = "inplace_iteration")]
use core::iter::{InPlaceIterable, SourceIter};
use core::mem::{self, swap, ManuallyDrop};
use core::num::NonZeroUsize;
use core::ops::{Deref, DerefMut};
use core::ptr;

use alloc::collections::TryReserveError;
use alloc::slice;
use alloc::vec::{self, Vec};
use cfg_if::cfg_if;

use super::SpecExtend;
use contextual_core::{borrow::ContextualBorrow, prelude::*};

#[cfg(test)]
mod tests;

/// A priority queue implemented with a binary heap.
///
/// This will be a max-heap.
///
/// It is a logic error for an item or runtime context to be modified (except via the
/// [`context_mut`] method) in such a way  that the item's ordering relative to any
/// other item, as determined by that runtime context, changes while they are in the
/// heap. This is normally only possible through the [`context_mut_unchecked`] method,
/// interior mutability, global state, I/O, or unsafe code. The behavior resulting
/// from such a logic error is not specified, but will be encapsulated to the
/// `BinaryHeap` that observed the logic error and not result in undefined behavior.
/// This could include panics, incorrect results, aborts, memory leaks, and
/// non-termination.
///
/// As long as no elements change their relative order while being in the heap
/// as described above, the API of `BinaryHeap` guarantees that the heap
/// invariant remains intact i.e. its methods all behave as documented. For
/// example if a method is documented as iterating in sorted order, that's
/// guaranteed to work as long as elements in the heap have not changed order,
/// even in the presence of closures getting unwinded out of, iterators getting
/// leaked, and similar foolishness.
///
/// # Examples
///
/// ```
/// use contextual_alloc::collections::BinaryHeap;
///
/// // Type inference lets us omit an explicit type signature (which
/// // would be `BinaryHeap<i32, OrdTotalOrder<i32>>` in this example).
/// let mut heap = BinaryHeap::default();
///
/// // We can use peek to look at the next item in the heap. In this case,
/// // there's no items in there yet so we get None.
/// assert_eq!(heap.peek(), None);
///
/// // Let's add some scores...
/// heap.push(1);
/// heap.push(5);
/// heap.push(2);
///
/// // Now peek shows the most important item in the heap.
/// assert_eq!(heap.peek(), Some(&5));
///
/// // We can check the length of a heap.
/// assert_eq!(heap.len(), 3);
///
/// // We can iterate over the items in the heap, although they are returned in
/// // a random order.
/// for x in &heap {
///     println!("{x}");
/// }
///
/// // If we instead pop these scores, they should come back in order.
/// assert_eq!(heap.pop(), Some(5));
/// assert_eq!(heap.pop(), Some(2));
/// assert_eq!(heap.pop(), Some(1));
/// assert_eq!(heap.pop(), None);
///
/// // We can clear the heap of any remaining items.
/// heap.clear();
///
/// // The heap should now be empty.
/// assert!(heap.is_empty())
/// ```
///
/// A `BinaryHeap` with a known list of items can be initialized from an array:
///
/// ```
/// use contextual_alloc::collections::BinaryHeap;
///
/// let heap = BinaryHeap::from([1, 5, 2]);
/// ```
///
/// ## Min-heap
///
/// Either [`core::cmp::Reverse`], a custom [`Ord`] implementation or a custom
/// runtime context implementation can be used to make `BinaryHeap` a min-heap.
/// This makes `heap.pop()` return the smallest value instead of the greatest one.
///
/// ```
/// use contextual_alloc::{collections::BinaryHeap, contextual_core::contextual};
///
/// struct ReversedOrder;
///
/// contextual! {
///     fn cmp(&self, other: &i32, context: &ReversedOrder) -> Ordering {
///         other.cmp(self)
///     }
/// }
///
/// let mut heap = BinaryHeap::new(ReversedOrder);
///
/// heap.push(1);
/// heap.push(5);
/// heap.push(2);
///
/// // If we pop these scores now, they should come back in the reverse order.
/// assert_eq!(heap.pop(), Some(1));
/// assert_eq!(heap.pop(), Some(2));
/// assert_eq!(heap.pop(), Some(5));
/// assert_eq!(heap.pop(), None);
/// ```
///
/// # Time complexity
///
/// | [push]  | [pop]         | [peek]/[peek\_mut] |
/// |---------|---------------|--------------------|
/// | *C*(1)~ | *C*(log(*n*)) | *C*(1)             |
///
/// The value for `push` is an expected cost; the method documentation gives a
/// more detailed analysis.
///
/// [`context_mut`]: Self::context_mut
/// [`context_mut_unchecked`]: Self::context_mut_unchecked
/// [`core::cmp::Reverse`]: core::cmp::Reverse
/// [`Ord`]: core::cmp::Ord
/// [`Cell`]: core::cell::Cell
/// [`RefCell`]: core::cell::RefCell
/// [push]: BinaryHeap::push
/// [pop]: BinaryHeap::pop
/// [peek]: BinaryHeap::peek
/// [peek\_mut]: BinaryHeap::peek_mut
pub struct BinaryHeap<T, C = NoContext> {
    data: Vec<T>,
    context: C,
}

/// Structure wrapping a mutable reference to the greatest item on a
/// `BinaryHeap`.
///
/// This `struct` is created by the [`peek_mut`] method on [`BinaryHeap`]. See
/// its documentation for more.
///
/// [`peek_mut`]: BinaryHeap::peek_mut
pub struct PeekMut<'a, T: 'a + ContextualOrd<C>, C = NoContext> {
    heap: &'a mut BinaryHeap<T, C>,
    // If a set_len + sift_down are required, this is Some. If a &mut T has not
    // yet been exposed to peek_mut()'s caller, it's None.
    original_len: Option<NonZeroUsize>,
}

impl<T: ContextualOrd<C> + fmt::Debug, C> fmt::Debug for PeekMut<'_, T, C> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_tuple("PeekMut").field(&self.heap.data[0]).finish()
    }
}

impl<T: ContextualOrd<C>, C> Drop for PeekMut<'_, T, C> {
    fn drop(&mut self) {
        if let Some(original_len) = self.original_len {
            // SAFETY: That's how many elements were in the Vec at the time of
            // the PeekMut::deref_mut call, and therefore also at the time of
            // the BinaryHeap::peek_mut call. Since the PeekMut did not end up
            // getting leaked, we are now undoing the leak amplification that
            // the DerefMut prepared for.
            unsafe { self.heap.data.set_len(original_len.get()) };

            // SAFETY: PeekMut is only instantiated for non-empty heaps.
            unsafe { self.heap.sift_down(0) };
        }
    }
}

impl<T: ContextualOrd<C>, C> Deref for PeekMut<'_, T, C> {
    type Target = T;
    fn deref(&self) -> &T {
        debug_assert!(!self.heap.is_empty());
        // SAFE: PeekMut is only instantiated for non-empty heaps
        unsafe { self.heap.data.get_unchecked(0) }
    }
}

impl<T: ContextualOrd<C>, C> DerefMut for PeekMut<'_, T, C> {
    fn deref_mut(&mut self) -> &mut T {
        debug_assert!(!self.heap.is_empty());

        let len = self.heap.len();
        if len > 1 {
            // Here we preemptively leak all the rest of the underlying vector
            // after the currently max element. If the caller mutates the &mut T
            // we're about to give them, and then leaks the PeekMut, all these
            // elements will remain leaked. If they don't leak the PeekMut, then
            // either Drop or PeekMut::pop will un-leak the vector elements.
            //
            // This is technique is described throughout several other places in
            // the standard library as "leak amplification".
            unsafe {
                // SAFETY: len > 1 so len != 0.
                self.original_len = Some(NonZeroUsize::new_unchecked(len));
                // SAFETY: len > 1 so all this does for now is leak elements,
                // which is safe.
                self.heap.data.set_len(1);
            }
        }

        // SAFE: PeekMut is only instantiated for non-empty heaps
        unsafe { self.heap.data.get_unchecked_mut(0) }
    }
}

impl<'a, T: ContextualOrd<C>, C> PeekMut<'a, T, C> {
    /// Removes the peeked value from the heap and returns it.
    pub fn pop(mut this: PeekMut<'a, T, C>) -> T {
        if let Some(original_len) = this.original_len.take() {
            // SAFETY: This is how many elements were in the Vec at the time of
            // the BinaryHeap::peek_mut call.
            unsafe { this.heap.data.set_len(original_len.get()) };

            // Unlike in Drop, here we don't also need to do a sift_down even if
            // the caller could've mutated the element. It is removed from the
            // heap on the next line and pop() is not sensitive to its value.
        }
        this.heap.pop().unwrap()
    }
}

impl<T: Clone, C: Clone> Clone for BinaryHeap<T, C> {
    fn clone(&self) -> Self {
        BinaryHeap { data: self.data.clone(), context: self.context.clone() }
    }

    fn clone_from(&mut self, source: &Self) {
        self.data.clone_from(&source.data);
    }
}

impl<T: ContextualOrd<C>, C: Default> Default for BinaryHeap<T, C> {
    /// Creates an empty `BinaryHeap<T>`.
    #[inline]
    fn default() -> BinaryHeap<T, C> {
        BinaryHeap::new(C::default())
    }
}

impl<T: fmt::Debug, C> fmt::Debug for BinaryHeap<T, C> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_list().entries(self.iter()).finish()
    }
}

impl<T: ContextualOrd<C>, C> BinaryHeap<T, C> {
    /// Creates an empty `BinaryHeap` as a max-heap.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// use contextual_alloc::collections::BinaryHeap;
    /// let mut heap = BinaryHeap::default();
    /// heap.push(4);
    /// ```
    #[must_use]
    pub fn new(context: C) -> BinaryHeap<T, C> {
        BinaryHeap { data: vec![], context }
    }

    /// Creates an empty `BinaryHeap` with at least the specified capacity.
    ///
    /// The binary heap will be able to hold at least `capacity` elements without
    /// reallocating. This method is allowed to allocate for more elements than
    /// `capacity`. If `capacity` is 0, the binary heap will not allocate.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// use contextual_alloc::collections::BinaryHeap;
    /// let mut heap = BinaryHeap::with_capacity(Default::default(), 10);
    /// heap.push(4);
    /// ```
    #[must_use]
    pub fn with_capacity(context: C, capacity: usize) -> BinaryHeap<T, C> {
        BinaryHeap { data: Vec::with_capacity(capacity), context }
    }

    /// Returns a mutable reference to the greatest item in the binary heap, or
    /// `None` if it is empty.
    ///
    /// Note: If the `PeekMut` value is leaked, some heap elements might get
    /// leaked along with it, but the remaining elements will remain a valid
    /// heap.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// use contextual_alloc::collections::BinaryHeap;
    /// let mut heap = BinaryHeap::default();
    /// assert!(heap.peek_mut().is_none());
    ///
    /// heap.push(1);
    /// heap.push(5);
    /// heap.push(2);
    /// {
    ///     let mut val = heap.peek_mut().unwrap();
    ///     *val = 0;
    /// }
    /// assert_eq!(heap.peek(), Some(&2));
    /// ```
    ///
    /// # Time complexity
    ///
    /// If the item is modified then the worst case time complexity is *C*(log(*n*)),
    /// otherwise it's *C*(1).
    pub fn peek_mut(&mut self) -> Option<PeekMut<'_, T, C>> {
        if self.is_empty() { None } else { Some(PeekMut { heap: self, original_len: None }) }
    }

    /// Removes the greatest item from the binary heap and returns it, or `None` if it
    /// is empty.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// use contextual_alloc::collections::BinaryHeap;
    /// let mut heap = BinaryHeap::from([1, 3]);
    ///
    /// assert_eq!(heap.pop(), Some(3));
    /// assert_eq!(heap.pop(), Some(1));
    /// assert_eq!(heap.pop(), None);
    /// ```
    ///
    /// # Time complexity
    ///
    /// The worst case cost of `pop` on a heap containing *n* elements is *C*(log(*n*)).
    pub fn pop(&mut self) -> Option<T> {
        self.data.pop().map(|mut item| {
            if !self.is_empty() {
                swap(&mut item, &mut self.data[0]);
                // SAFETY: !self.is_empty() means that self.len() > 0
                unsafe { self.sift_down_to_bottom(0) };
            }
            item
        })
    }

    /// Pushes an item onto the binary heap.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// use contextual_alloc::collections::BinaryHeap;
    /// let mut heap = BinaryHeap::default();
    /// heap.push(3);
    /// heap.push(5);
    /// heap.push(1);
    ///
    /// assert_eq!(heap.len(), 3);
    /// assert_eq!(heap.peek(), Some(&5));
    /// ```
    ///
    /// # Time complexity
    ///
    /// The expected cost of `push`, averaged over every possible ordering of
    /// the elements being pushed, and over a sufficiently large number of
    /// pushes, is *C*(1). This is the most meaningful cost metric when pushing
    /// elements that are *not* already in any sorted pattern.
    ///
    /// The time complexity degrades if elements are pushed in predominantly
    /// ascending order. In the worst case, elements are pushed in ascending
    /// sorted order and the amortized cost per push is *C*(log(*n*)) against a heap
    /// containing *n* elements.
    ///
    /// The worst case cost of a *single* call to `push` is *C*(*n*). The worst case
    /// occurs when capacity is exhausted and needs a resize. The resize cost
    /// has been amortized in the previous figures.
    pub fn push(&mut self, item: T) {
        let old_len = self.len();
        self.data.push(item);
        // SAFETY: Since we pushed a new item it means that
        //  old_len = self.len() - 1 < self.len()
        unsafe { self.sift_up(0, old_len) };
    }

    /// Consumes the `BinaryHeap` and returns a vector in sorted
    /// (ascending) order.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// use contextual_alloc::collections::BinaryHeap;
    ///
    /// let mut heap = BinaryHeap::from([1, 2, 4, 5, 7]);
    /// heap.push(6);
    /// heap.push(3);
    ///
    /// let vec = heap.into_sorted_vec();
    /// assert_eq!(vec, [1, 2, 3, 4, 5, 6, 7]);
    /// ```
    #[must_use = "`self` will be dropped if the result is not used"]
    pub fn into_sorted_vec(mut self) -> Vec<T> {
        let mut end = self.len();
        while end > 1 {
            end -= 1;
            // SAFETY: `end` goes from `self.len() - 1` to 1 (both included),
            //  so it's always a valid index to access.
            //  It is safe to access index 0 (i.e. `ptr`), because
            //  1 <= end < self.len(), which means self.len() >= 2.
            unsafe {
                let ptr = self.data.as_mut_ptr();
                ptr::swap(ptr, ptr.add(end));
            }
            // SAFETY: `end` goes from `self.len() - 1` to 1 (both included) so:
            //  0 < 1 <= end <= self.len() - 1 < self.len()
            //  Which means 0 < end and end < self.len().
            unsafe { self.sift_down_range(0, end) };
        }
        self.into_vec()
    }

    // The implementations of sift_up and sift_down use unsafe blocks in
    // order to move an element out of the vector (leaving behind a
    // hole), shift along the others and move the removed element back into the
    // vector at the final location of the hole.
    // The `Hole` type is used to represent this, and make sure
    // the hole is filled back at the end of its scope, even on panic.
    // Using a hole reduces the constant factor compared to using swaps,
    // which involves twice as many moves.

    /// # Safety
    ///
    /// The caller must guarantee that `pos < self.len()`.
    unsafe fn sift_up(&mut self, start: usize, pos: usize) -> usize {
        // Take out the value at `pos` and create a hole.
        // SAFETY: The caller guarantees that pos < self.len()
        let mut hole = unsafe { Hole::new(&mut self.data, pos) };

        while hole.pos() > start {
            let parent = (hole.pos() - 1) / 2;

            // SAFETY: hole.pos() > start >= 0, which means hole.pos() > 0
            //  and so hole.pos() - 1 can't underflow.
            //  This guarantees that parent < hole.pos() so
            //  it's a valid index and also != hole.pos().
            if hole.element().contextual_le(unsafe { hole.get(parent) }, &self.context) {
                break;
            }

            // SAFETY: Same as above
            unsafe { hole.move_to(parent) };
        }

        hole.pos()
    }

    /// Take an element at `pos` and move it down the heap,
    /// while its children are larger.
    ///
    /// # Safety
    ///
    /// The caller must guarantee that `pos < end <= self.len()`.
    unsafe fn sift_down_range(&mut self, pos: usize, end: usize) {
        // SAFETY: The caller guarantees that pos < end <= self.len().
        let mut hole = unsafe { Hole::new(&mut self.data, pos) };
        let mut child = 2 * hole.pos() + 1;

        // Loop invariant: child == 2 * hole.pos() + 1.
        while child <= end.saturating_sub(2) {
            // compare with the greater of the two children
            // SAFETY: child < end - 1 < self.len() and
            //  child + 1 < end <= self.len(), so they're valid indexes.
            //  child == 2 * hole.pos() + 1 != hole.pos() and
            //  child + 1 == 2 * hole.pos() + 2 != hole.pos().
            // FIXME: 2 * hole.pos() + 1 or 2 * hole.pos() + 2 could overflow
            //  if T is a ZST
            child += unsafe { hole.get(child).contextual_le(hole.get(child + 1), &self.context) }
                as usize;

            // if we are already in order, stop.
            // SAFETY: child is now either the old child or the old child+1
            //  We already proven that both are < self.len() and != hole.pos()
            if hole.element().contextual_ge(unsafe { hole.get(child) }, &self.context) {
                return;
            }

            // SAFETY: same as above.
            unsafe { hole.move_to(child) };
            child = 2 * hole.pos() + 1;
        }

        // SAFETY: && short circuit, which means that in the
        //  second condition it's already true that child == end - 1 < self.len().
        if child == end - 1
            && hole.element().contextual_lt(unsafe { hole.get(child) }, &self.context)
        {
            // SAFETY: child is already proven to be a valid index and
            //  child == 2 * hole.pos() + 1 != hole.pos().
            unsafe { hole.move_to(child) };
        }
    }

    /// # Safety
    ///
    /// The caller must guarantee that `pos < self.len()`.
    unsafe fn sift_down(&mut self, pos: usize) {
        let len = self.len();
        // SAFETY: pos < len is guaranteed by the caller and
        //  obviously len = self.len() <= self.len().
        unsafe { self.sift_down_range(pos, len) };
    }

    /// Take an element at `pos` and move it all the way down the heap,
    /// then sift it up to its position.
    ///
    /// Note: This is faster when the element is known to be large / should
    /// be closer to the bottom.
    ///
    /// # Safety
    ///
    /// The caller must guarantee that `pos < self.len()`.
    unsafe fn sift_down_to_bottom(&mut self, mut pos: usize) {
        let end = self.len();
        let start = pos;

        // SAFETY: The caller guarantees that pos < self.len().
        let mut hole = unsafe { Hole::new(&mut self.data, pos) };
        let mut child = 2 * hole.pos() + 1;

        // Loop invariant: child == 2 * hole.pos() + 1.
        while child <= end.saturating_sub(2) {
            // SAFETY: child < end - 1 < self.len() and
            //  child + 1 < end <= self.len(), so they're valid indexes.
            //  child == 2 * hole.pos() + 1 != hole.pos() and
            //  child + 1 == 2 * hole.pos() + 2 != hole.pos().
            // FIXME: 2 * hole.pos() + 1 or 2 * hole.pos() + 2 could overflow
            //  if T is a ZST
            child += unsafe { hole.get(child).contextual_le(hole.get(child + 1), &self.context) }
                as usize;

            // SAFETY: Same as above
            unsafe { hole.move_to(child) };
            child = 2 * hole.pos() + 1;
        }

        if child == end - 1 {
            // SAFETY: child == end - 1 < self.len(), so it's a valid index
            //  and child == 2 * hole.pos() + 1 != hole.pos().
            unsafe { hole.move_to(child) };
        }
        pos = hole.pos();
        drop(hole);

        // SAFETY: pos is the position in the hole and was already proven
        //  to be a valid index.
        unsafe { self.sift_up(start, pos) };
    }

    /// Rebuild assuming data[0..start] is still a proper heap.
    fn rebuild_tail(&mut self, start: usize) {
        if start == self.len() {
            return;
        }

        let tail_len = self.len() - start;

        #[inline(always)]
        fn log2_fast(x: usize) -> usize {
            (usize::BITS - x.leading_zeros() - 1) as usize
        }

        // `rebuild` takes C(self.len()) operations
        // and about 2 * self.len() comparisons in the worst case
        // while repeating `sift_up` takes C(tail_len * log(start)) operations
        // and about 1 * tail_len * log_2(start) comparisons in the worst case,
        // assuming start >= tail_len. For larger heaps, the crossover point
        // no longer follows this reasoning and was determined empirically.
        let better_to_rebuild = if start < tail_len {
            true
        } else if self.len() <= 2048 {
            2 * self.len() < tail_len * log2_fast(start)
        } else {
            2 * self.len() < tail_len * 11
        };

        if better_to_rebuild {
            self.rebuild();
        } else {
            for i in start..self.len() {
                // SAFETY: The index `i` is always less than self.len().
                unsafe { self.sift_up(0, i) };
            }
        }
    }

    fn rebuild(&mut self) {
        let mut n = self.len() / 2;
        while n > 0 {
            n -= 1;
            // SAFETY: n starts from self.len() / 2 and goes down to 0.
            //  The only case when !(n < self.len()) is if
            //  self.len() == 0, but it's ruled out by the loop condition.
            unsafe { self.sift_down(n) };
        }
    }

    /// Moves all the elements of `other` into `self`, leaving `other` empty.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// use contextual_alloc::collections::BinaryHeap;
    ///
    /// let mut a = BinaryHeap::from([-10, 1, 2, 3, 3]);
    /// let mut b = BinaryHeap::from([-20, 5, 43]);
    ///
    /// a.append(&mut b);
    ///
    /// assert_eq!(a.into_sorted_vec(), [-20, -10, 1, 2, 3, 3, 5, 43]);
    /// assert!(b.is_empty());
    /// ```
    pub fn append(&mut self, other: &mut Self) {
        if self.len() < other.len() {
            swap(self, other);
        }

        let start = self.data.len();

        self.data.append(&mut other.data);

        self.rebuild_tail(start);
    }

    /// Clears the binary heap, returning an iterator over the removed elements
    /// in heap order. If the iterator is dropped before being fully consumed,
    /// it drops the remaining elements in heap order.
    ///
    /// The returned iterator keeps a mutable borrow on the heap to optimize
    /// its implementation.
    ///
    /// Note:
    /// * `.drain_sorted()` is *C*(*n* \* log(*n*)); much slower than `.drain()`.
    ///   You should use the latter for most cases.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// use contextual_alloc::collections::BinaryHeap;
    ///
    /// let mut heap = BinaryHeap::from([1, 2, 3, 4, 5]);
    /// assert_eq!(heap.len(), 5);
    ///
    /// drop(heap.drain_sorted()); // removes all elements in heap order
    /// assert_eq!(heap.len(), 0);
    /// ```
    #[inline]
    #[cfg(feature = "binary_heap_drain_sorted")]
    pub fn drain_sorted(&mut self) -> DrainSorted<'_, T, C> {
        DrainSorted { inner: self }
    }

    /// Retains only the elements specified by the predicate.
    ///
    /// In other words, remove all elements `e` for which `f(&e)` returns
    /// `false`. The elements are visited in unsorted (and unspecified) order.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// use contextual_alloc::collections::BinaryHeap;
    ///
    /// let mut heap = BinaryHeap::from([-10, -5, 1, 2, 4, 13]);
    ///
    /// heap.retain(|x| x % 2 == 0); // only keep even numbers
    ///
    /// assert_eq!(heap.into_sorted_vec(), [-10, 2, 4])
    /// ```
    #[cfg(feature = "binary_heap_retain")]
    pub fn retain<F>(&mut self, mut f: F)
    where
        F: FnMut(&T) -> bool,
    {
        struct RebuildOnDrop<'a, T: ContextualOrd<C>, C = NoContext> {
            heap: &'a mut BinaryHeap<T, C>,
            first_removed: usize,
        }

        let mut guard = RebuildOnDrop { first_removed: self.len(), heap: self };

        let mut i = 0;
        guard.heap.data.retain(|e| {
            let keep = f(e);
            if !keep && i < guard.first_removed {
                guard.first_removed = i;
            }
            i += 1;
            keep
        });

        impl<'a, T: ContextualOrd<C>, C> Drop for RebuildOnDrop<'a, T, C> {
            fn drop(&mut self) {
                // data[..first_removed] is untouched, so we only need to
                // rebuild the tail:
                self.heap.rebuild_tail(self.first_removed);
            }
        }
    }

    /// Borrow this heap's context.
    pub fn context(&self) -> &C {
        &self.context
    }

    /// Mutably borrow this heap's context.  When the returned guard is dropped, the
    /// heap will be rebuilt.
    pub fn context_mut(&mut self) -> ContextMut<'_, T, C> {
        ContextMut(self)
    }

    /// Mutably borrow this heap's context.  It is a logic error for the context to be
    /// modified in a way that changes the relative ordering of any two items contained
    /// in the heap.  The behavior resulting from such a logic error is not specified,
    /// but will be encapsulated to the `BinaryHeap` that observed the logic error and
    /// not result in undefined behavior. This could include panics, incorrect results,
    /// aborts, memory leaks, and non-termination.
    ///
    /// If the context might be modified in such a way, consider using [`context_mut`]
    /// instead, which will reorder the heap once the guard is dropped so as to uphold
    /// its invariants.
    ///
    /// [`context_mut`]: Self::context_mut
    pub fn context_mut_unchecked(&mut self) -> &mut C {
        &mut self.context
    }
}

#[doc(hidden)]
pub struct ContextMut<'a, T: ContextualOrd<C>, C = NoContext>(&'a mut BinaryHeap<T, C>);

impl<T: ContextualOrd<C>, C> Deref for ContextMut<'_, T, C> {
    type Target = C;
    fn deref(&self) -> &Self::Target {
        &self.0.context
    }
}

impl<T: ContextualOrd<C>, C> DerefMut for ContextMut<'_, T, C> {
    fn deref_mut(&mut self) -> &mut Self::Target {
        &mut self.0.context
    }
}

impl<T: ContextualOrd<C>, C> Drop for ContextMut<'_, T, C> {
    fn drop(&mut self) {
        self.0.rebuild()
    }
}

impl<T, C> BinaryHeap<T, C> {
    /// Returns an iterator visiting all values in the underlying vector, in
    /// arbitrary order.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// use contextual_alloc::collections::BinaryHeap;
    /// let heap = BinaryHeap::from([1, 2, 3, 4]);
    ///
    /// // Print 1, 2, 3, 4 in arbitrary order
    /// for x in heap.iter() {
    ///     println!("{x}");
    /// }
    /// ```
    pub fn iter(&self) -> Iter<'_, T> {
        Iter { iter: self.data.iter() }
    }

    /// Returns an iterator which retrieves elements in heap order.
    /// This method consumes the original heap.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// use contextual_alloc::collections::BinaryHeap;
    /// let heap = BinaryHeap::from([1, 2, 3, 4, 5]);
    ///
    /// assert_eq!(heap.into_iter_sorted().take(2).collect::<Vec<_>>(), [5, 4]);
    /// ```
    #[cfg(feature = "binary_heap_into_iter_sorted")]
    pub fn into_iter_sorted(self) -> IntoIterSorted<T, C> {
        IntoIterSorted { inner: self }
    }

    /// Returns the greatest item in the binary heap, or `None` if it is empty.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// use contextual_alloc::collections::BinaryHeap;
    /// let mut heap = BinaryHeap::default();
    /// assert_eq!(heap.peek(), None);
    ///
    /// heap.push(1);
    /// heap.push(5);
    /// heap.push(2);
    /// assert_eq!(heap.peek(), Some(&5));
    ///
    /// ```
    ///
    /// # Time complexity
    ///
    /// Cost is *C*(1) in the worst case.
    #[must_use]
    pub fn peek(&self) -> Option<&T> {
        self.data.get(0)
    }

    /// Returns the number of elements the binary heap can hold without reallocating.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// use contextual_alloc::collections::BinaryHeap;
    /// let mut heap = BinaryHeap::with_capacity(Default::default(), 100);
    /// assert!(heap.capacity() >= 100);
    /// heap.push(4);
    /// ```
    #[must_use]
    pub fn capacity(&self) -> usize {
        self.data.capacity()
    }

    /// Reserves the minimum capacity for at least `additional` elements more than
    /// the current length. Unlike [`reserve`], this will not
    /// deliberately over-allocate to speculatively avoid frequent allocations.
    /// After calling `reserve_exact`, capacity will be greater than or equal to
    /// `self.len() + additional`. Does nothing if the capacity is already
    /// sufficient.
    ///
    /// [`reserve`]: BinaryHeap::reserve
    ///
    /// # Panics
    ///
    /// Panics if the new capacity overflows [`usize`].
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// use contextual_alloc::collections::BinaryHeap;
    /// let mut heap = BinaryHeap::default();
    /// heap.reserve_exact(100);
    /// assert!(heap.capacity() >= 100);
    /// heap.push(4);
    /// ```
    ///
    /// [`reserve`]: BinaryHeap::reserve
    pub fn reserve_exact(&mut self, additional: usize) {
        self.data.reserve_exact(additional);
    }

    /// Reserves capacity for at least `additional` elements more than the
    /// current length. The allocator may reserve more space to speculatively
    /// avoid frequent allocations. After calling `reserve`,
    /// capacity will be greater than or equal to `self.len() + additional`.
    /// Does nothing if capacity is already sufficient.
    ///
    /// # Panics
    ///
    /// Panics if the new capacity overflows [`usize`].
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// use contextual_alloc::collections::BinaryHeap;
    /// let mut heap = BinaryHeap::default();
    /// heap.reserve(100);
    /// assert!(heap.capacity() >= 100);
    /// heap.push(4);
    /// ```
    pub fn reserve(&mut self, additional: usize) {
        self.data.reserve(additional);
    }

    /// Tries to reserve the minimum capacity for at least `additional` elements
    /// more than the current length. Unlike [`try_reserve`], this will not
    /// deliberately over-allocate to speculatively avoid frequent allocations.
    /// After calling `try_reserve_exact`, capacity will be greater than or
    /// equal to `self.len() + additional` if it returns `Ok(())`.
    /// Does nothing if the capacity is already sufficient.
    ///
    /// Note that the allocator may give the collection more space than it
    /// requests. Therefore, capacity can not be relied upon to be precisely
    /// minimal. Prefer [`try_reserve`] if future insertions are expected.
    ///
    /// [`try_reserve`]: BinaryHeap::try_reserve
    ///
    /// # Errors
    ///
    /// If the capacity overflows, or the allocator reports a failure, then an error
    /// is returned.
    ///
    /// # Examples
    ///
    /// ```
    /// use contextual_alloc::collections::BinaryHeap;
    /// use std::collections::TryReserveError;
    ///
    /// fn find_max_slow(data: &[u32]) -> Result<Option<u32>, TryReserveError> {
    ///     let mut heap = BinaryHeap::default();
    ///
    ///     // Pre-reserve the memory, exiting if we can't
    ///     heap.try_reserve_exact(data.len())?;
    ///
    ///     // Now we know this can't OOM in the middle of our complex work
    ///     heap.extend(data.iter());
    ///
    ///     Ok(heap.pop())
    /// }
    /// # find_max_slow(&[1, 2, 3]).expect("why is the test harness OOMing on 12 bytes?");
    /// ```
    pub fn try_reserve_exact(&mut self, additional: usize) -> Result<(), TryReserveError> {
        self.data.try_reserve_exact(additional)
    }

    /// Tries to reserve capacity for at least `additional` elements more than the
    /// current length. The allocator may reserve more space to speculatively
    /// avoid frequent allocations. After calling `try_reserve`, capacity will be
    /// greater than or equal to `self.len() + additional` if it returns
    /// `Ok(())`. Does nothing if capacity is already sufficient. This method
    /// preserves the contents even if an error occurs.
    ///
    /// # Errors
    ///
    /// If the capacity overflows, or the allocator reports a failure, then an error
    /// is returned.
    ///
    /// # Examples
    ///
    /// ```
    /// use contextual_alloc::collections::BinaryHeap;
    /// use std::collections::TryReserveError;
    ///
    /// fn find_max_slow(data: &[u32]) -> Result<Option<u32>, TryReserveError> {
    ///     let mut heap = BinaryHeap::default();
    ///
    ///     // Pre-reserve the memory, exiting if we can't
    ///     heap.try_reserve(data.len())?;
    ///
    ///     // Now we know this can't OOM in the middle of our complex work
    ///     heap.extend(data.iter());
    ///
    ///     Ok(heap.pop())
    /// }
    /// # find_max_slow(&[1, 2, 3]).expect("why is the test harness OOMing on 12 bytes?");
    /// ```
    pub fn try_reserve(&mut self, additional: usize) -> Result<(), TryReserveError> {
        self.data.try_reserve(additional)
    }

    /// Discards as much additional capacity as possible.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// use contextual_alloc::collections::BinaryHeap;
    /// let mut heap: BinaryHeap<i32> = BinaryHeap::with_capacity(Default::default(), 100);
    ///
    /// assert!(heap.capacity() >= 100);
    /// heap.shrink_to_fit();
    /// assert!(heap.capacity() == 0);
    /// ```
    pub fn shrink_to_fit(&mut self) {
        self.data.shrink_to_fit();
    }

    /// Discards capacity with a lower bound.
    ///
    /// The capacity will remain at least as large as both the length
    /// and the supplied value.
    ///
    /// If the current capacity is less than the lower limit, this is a no-op.
    ///
    /// # Examples
    ///
    /// ```
    /// use contextual_alloc::collections::BinaryHeap;
    /// let mut heap: BinaryHeap<i32> = BinaryHeap::with_capacity(Default::default(), 100);
    ///
    /// assert!(heap.capacity() >= 100);
    /// heap.shrink_to(10);
    /// assert!(heap.capacity() >= 10);
    /// ```
    #[inline]
    pub fn shrink_to(&mut self, min_capacity: usize) {
        self.data.shrink_to(min_capacity)
    }

    /// Returns a slice of all values in the underlying vector, in arbitrary
    /// order.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// use contextual_alloc::collections::BinaryHeap;
    /// use std::io::{self, Write};
    ///
    /// let heap = BinaryHeap::from([1, 2, 3, 4, 5, 6, 7]);
    ///
    /// io::sink().write(heap.as_slice()).unwrap();
    /// ```
    #[must_use]
    #[cfg(feature = "binary_heap_as_slice")]
    pub fn as_slice(&self) -> &[T] {
        self.data.as_slice()
    }

    /// Consumes the `BinaryHeap` and returns the underlying vector
    /// in arbitrary order.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// use contextual_alloc::collections::BinaryHeap;
    /// let heap = BinaryHeap::from([1, 2, 3, 4, 5, 6, 7]);
    /// let vec = heap.into_vec();
    ///
    /// // Will print in some order
    /// for x in vec {
    ///     println!("{x}");
    /// }
    /// ```
    #[must_use = "`self` will be dropped if the result is not used"]
    pub fn into_vec(self) -> Vec<T> {
        self.into()
    }

    /// Returns the length of the binary heap.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// use contextual_alloc::collections::BinaryHeap;
    /// let heap = BinaryHeap::from([1, 3]);
    ///
    /// assert_eq!(heap.len(), 2);
    /// ```
    #[must_use]
    pub fn len(&self) -> usize {
        self.data.len()
    }

    /// Checks if the binary heap is empty.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// use contextual_alloc::collections::BinaryHeap;
    /// let mut heap = BinaryHeap::default();
    ///
    /// assert!(heap.is_empty());
    ///
    /// heap.push(3);
    /// heap.push(5);
    /// heap.push(1);
    ///
    /// assert!(!heap.is_empty());
    /// ```
    #[must_use]
    pub fn is_empty(&self) -> bool {
        self.len() == 0
    }

    /// Clears the binary heap, returning an iterator over the removed elements
    /// in arbitrary order. If the iterator is dropped before being fully
    /// consumed, it drops the remaining elements in arbitrary order.
    ///
    /// The returned iterator keeps a mutable borrow on the heap to optimize
    /// its implementation.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// use contextual_alloc::collections::BinaryHeap;
    /// let mut heap = BinaryHeap::from([1, 3]);
    ///
    /// assert!(!heap.is_empty());
    ///
    /// for x in heap.drain() {
    ///     println!("{x}");
    /// }
    ///
    /// assert!(heap.is_empty());
    /// ```
    #[inline]
    pub fn drain(&mut self) -> Drain<'_, T> {
        Drain { iter: self.data.drain(..) }
    }

    /// Drops all items from the binary heap.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// use contextual_alloc::collections::BinaryHeap;
    /// let mut heap = BinaryHeap::from([1, 3]);
    ///
    /// assert!(!heap.is_empty());
    ///
    /// heap.clear();
    ///
    /// assert!(heap.is_empty());
    /// ```
    pub fn clear(&mut self) {
        self.drain();
    }
}

/// Hole represents a hole in a slice i.e., an index without valid value
/// (because it was moved from or duplicated).
/// In drop, `Hole` will restore the slice by filling the hole
/// position with the value that was originally removed.
struct Hole<'a, T: 'a> {
    data: &'a mut [T],
    elt: ManuallyDrop<T>,
    pos: usize,
}

impl<'a, T> Hole<'a, T> {
    /// Create a new `Hole` at index `pos`.
    ///
    /// Unsafe because pos must be within the data slice.
    #[inline]
    unsafe fn new(data: &'a mut [T], pos: usize) -> Self {
        debug_assert!(pos < data.len());
        // SAFE: pos should be inside the slice
        let elt = unsafe { ptr::read(data.get_unchecked(pos)) };
        Hole { data, elt: ManuallyDrop::new(elt), pos }
    }

    #[inline]
    fn pos(&self) -> usize {
        self.pos
    }

    /// Returns a reference to the element removed.
    #[inline]
    fn element(&self) -> &T {
        &self.elt
    }

    /// Returns a reference to the element at `index`.
    ///
    /// Unsafe because index must be within the data slice and not equal to pos.
    #[inline]
    unsafe fn get(&self, index: usize) -> &T {
        debug_assert!(index != self.pos);
        debug_assert!(index < self.data.len());
        unsafe { self.data.get_unchecked(index) }
    }

    /// Move hole to new location
    ///
    /// Unsafe because index must be within the data slice and not equal to pos.
    #[inline]
    unsafe fn move_to(&mut self, index: usize) {
        debug_assert!(index != self.pos);
        debug_assert!(index < self.data.len());
        unsafe {
            let ptr = self.data.as_mut_ptr();
            let index_ptr: *const _ = ptr.add(index);
            let hole_ptr = ptr.add(self.pos);
            ptr::copy_nonoverlapping(index_ptr, hole_ptr, 1);
        }
        self.pos = index;
    }
}

impl<T> Drop for Hole<'_, T> {
    #[inline]
    fn drop(&mut self) {
        // fill the hole again
        unsafe {
            let pos = self.pos;
            ptr::copy_nonoverlapping(&*self.elt, self.data.get_unchecked_mut(pos), 1);
        }
    }
}

/// An iterator over the elements of a `BinaryHeap`.
///
/// This `struct` is created by [`BinaryHeap::iter()`]. See its
/// documentation for more.
///
/// [`iter`]: BinaryHeap::iter
#[must_use = "iterators are lazy and do nothing unless consumed"]
pub struct Iter<'a, T: 'a> {
    iter: slice::Iter<'a, T>,
}

impl<T: fmt::Debug> fmt::Debug for Iter<'_, T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_tuple("Iter").field(&self.iter.as_slice()).finish()
    }
}

// FIXME(#26925) Remove in favor of `#[derive(Clone)]`
impl<T> Clone for Iter<'_, T> {
    fn clone(&self) -> Self {
        Iter { iter: self.iter.clone() }
    }
}

impl<'a, T> Iterator for Iter<'a, T> {
    type Item = &'a T;

    #[inline]
    fn next(&mut self) -> Option<&'a T> {
        self.iter.next()
    }

    #[inline]
    fn size_hint(&self) -> (usize, Option<usize>) {
        self.iter.size_hint()
    }

    #[inline]
    fn last(self) -> Option<&'a T> {
        self.iter.last()
    }
}

impl<'a, T> DoubleEndedIterator for Iter<'a, T> {
    #[inline]
    fn next_back(&mut self) -> Option<&'a T> {
        self.iter.next_back()
    }
}

impl<T> ExactSizeIterator for Iter<'_, T> {
    #[cfg(feature = "exact_size_is_empty")]
    fn is_empty(&self) -> bool {
        self.iter.is_empty()
    }
}

impl<T> FusedIterator for Iter<'_, T> {}

cfg_if! {
    if #[cfg(not(feature = "inplace_iteration"))] {
        /// An owning iterator over the elements of a `BinaryHeap`.
        ///
        /// This `struct` is created by [`BinaryHeap::into_iter()`]
        /// (provided by the [`IntoIterator`] trait). See its documentation for more.
        ///
        /// [`into_iter`]: BinaryHeap::into_iter
        /// [`IntoIterator`]: core::iter::IntoIterator
        #[derive(Clone)]
        pub struct IntoIter<T> {
            iter: vec::IntoIter<T>,
        }

        impl<T: fmt::Debug> fmt::Debug for IntoIter<T> {
            fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
                f.debug_tuple("IntoIter").field(&self.iter.as_slice()).finish()
            }
        }

        impl<T> Iterator for IntoIter<T> {
            type Item = T;

            #[inline]
            fn next(&mut self) -> Option<T> {
                self.iter.next()
            }

            #[inline]
            fn size_hint(&self) -> (usize, Option<usize>) {
                self.iter.size_hint()
            }
        }

        impl<T> DoubleEndedIterator for IntoIter<T> {
            #[inline]
            fn next_back(&mut self) -> Option<T> {
                self.iter.next_back()
            }
        }

        impl<T> ExactSizeIterator for IntoIter<T> {
            #[cfg(feature = "exact_size_is_empty")]
            fn is_empty(&self) -> bool {
                self.iter.is_empty()
            }
        }

        impl<T> FusedIterator for IntoIter<T> {}

        // In addition to the SAFETY invariants of the following three unsafe traits
        // also refer to the vec::in_place_collect module documentation to get an overview
        #[cfg(feature = "inplace_iteration")]
        #[doc(hidden)]
        unsafe impl<T> SourceIter for IntoIter<T> {
            type Source = IntoIter<T>;

            #[inline]
            unsafe fn as_inner(&mut self) -> &mut Self::Source {
                self
            }
        }

        #[cfg(feature = "inplace_iteration")]
        #[doc(hidden)]
        unsafe impl<I> InPlaceIterable for IntoIter<I> {}
    } else {
        pub use vec::IntoIter;
    }
}
#[must_use = "iterators are lazy and do nothing unless consumed"]
#[cfg(feature = "binary_heap_into_iter_sorted")]
#[derive(Clone, Debug)]
pub struct IntoIterSorted<T, C = NoContext> {
    inner: BinaryHeap<T, C>,
}

#[cfg(feature = "binary_heap_into_iter_sorted")]
impl<T: ContextualOrd<C>, C> Iterator for IntoIterSorted<T, C> {
    type Item = T;

    #[inline]
    fn next(&mut self) -> Option<T> {
        self.inner.pop()
    }

    #[inline]
    fn size_hint(&self) -> (usize, Option<usize>) {
        let exact = self.inner.len();
        (exact, Some(exact))
    }
}

#[cfg(feature = "binary_heap_into_iter_sorted")]
impl<T: ContextualOrd<C>, C> ExactSizeIterator for IntoIterSorted<T, C> {}

#[cfg(feature = "binary_heap_into_iter_sorted")]
impl<T: ContextualOrd<C>, C> FusedIterator for IntoIterSorted<T, C> {}

#[cfg(all(feature = "binary_heap_into_iter_sorted", feature = "trusted_len"))]
unsafe impl<T: ContextualOrd<C>, C> TrustedLen for IntoIterSorted<T, C> {}

/// A draining iterator over the elements of a `BinaryHeap`.
///
/// This `struct` is created by [`BinaryHeap::drain()`]. See its
/// documentation for more.
///
/// [`drain`]: BinaryHeap::drain
#[derive(Debug)]
pub struct Drain<'a, T: 'a> {
    iter: vec::Drain<'a, T>,
}

impl<T> Iterator for Drain<'_, T> {
    type Item = T;

    #[inline]
    fn next(&mut self) -> Option<T> {
        self.iter.next()
    }

    #[inline]
    fn size_hint(&self) -> (usize, Option<usize>) {
        self.iter.size_hint()
    }
}

impl<T> DoubleEndedIterator for Drain<'_, T> {
    #[inline]
    fn next_back(&mut self) -> Option<T> {
        self.iter.next_back()
    }
}

impl<T> ExactSizeIterator for Drain<'_, T> {
    #[cfg(feature = "exact_size_is_empty")]
    fn is_empty(&self) -> bool {
        self.iter.is_empty()
    }
}

impl<T> FusedIterator for Drain<'_, T> {}

/// A draining iterator over the elements of a `BinaryHeap`.
///
/// This `struct` is created by [`BinaryHeap::drain_sorted()`]. See its
/// documentation for more.
///
/// [`drain_sorted`]: BinaryHeap::drain_sorted
#[cfg(feature = "binary_heap_drain_sorted")]
#[derive(Debug)]
pub struct DrainSorted<'a, T: ContextualOrd<C>, C = NoContext> {
    inner: &'a mut BinaryHeap<T, C>,
}

#[cfg(feature = "binary_heap_drain_sorted")]
impl<'a, T: ContextualOrd<C>, C> Drop for DrainSorted<'a, T, C> {
    /// Removes heap elements in heap order.
    fn drop(&mut self) {
        struct DropGuard<'r, 'a, T: ContextualOrd<C>, C = NoContext>(&'r mut DrainSorted<'a, T, C>);

        impl<'r, 'a, T: ContextualOrd<C>, C> Drop for DropGuard<'r, 'a, T, C> {
            fn drop(&mut self) {
                while self.0.inner.pop().is_some() {}
            }
        }

        while let Some(item) = self.inner.pop() {
            let guard = DropGuard(self);
            drop(item);
            mem::forget(guard);
        }
    }
}

#[cfg(feature = "binary_heap_drain_sorted")]
impl<T: ContextualOrd<C>, C> Iterator for DrainSorted<'_, T, C> {
    type Item = T;

    #[inline]
    fn next(&mut self) -> Option<T> {
        self.inner.pop()
    }

    #[inline]
    fn size_hint(&self) -> (usize, Option<usize>) {
        let exact = self.inner.len();
        (exact, Some(exact))
    }
}

#[cfg(feature = "binary_heap_drain_sorted")]
impl<T: ContextualOrd<C>, C> ExactSizeIterator for DrainSorted<'_, T, C> {}

#[cfg(feature = "binary_heap_drain_sorted")]
impl<T: ContextualOrd<C>, C> FusedIterator for DrainSorted<'_, T, C> {}

#[cfg(all(feature = "binary_heap_drain_sorted", feature = "trusted_len"))]
unsafe impl<T: ContextualOrd<C>, C> TrustedLen for DrainSorted<'_, T, C> {}

impl<T: ContextualOrd<C>, C: Default> From<Vec<T>> for BinaryHeap<T, C> {
    /// Converts a `Vec<T>` into a `BinaryHeap<T>`.
    ///
    /// This conversion happens in-place, and has *C*(*n*) time complexity.
    fn from(vec: Vec<T>) -> BinaryHeap<T, C> {
        let mut heap = BinaryHeap { data: vec, context: C::default() };
        heap.rebuild();
        heap
    }
}

impl<T: ContextualOrd<C>, C: Default, const N: usize> From<[T; N]> for BinaryHeap<T, C> {
    /// ```
    /// use contextual_alloc::collections::BinaryHeap;
    ///
    /// let mut h1 = BinaryHeap::from([1, 4, 2, 3]);
    /// let mut h2: BinaryHeap<_> = [1, 4, 2, 3].into();
    /// while let Some((a, b)) = h1.pop().zip(h2.pop()) {
    ///     assert_eq!(a, b);
    /// }
    /// ```
    fn from(arr: [T; N]) -> Self {
        Self::from_iter(arr)
    }
}

impl<T, C> From<BinaryHeap<T, C>> for Vec<T> {
    /// Converts a `BinaryHeap<T>` into a `Vec<T>`.
    ///
    /// This conversion requires no data movement or allocation, and has
    /// constant time complexity.
    fn from(heap: BinaryHeap<T, C>) -> Vec<T> {
        heap.data
    }
}

impl<T: ContextualOrd<C>, C: Default> FromIterator<T> for BinaryHeap<T, C> {
    fn from_iter<I: IntoIterator<Item = T>>(iter: I) -> BinaryHeap<T, C> {
        BinaryHeap::from(iter.into_iter().collect::<Vec<_>>())
    }
}

impl<T, C> IntoIterator for BinaryHeap<T, C> {
    type Item = T;
    type IntoIter = IntoIter<T>;

    /// Creates a consuming iterator, that is, one that moves each value out of
    /// the binary heap in arbitrary order. The binary heap cannot be used
    /// after calling this.
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```
    /// use contextual_alloc::collections::BinaryHeap;
    /// let heap = BinaryHeap::from([1, 2, 3, 4]);
    ///
    /// // Print 1, 2, 3, 4 in arbitrary order
    /// for x in heap.into_iter() {
    ///     // x has type i32, not &i32
    ///     println!("{x}");
    /// }
    /// ```
    fn into_iter(self) -> IntoIter<T> {
        let iter = self.data.into_iter();
        cfg_if! {
            if #[cfg(not(feature = "inplace_iteration"))] {
                IntoIter { iter }
            } else {
                #[allow(clippy::let_and_return)]
                iter
            }
        }
    }
}

impl<'a, T, C> IntoIterator for &'a BinaryHeap<T, C> {
    type Item = &'a T;
    type IntoIter = Iter<'a, T>;

    fn into_iter(self) -> Iter<'a, T> {
        self.iter()
    }
}

impl<T: ContextualOrd<C>, C> Extend<T> for BinaryHeap<T, C> {
    #[inline]
    fn extend<I: IntoIterator<Item = T>>(&mut self, iter: I) {
        <Self as SpecExtend<I>>::spec_extend(self, iter);
    }

    #[inline]
    #[cfg(feature = "extend_one")]
    fn extend_one(&mut self, item: T) {
        self.push(item);
    }

    #[inline]
    #[cfg(feature = "extend_one")]
    fn extend_reserve(&mut self, additional: usize) {
        self.reserve(additional);
    }
}

cfg_if! {
    if #[cfg(feature = "specialization")] {
        impl<T: ContextualOrd<C>, C, I: IntoIterator<Item = T>> SpecExtend<I> for BinaryHeap<T, C> {
            default fn spec_extend(&mut self, iter: I) {
                self.extend_desugared(iter.into_iter());
            }
        }

        impl<T: ContextualOrd<C>, C> SpecExtend<Vec<T>> for BinaryHeap<T, C> {
            fn spec_extend(&mut self, ref mut other: Vec<T>) {
                let start = self.data.len();
                self.data.append(other);
                self.rebuild_tail(start);
            }
        }

        impl<T: ContextualOrd<C>, C> SpecExtend<BinaryHeap<T, C>> for BinaryHeap<T, C> {
            fn spec_extend(&mut self, ref mut other: BinaryHeap<T, C>) {
                self.append(other);
            }
        }
    } else {
        impl<T: ContextualOrd<C>, C, I: IntoIterator<Item = T>> SpecExtend<I> for BinaryHeap<T, C> {
            fn spec_extend(&mut self, iter: I) {
                self.extend_desugared(iter.into_iter());
            }
        }
    }
}

impl<T: ContextualOrd<C>, C> BinaryHeap<T, C> {
    fn extend_desugared<I: IntoIterator<Item = T>>(&mut self, iter: I) {
        let iterator = iter.into_iter();
        let (lower, _) = iterator.size_hint();

        self.reserve(lower);

        iterator.for_each(move |elem| self.push(elem));
    }
}

impl<'a, T: 'a + ContextualOrd<C> + Copy, C> Extend<&'a T> for BinaryHeap<T, C> {
    fn extend<I: IntoIterator<Item = &'a T>>(&mut self, iter: I) {
        self.extend(iter.into_iter().cloned());
    }

    #[inline]
    #[cfg(feature = "extend_one")]
    fn extend_one(&mut self, &item: &'a T) {
        self.push(item);
    }

    #[inline]
    #[cfg(feature = "extend_one")]
    fn extend_reserve(&mut self, additional: usize) {
        self.reserve(additional);
    }
}
