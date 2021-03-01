use core::borrow::Borrow;
use core::ops::RangeBounds;
use core::ptr;

use super::node::{marker, ForceResult::*, Handle, NodeRef};

pub struct LeafRange<BorrowType, K, V> {
    pub front: Option<Handle<NodeRef<BorrowType, K, V, marker::Leaf>, marker::Edge>>,
    pub back: Option<Handle<NodeRef<BorrowType, K, V, marker::Leaf>, marker::Edge>>,
}

impl<BorrowType, K, V> LeafRange<BorrowType, K, V> {
    pub fn none() -> Self {
        LeafRange { front: None, back: None }
    }

    pub fn is_empty(&self) -> bool {
        self.front == self.back
    }

    /// Temporarily takes out another, immutable equivalent of the same range.
    pub fn reborrow(&self) -> LeafRange<marker::Immut<'_>, K, V> {
        LeafRange {
            front: self.front.as_ref().map(|f| f.reborrow()),
            back: self.back.as_ref().map(|b| b.reborrow()),
        }
    }
}

impl<BorrowType: marker::BorrowType, K, V> NodeRef<BorrowType, K, V, marker::LeafOrInternal> {
    /// Finds the distinct leaf edges delimiting a specified range in a tree.
    /// Returns either a pair of different handles into the same tree or a pair
    /// of empty options.
    /// # Safety
    /// Unless `BorrowType` is `Immut`, do not use the duplicate handles to
    /// visit the same KV twice.
    unsafe fn find_leaf_edges_spanning_range<Q: ?Sized, R>(
        self,
        range: R,
    ) -> LeafRange<BorrowType, K, V>
    where
        Q: Ord,
        K: Borrow<Q>,
        R: RangeBounds<Q>,
    {
        match self.search_tree_for_bifurcation(&range) {
            Err(_) => LeafRange::none(),
            Ok((
                node,
                lower_edge_idx,
                upper_edge_idx,
                mut lower_child_bound,
                mut upper_child_bound,
            )) => {
                let mut lower_edge = unsafe { Handle::new_edge(ptr::read(&node), lower_edge_idx) };
                let mut upper_edge = unsafe { Handle::new_edge(node, upper_edge_idx) };
                loop {
                    match (lower_edge.force(), upper_edge.force()) {
                        (Leaf(f), Leaf(b)) => return LeafRange { front: Some(f), back: Some(b) },
                        (Internal(f), Internal(b)) => {
                            (lower_edge, lower_child_bound) =
                                f.descend().find_lower_bound_edge(lower_child_bound);
                            (upper_edge, upper_child_bound) =
                                b.descend().find_upper_bound_edge(upper_child_bound);
                        }
                        _ => unreachable!("BTreeMap has different depths"),
                    }
                }
            }
        }
    }
}

/// Equivalent to `(root1.first_leaf_edge(), root2.last_leaf_edge())` but more efficient.
fn full_range<BorrowType: marker::BorrowType, K, V>(
    root1: NodeRef<BorrowType, K, V, marker::LeafOrInternal>,
    root2: NodeRef<BorrowType, K, V, marker::LeafOrInternal>,
) -> LeafRange<BorrowType, K, V> {
    let mut min_node = root1;
    let mut max_node = root2;
    loop {
        let front = min_node.first_edge();
        let back = max_node.last_edge();
        match (front.force(), back.force()) {
            (Leaf(f), Leaf(b)) => {
                return LeafRange { front: Some(f), back: Some(b) };
            }
            (Internal(min_int), Internal(max_int)) => {
                min_node = min_int.descend();
                max_node = max_int.descend();
            }
            _ => unreachable!("BTreeMap has different depths"),
        };
    }
}

impl<'a, K: 'a, V: 'a> NodeRef<marker::Immut<'a>, K, V, marker::LeafOrInternal> {
    /// Finds the pair of leaf edges delimiting a specific range in a tree.
    ///
    /// The result is meaningful only if the tree is ordered by key, like the tree
    /// in a `BTreeMap` is.
    pub fn range_search<Q, R>(self, range: R) -> LeafRange<marker::Immut<'a>, K, V>
    where
        Q: ?Sized + Ord,
        K: Borrow<Q>,
        R: RangeBounds<Q>,
    {
        // SAFETY: our borrow type is immutable.
        unsafe { self.find_leaf_edges_spanning_range(range) }
    }

    /// Finds the pair of leaf edges delimiting an entire tree.
    pub fn full_range(self) -> LeafRange<marker::Immut<'a>, K, V> {
        full_range(self, self)
    }
}

impl<'a, K: 'a, V: 'a> NodeRef<marker::ValMut<'a>, K, V, marker::LeafOrInternal> {
    /// Splits a unique reference into a pair of leaf edges delimiting a specified range.
    /// The result are non-unique references allowing (some) mutation, which must be used
    /// carefully.
    ///
    /// The result is meaningful only if the tree is ordered by key, like the tree
    /// in a `BTreeMap` is.
    ///
    /// # Safety
    /// Do not use the duplicate handles to visit the same KV twice.
    pub fn range_search<Q, R>(self, range: R) -> LeafRange<marker::ValMut<'a>, K, V>
    where
        Q: ?Sized + Ord,
        K: Borrow<Q>,
        R: RangeBounds<Q>,
    {
        unsafe { self.find_leaf_edges_spanning_range(range) }
    }

    /// Splits a unique reference into a pair of leaf edges delimiting the full range of the tree.
    /// The results are non-unique references allowing mutation (of values only), so must be used
    /// with care.
    pub fn full_range(self) -> LeafRange<marker::ValMut<'a>, K, V> {
        // We duplicate the root NodeRef here -- we will never visit the same KV
        // twice, and never end up with overlapping value references.
        let self2 = unsafe { ptr::read(&self) };
        full_range(self, self2)
    }
}

impl<K, V> NodeRef<marker::Dying, K, V, marker::LeafOrInternal> {
    /// Splits a unique reference into a pair of leaf edges delimiting the full range of the tree.
    /// The results are non-unique references allowing massively destructive mutation, so must be
    /// used with the utmost care.
    pub fn full_range(self) -> LeafRange<marker::Dying, K, V> {
        // We duplicate the root NodeRef here -- we will never access it in a way
        // that overlaps references obtained from the root.
        let self2 = unsafe { ptr::read(&self) };
        full_range(self, self2)
    }
}

impl<BorrowType: marker::BorrowType, K, V>
    Handle<NodeRef<BorrowType, K, V, marker::Leaf>, marker::Edge>
{
    /// Given a leaf edge handle, returns [`Result::Ok`] with a handle to the neighboring KV
    /// on the right side, which is either in the same leaf node or in an ancestor node.
    /// If the leaf edge is the last one in the tree, returns [`Result::Err`] with the root node.
    pub fn next_kv(
        self,
    ) -> Result<
        Handle<NodeRef<BorrowType, K, V, marker::LeafOrInternal>, marker::KV>,
        NodeRef<BorrowType, K, V, marker::LeafOrInternal>,
    > {
        let mut edge = self.forget_node_type();
        loop {
            edge = match edge.right_kv() {
                Ok(kv) => return Ok(kv),
                Err(last_edge) => match last_edge.into_node().ascend() {
                    Ok(parent_edge) => parent_edge.forget_node_type(),
                    Err(root) => return Err(root),
                },
            }
        }
    }

    /// Given a leaf edge handle, returns [`Result::Ok`] with a handle to the neighboring KV
    /// on the left side, which is either in the same leaf node or in an ancestor node.
    /// If the leaf edge is the first one in the tree, returns [`Result::Err`] with the root node.
    pub fn next_back_kv(
        self,
    ) -> Result<
        Handle<NodeRef<BorrowType, K, V, marker::LeafOrInternal>, marker::KV>,
        NodeRef<BorrowType, K, V, marker::LeafOrInternal>,
    > {
        let mut edge = self.forget_node_type();
        loop {
            edge = match edge.left_kv() {
                Ok(kv) => return Ok(kv),
                Err(last_edge) => match last_edge.into_node().ascend() {
                    Ok(parent_edge) => parent_edge.forget_node_type(),
                    Err(root) => return Err(root),
                },
            }
        }
    }
}

impl<BorrowType: marker::BorrowType, K, V>
    Handle<NodeRef<BorrowType, K, V, marker::Internal>, marker::Edge>
{
    /// Given an internal edge handle, returns [`Result::Ok`] with a handle to the neighboring KV
    /// on the right side, which is either in the same internal node or in an ancestor node.
    /// If the internal edge is the last one in the tree, returns [`Result::Err`] with the root node.
    pub fn next_kv(
        self,
    ) -> Result<
        Handle<NodeRef<BorrowType, K, V, marker::Internal>, marker::KV>,
        NodeRef<BorrowType, K, V, marker::Internal>,
    > {
        let mut edge = self;
        loop {
            edge = match edge.right_kv() {
                Ok(internal_kv) => return Ok(internal_kv),
                Err(last_edge) => match last_edge.into_node().ascend() {
                    Ok(parent_edge) => parent_edge,
                    Err(root) => return Err(root),
                },
            }
        }
    }
}

impl<K, V> Handle<NodeRef<marker::Dying, K, V, marker::Leaf>, marker::Edge> {
    /// Given a leaf edge handle into a dying tree, returns the next leaf edge
    /// on the right side, and the key-value pair in between, which is either
    /// in the same leaf node, in an ancestor node, or non-existent.
    ///
    /// This method also deallocates any node(s) it reaches the end of. This
    /// implies that if no more key-value pair exists, the entire remainder of
    /// the tree will have been deallocated and there is nothing left to return.
    ///
    /// # Safety
    /// The given edge must not have been previously returned by counterpart
    /// `deallocating_next_back`.
    unsafe fn deallocating_next(self) -> Option<(Self, (K, V))> {
        let mut edge = self.forget_node_type();
        loop {
            edge = match edge.right_kv() {
                Ok(kv) => {
                    let k = unsafe { ptr::read(kv.reborrow().into_kv().0) };
                    let v = unsafe { ptr::read(kv.reborrow().into_kv().1) };
                    return Some((kv.next_leaf_edge(), (k, v)));
                }
                Err(last_edge) => match unsafe { last_edge.into_node().deallocate_and_ascend() } {
                    Some(parent_edge) => parent_edge.forget_node_type(),
                    None => return None,
                },
            }
        }
    }

    /// Given a leaf edge handle into a dying tree, returns the next leaf edge
    /// on the left side, and the key-value pair in between, which is either
    /// in the same leaf node, in an ancestor node, or non-existent.
    ///
    /// This method also deallocates any node(s) it reaches the end of. This
    /// implies that if no more key-value pair exists, the entire remainder of
    /// the tree will have been deallocated and there is nothing left to return.
    ///
    /// # Safety
    /// The given edge must not have been previously returned by counterpart
    /// `deallocating_next`.
    unsafe fn deallocating_next_back(self) -> Option<(Self, (K, V))> {
        let mut edge = self.forget_node_type();
        loop {
            edge = match edge.left_kv() {
                Ok(kv) => {
                    let k = unsafe { ptr::read(kv.reborrow().into_kv().0) };
                    let v = unsafe { ptr::read(kv.reborrow().into_kv().1) };
                    return Some((kv.next_back_leaf_edge(), (k, v)));
                }
                Err(last_edge) => match unsafe { last_edge.into_node().deallocate_and_ascend() } {
                    Some(parent_edge) => parent_edge.forget_node_type(),
                    None => return None,
                },
            }
        }
    }

    /// Deallocates a pile of nodes from the leaf up to the root.
    /// This is the only way to deallocate the remainder of a tree after
    /// `deallocating_next` and `deallocating_next_back` have been nibbling at
    /// both sides of the tree, and have hit the same edge. As it is intended
    /// only to be called when all keys and values have been returned,
    /// no cleanup is done on any of the keys or values.
    pub fn deallocating_end(self) {
        let mut edge = self.forget_node_type();
        while let Some(parent_edge) = unsafe { edge.into_node().deallocate_and_ascend() } {
            edge = parent_edge.forget_node_type();
        }
    }
}

impl<'a, K, V> Handle<NodeRef<marker::Immut<'a>, K, V, marker::Leaf>, marker::Edge> {
    /// Moves the leaf edge handle to the next leaf edge and returns references to the
    /// key and value in between.
    ///
    /// # Safety
    /// There must be another KV in the direction travelled.
    pub unsafe fn next_unchecked(&mut self) -> (&'a K, &'a V) {
        super::mem::replace(self, |leaf_edge| {
            let kv = leaf_edge.next_kv();
            let kv = unsafe { kv.ok().unwrap_unchecked() };
            (kv.next_leaf_edge(), kv.into_kv())
        })
    }

    /// Moves the leaf edge handle to the previous leaf edge and returns references to the
    /// key and value in between.
    ///
    /// # Safety
    /// There must be another KV in the direction travelled.
    pub unsafe fn next_back_unchecked(&mut self) -> (&'a K, &'a V) {
        super::mem::replace(self, |leaf_edge| {
            let kv = leaf_edge.next_back_kv();
            let kv = unsafe { kv.ok().unwrap_unchecked() };
            (kv.next_back_leaf_edge(), kv.into_kv())
        })
    }
}

impl<'a, K, V> Handle<NodeRef<marker::ValMut<'a>, K, V, marker::Leaf>, marker::Edge> {
    /// Moves the leaf edge handle to the next leaf edge and returns references to the
    /// key and value in between.
    ///
    /// # Safety
    /// There must be another KV in the direction travelled.
    pub unsafe fn next_unchecked(&mut self) -> (&'a K, &'a mut V) {
        let kv = super::mem::replace(self, |leaf_edge| {
            let kv = leaf_edge.next_kv();
            let kv = unsafe { kv.ok().unwrap_unchecked() };
            (unsafe { ptr::read(&kv) }.next_leaf_edge(), kv)
        });
        // Doing this last is faster, according to benchmarks.
        kv.into_kv_valmut()
    }

    /// Moves the leaf edge handle to the previous leaf and returns references to the
    /// key and value in between.
    ///
    /// # Safety
    /// There must be another KV in the direction travelled.
    pub unsafe fn next_back_unchecked(&mut self) -> (&'a K, &'a mut V) {
        let kv = super::mem::replace(self, |leaf_edge| {
            let kv = leaf_edge.next_back_kv();
            let kv = unsafe { kv.ok().unwrap_unchecked() };
            (unsafe { ptr::read(&kv) }.next_back_leaf_edge(), kv)
        });
        // Doing this last is faster, according to benchmarks.
        kv.into_kv_valmut()
    }
}

impl<K, V> Handle<NodeRef<marker::Dying, K, V, marker::Leaf>, marker::Edge> {
    /// Moves the leaf edge handle to the next leaf edge and returns the key and value
    /// in between, deallocating any node left behind while leaving the corresponding
    /// edge in its parent node dangling.
    ///
    /// # Safety
    /// - There must be another KV in the direction travelled.
    /// - That KV was not previously returned by counterpart `next_back_unchecked`
    ///   on any copy of the handles being used to traverse the tree.
    ///
    /// The only safe way to proceed with the updated handle is to compare it, drop it,
    /// call this method again subject to its safety conditions, or call counterpart
    /// `next_back_unchecked` subject to its safety conditions.
    pub unsafe fn deallocating_next_unchecked(&mut self) -> (K, V) {
        super::mem::replace(self, |leaf_edge| unsafe {
            leaf_edge.deallocating_next().unwrap_unchecked()
        })
    }

    /// Moves the leaf edge handle to the previous leaf edge and returns the key and value
    /// in between, deallocating any node left behind while leaving the corresponding
    /// edge in its parent node dangling.
    ///
    /// # Safety
    /// - There must be another KV in the direction travelled.
    /// - That leaf edge was not previously returned by counterpart `next_unchecked`
    ///   on any copy of the handles being used to traverse the tree.
    ///
    /// The only safe way to proceed with the updated handle is to compare it, drop it,
    /// call this method again subject to its safety conditions, or call counterpart
    /// `next_unchecked` subject to its safety conditions.
    pub unsafe fn deallocating_next_back_unchecked(&mut self) -> (K, V) {
        super::mem::replace(self, |leaf_edge| unsafe {
            leaf_edge.deallocating_next_back().unwrap_unchecked()
        })
    }
}

impl<BorrowType: marker::BorrowType, K, V> NodeRef<BorrowType, K, V, marker::LeafOrInternal> {
    /// Returns the leftmost leaf edge in or underneath a node - in other words, the edge
    /// you need first when navigating forward (or last when navigating backward).
    #[inline]
    pub fn first_leaf_edge(self) -> Handle<NodeRef<BorrowType, K, V, marker::Leaf>, marker::Edge> {
        let mut node = self;
        loop {
            match node.force() {
                Leaf(leaf) => return leaf.first_edge(),
                Internal(internal) => node = internal.first_edge().descend(),
            }
        }
    }

    /// Returns the rightmost leaf edge in or underneath a node - in other words, the edge
    /// you need last when navigating forward (or first when navigating backward).
    #[inline]
    pub fn last_leaf_edge(self) -> Handle<NodeRef<BorrowType, K, V, marker::Leaf>, marker::Edge> {
        let mut node = self;
        loop {
            match node.force() {
                Leaf(leaf) => return leaf.last_edge(),
                Internal(internal) => node = internal.last_edge().descend(),
            }
        }
    }
}

pub enum Position<BorrowType, K, V> {
    Leaf(NodeRef<BorrowType, K, V, marker::Leaf>),
    Internal(NodeRef<BorrowType, K, V, marker::Internal>),
    InternalKV(Handle<NodeRef<BorrowType, K, V, marker::Internal>, marker::KV>),
}

impl<'a, K: 'a, V: 'a> NodeRef<marker::Immut<'a>, K, V, marker::LeafOrInternal> {
    /// Visits leaf nodes and internal KVs in order of ascending keys, and also
    /// visits internal nodes as a whole in a depth first order, meaning that
    /// internal nodes precede their individual KVs and their child nodes.
    pub fn visit_nodes_in_order<F>(self, mut visit: F)
    where
        F: FnMut(Position<marker::Immut<'a>, K, V>),
    {
        match self.force() {
            Leaf(leaf) => visit(Position::Leaf(leaf)),
            Internal(internal) => {
                visit(Position::Internal(internal));
                let mut edge = internal.first_edge();
                loop {
                    edge = match edge.descend().force() {
                        Leaf(leaf) => {
                            visit(Position::Leaf(leaf));
                            match edge.next_kv() {
                                Ok(kv) => {
                                    visit(Position::InternalKV(kv));
                                    kv.right_edge()
                                }
                                Err(_) => return,
                            }
                        }
                        Internal(internal) => {
                            visit(Position::Internal(internal));
                            internal.first_edge()
                        }
                    }
                }
            }
        }
    }

    /// Calculates the number of elements in a (sub)tree.
    pub fn calc_length(self) -> usize {
        let mut result = 0;
        self.visit_nodes_in_order(|pos| match pos {
            Position::Leaf(node) => result += node.len(),
            Position::Internal(node) => result += node.len(),
            Position::InternalKV(_) => (),
        });
        result
    }
}

impl<BorrowType: marker::BorrowType, K, V>
    Handle<NodeRef<BorrowType, K, V, marker::LeafOrInternal>, marker::KV>
{
    /// Returns the leaf edge closest to a KV for forward navigation.
    pub fn next_leaf_edge(self) -> Handle<NodeRef<BorrowType, K, V, marker::Leaf>, marker::Edge> {
        match self.force() {
            Leaf(leaf_kv) => leaf_kv.right_edge(),
            Internal(internal_kv) => {
                let next_internal_edge = internal_kv.right_edge();
                next_internal_edge.descend().first_leaf_edge()
            }
        }
    }

    /// Returns the leaf edge closest to a KV for backward navigation.
    pub fn next_back_leaf_edge(
        self,
    ) -> Handle<NodeRef<BorrowType, K, V, marker::Leaf>, marker::Edge> {
        match self.force() {
            Leaf(leaf_kv) => leaf_kv.left_edge(),
            Internal(internal_kv) => {
                let next_internal_edge = internal_kv.left_edge();
                next_internal_edge.descend().last_leaf_edge()
            }
        }
    }
}
