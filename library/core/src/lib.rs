#![doc = include_str!("../README.md")]
#![cfg_attr(not(any(doc, test)), no_std)]
#![cfg_attr(feature = "is_sorted", feature(is_sorted))]
#![cfg_attr(docsrs, feature(doc_auto_cfg, doc_cfg, doc_cfg_hide))]
#![deny(missing_docs)]

pub mod borrow;
pub mod cmp;
pub mod iter;
mod macros;

/// The recommended prelude for this crate.
pub mod prelude {
    pub use crate::{
        cmp::{ContextualEq, ContextualOrd, ContextualPartialEq, ContextualPartialOrd},
        contextual,
        iter::ContextualIterator as _,
        NoContext,
    };
}

mod polyfill;

use borrow::*;
use cmp::*;
use core::borrow::*;

/// A zero-sized context that makes `contextual_core`'s functions behave as per
/// the respective standard library function of which they are the analogue.
#[derive(Clone, Copy, Debug, Default, Eq, PartialEq)]
pub struct NoContext;

impl<Lhs, Rhs> ContextualPartialEq<NoContext, Rhs> for Lhs
where
    Lhs: ?Sized + PartialEq<Rhs>,
    Rhs: ?Sized,
{
    fn contextual_eq(&self, other: &Rhs, _: &NoContext) -> bool {
        self == other
    }
    fn contextual_ne(&self, other: &Rhs, _: &NoContext) -> bool {
        self != other
    }
}

impl<T> ContextualEq<NoContext> for T where T: ?Sized + Eq {}

impl<Lhs, Rhs> ContextualPartialOrd<NoContext, Rhs> for Lhs
where
    Lhs: ?Sized + PartialOrd<Rhs>,
    Rhs: ?Sized,
{
    fn contextual_partial_cmp(&self, other: &Rhs, _: &NoContext) -> Option<Ordering> {
        self.partial_cmp(other)
    }

    fn contextual_lt(&self, other: &Rhs, _: &NoContext) -> bool {
        self < other
    }

    fn contextual_le(&self, other: &Rhs, _: &NoContext) -> bool {
        self <= other
    }

    fn contextual_gt(&self, other: &Rhs, _: &NoContext) -> bool {
        self > other
    }

    fn contextual_ge(&self, other: &Rhs, _: &NoContext) -> bool {
        self >= other
    }
}

impl<T> ContextualOrd<NoContext> for T
where
    T: ?Sized + Ord,
{
    fn contextual_cmp(&self, other: &Self, _: &NoContext) -> Ordering {
        self.cmp(other)
    }

    fn contextual_max(self, other: Self, _: &NoContext) -> Self
    where
        Self: Sized,
    {
        self.max(other)
    }

    fn contextual_min(self, other: Self, _: &NoContext) -> Self
    where
        Self: Sized,
    {
        self.min(other)
    }

    fn contextual_clamp(self, min: Self, max: Self, _: &NoContext) -> Self
    where
        Self: Sized,
    {
        self.clamp(min, max)
    }
}

impl<Borrowed, T> ContextualBorrow<Borrowed> for T
where
    Borrowed: ?Sized,
    T: ?Sized + Borrow<Borrowed>,
{
    fn contextual_borrow(&self, _: &NoContext) -> &Borrowed {
        self.borrow()
    }
}

impl<Borrowed, T> ContextualBorrowMut<Borrowed> for T
where
    Borrowed: ?Sized,
    T: ?Sized + BorrowMut<Borrowed>,
{
    fn contextual_borrow_mut(&mut self, _: &NoContext) -> &mut Borrowed {
        self.borrow_mut()
    }
}
