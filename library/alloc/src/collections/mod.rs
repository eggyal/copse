#[cfg(not(no_global_oom_handling))]
pub mod binary_heap;
#[cfg(not(no_global_oom_handling))]
mod btree;

#[cfg(not(no_global_oom_handling))]
pub mod btree_map {
    //! An ordered map based on a B-Tree.
    pub use super::btree::map::*;
}

#[cfg(not(no_global_oom_handling))]
pub mod btree_set {
    //! An ordered set based on a B-Tree.
    pub use super::btree::set::*;
}

#[cfg(not(no_global_oom_handling))]
#[doc(no_inline)]
pub use binary_heap::BinaryHeap;

#[cfg(not(no_global_oom_handling))]
#[doc(no_inline)]
pub use btree_map::BTreeMap;

#[cfg(not(no_global_oom_handling))]
#[doc(no_inline)]
pub use btree_set::BTreeSet;

cfg_if::cfg_if! {
    if #[cfg(feature = "try_reserve_kind")] {
        pub use alloc::collections::{TryReserveError, TryReserveErrorKind};
    } else {
        use alloc::alloc::{Layout, LayoutError};
        use core::fmt::Display;

        /// The error type for `try_reserve` methods.
        #[derive(Clone, PartialEq, Eq, Debug)]
        pub struct TryReserveError {
            kind: TryReserveErrorKind,
        }

        impl TryReserveError {
            /// Details about the allocation that caused the error
            #[inline]
            #[must_use]
            #[cfg_attr(docsrs, doc(cfg(feature = "try_reserve_kind")))]
            pub fn kind(&self) -> TryReserveErrorKind {
                self.kind.clone()
            }
        }

        /// Details of the allocation that caused a `TryReserveError`
        #[derive(Clone, PartialEq, Eq, Debug)]
        #[cfg_attr(docsrs, doc(cfg(feature = "try_reserve_kind")))]
        pub enum TryReserveErrorKind {
            /// Error due to the computed capacity exceeding the collection's maximum
            /// (usually `isize::MAX` bytes).
            CapacityOverflow,

            /// The memory allocator returned an error
            AllocError {
                /// The layout of allocation request that failed
                layout: Layout,

                #[doc(hidden)]
                #[cfg(feature = "container_error_extra")]
                non_exhaustive: (),
            },
        }

        #[cfg_attr(docsrs, doc(cfg(feature = "try_reserve_kind")))]
        impl From<TryReserveErrorKind> for TryReserveError {
            #[inline]
            fn from(kind: TryReserveErrorKind) -> Self {
                Self { kind }
            }
        }

        #[cfg_attr(docsrs, doc(cfg(feature = "try_reserve_kind")))]
        impl From<LayoutError> for TryReserveErrorKind {
            /// Always evaluates to [`TryReserveErrorKind::CapacityOverflow`].
            #[inline]
            fn from(_: LayoutError) -> Self {
                TryReserveErrorKind::CapacityOverflow
            }
        }

        impl Display for TryReserveError {
            fn fmt(
                &self,
                fmt: &mut core::fmt::Formatter<'_>,
            ) -> core::result::Result<(), core::fmt::Error> {
                fmt.write_str("memory allocation failed")?;
                let reason = match self.kind {
                    TryReserveErrorKind::CapacityOverflow => {
                        " because the computed capacity exceeded the collection's maximum"
                    }
                    TryReserveErrorKind::AllocError { .. } => {
                        " because the memory allocator returned an error"
                    }
                };
                fmt.write_str(reason)
            }
        }

        #[cfg(feature = "error_in_core")]
        impl core::error::Error for TryReserveError {}
    }
}

/// An intermediate trait for specialization of `Extend`.
#[doc(hidden)]
trait SpecExtend<I: IntoIterator> {
    /// Extends `self` with the contents of the given iterator.
    fn spec_extend(&mut self, iter: I);
}
