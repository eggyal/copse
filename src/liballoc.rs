#![allow(
    clippy::clone_on_copy,
    clippy::drop_non_drop,
    clippy::needless_borrow,
    clippy::needless_lifetimes,
    clippy::toplevel_ref_arg,
    clippy::type_complexity,
    clippy::unnecessary_mut_passed,
    missing_docs,
    unstable_name_collisions,
    unused_attributes,
    unused_imports
)]
#![cfg_attr(
    test,
    allow(
        clippy::bool_assert_comparison,
        clippy::bool_to_int_with_if,
        clippy::derive_ord_xor_partial_ord,
        clippy::explicit_counter_loop,
        clippy::ifs_same_cond,
        clippy::map_identity,
        clippy::needless_range_loop,
        clippy::redundant_clone,
        clippy::redundant_closure,
        clippy::single_char_add_str,
        clippy::uninlined_format_args,
        clippy::useless_vec,
    )
)]

pub mod collections {
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

    /// An intermediate trait for specialization of `Extend`.
    #[doc(hidden)]
    trait SpecExtend<I: IntoIterator> {
        /// Extends `self` with the contents of the given iterator.
        fn spec_extend(&mut self, iter: I);
    }
}

#[cfg(test)]
mod testing;

#[cfg(test)]
#[allow(dead_code)] // Not used in all configurations
pub(crate) mod test_helpers {
    /// Copied from `std::test_helpers::test_rng`, since these tests rely on the
    /// seed not being the same for every RNG invocation too.
    pub(crate) fn test_rng() -> rand_xorshift::XorShiftRng {
        use std::hash::{BuildHasher, Hash, Hasher};
        let mut hasher = std::collections::hash_map::RandomState::new().build_hasher();
        std::panic::Location::caller().hash(&mut hasher);
        let hc64 = hasher.finish();
        let seed_vec =
            hc64.to_le_bytes().into_iter().chain(0u8..8).collect::<alloc::vec::Vec<u8>>();
        let seed: [u8; 16] = seed_vec.as_slice().try_into().unwrap();
        rand::SeedableRng::from_seed(seed)
    }
}
