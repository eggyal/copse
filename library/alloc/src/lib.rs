#![doc = include_str!("../README.md")]
#![cfg_attr(not(test), no_std)]
#![cfg_attr(feature = "allocator_api", feature(allocator_api))]
#![cfg_attr(feature = "core_intrinsics", feature(core_intrinsics))]
#![cfg_attr(feature = "dropck_eyepatch", feature(dropck_eyepatch))]
#![cfg_attr(feature = "error_in_core", feature(error_in_core))]
#![cfg_attr(feature = "exact_size_is_empty", feature(exact_size_is_empty))]
#![cfg_attr(feature = "exclusive_range_pattern", feature(exclusive_range_pattern))]
#![cfg_attr(feature = "extend_one", feature(extend_one))]
#![cfg_attr(feature = "hasher_prefixfree_extras", feature(hasher_prefixfree_extras))]
#![cfg_attr(feature = "inline_const", feature(inline_const))]
#![cfg_attr(feature = "inplace_iteration", feature(inplace_iteration))]
#![cfg_attr(feature = "is_sorted", feature(is_sorted))]
#![cfg_attr(feature = "maybe_uninit_slice", feature(maybe_uninit_slice))]
#![cfg_attr(feature = "new_uninit", feature(new_uninit))]
#![cfg_attr(feature = "rustc_attrs", feature(rustc_attrs))]
#![cfg_attr(feature = "slice_ptr_get", feature(slice_ptr_get))]
#![cfg_attr(feature = "specialization", feature(specialization))]
#![cfg_attr(feature = "trusted_len", feature(trusted_len))]
// documentation controls
#![cfg_attr(docsrs, feature(doc_auto_cfg, doc_cfg, doc_cfg_hide))]
#![cfg_attr(docsrs, doc(cfg_hide(no_global_oom_handling)))]
#![deny(missing_docs)]
// linting controls
#![cfg_attr(feature = "specialization", allow(incomplete_features))]
#![allow(
    clippy::clone_on_copy,
    clippy::drop_non_drop,
    clippy::needless_borrow,
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

#[doc(hidden)]
pub use cfg_if;

#[macro_use]
extern crate alloc;
pub extern crate contextual_core;

#[macro_use]
mod polyfill;

pub mod collections;

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
