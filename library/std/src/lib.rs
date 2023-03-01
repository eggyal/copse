#![doc = include_str!("../README.md")]
#![cfg_attr(feature = "allow_internal_unstable", feature(allow_internal_unstable))]
#![cfg_attr(feature = "extend_one", feature(extend_one))]
#![cfg_attr(feature = "rustc_attrs", feature(rustc_attrs))]
// documentation controls
#![cfg_attr(docsrs, feature(doc_auto_cfg, doc_cfg, doc_cfg_hide))]
#![cfg_attr(docsrs, doc(cfg_hide(no_global_oom_handling)))]
#![deny(missing_docs)]
#![cfg_attr(
    test,
    allow(
        clippy::assign_op_pattern,
        clippy::no_effect,
        clippy::nonminimal_bool,
        clippy::redundant_closure
    )
)]

#[macro_use]
extern crate contextual_alloc as alloc_crate;

pub mod collections;
mod polyfill;

#[cfg(test)]
#[allow(dead_code)] // Not used in all configurations.
pub(crate) mod test_helpers {
    /// Test-only replacement for `rand::thread_rng()`, which is unusable for
    /// us, as we want to allow running stdlib tests on tier-3 targets which may
    /// not have `getrandom` support.
    ///
    /// Does a bit of a song and dance to ensure that the seed is different on
    /// each call (as some tests sadly rely on this), but doesn't try that hard.
    ///
    /// This is duplicated in the `core`, `alloc` test suites (as well as
    /// `std`'s integration tests), but figuring out a mechanism to share these
    /// seems far more painful than copy-pasting a 7 line function a couple
    /// times, given that even under a perma-unstable feature, I don't think we
    /// want to expose types from `rand` from `std`.
    #[track_caller]
    pub(crate) fn test_rng() -> rand_xorshift::XorShiftRng {
        use core::hash::{BuildHasher, Hash, Hasher};
        let mut hasher = crate::collections::hash_map::RandomState::new().build_hasher();
        core::panic::Location::caller().hash(&mut hasher);
        let hc64 = hasher.finish();
        let seed_vec = hc64.to_le_bytes().into_iter().chain(0u8..8).collect::<Vec<u8>>();
        let seed: [u8; 16] = seed_vec.as_slice().try_into().unwrap();
        rand::SeedableRng::from_seed(seed)
    }
}
