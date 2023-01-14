#![cfg_attr(not(any(feature = "std", test)), no_std)]
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
#![cfg_attr(feature = "maybe_uninit_slice", feature(maybe_uninit_slice))]
#![cfg_attr(feature = "new_uninit", feature(new_uninit))]
#![cfg_attr(feature = "rustc_attrs", feature(rustc_attrs))]
#![cfg_attr(feature = "slice_ptr_get", feature(slice_ptr_get))]
#![cfg_attr(feature = "specialization", feature(specialization))]
#![cfg_attr(feature = "trusted_len", feature(trusted_len))]
// documentation controls
#![cfg_attr(docsrs, feature(doc_auto_cfg, doc_cfg))]
// linting controls
#![cfg_attr(feature = "specialization", allow(incomplete_features))]

#[macro_use]
extern crate alloc;

#[macro_use]
mod polyfill;

// port of stdlib implementation
mod liballoc;
pub use liballoc::collections::{binary_heap, btree_map, btree_set};

#[cfg(not(no_global_oom_handling))]
#[doc(no_inline)]
pub use binary_heap::BinaryHeap;

#[cfg(not(no_global_oom_handling))]
#[doc(no_inline)]
pub use btree_map::BTreeMap;

#[cfg(not(no_global_oom_handling))]
#[doc(no_inline)]
pub use btree_set::BTreeSet;
